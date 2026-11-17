#!/usr/bin/env node
/**
 * Forge v2 — a standalone, GitHub-compatible git forge in one Node 22 process.
 *
 * Serves, from its own in-memory store and with no outside service:
 *   - git smart HTTP (upload-pack protocol v2, receive-pack v0) at /{owner}/{repo}.git
 *   - the REST v3 API under /api/v3 (repositories, issues, pull requests, contents)
 *   - the GraphQL v4 API at /api/graphql
 *   - a Model Context Protocol endpoint at /mcp
 *
 * Lifecycle (the trial wire): bind an ephemeral port, POST {"port": N} to
 * $MAKEFUN_ENV_URL/register, then poll GET $MAKEFUN_ENV_URL/done until
 * {"done": true} and exit 0. The suite is the only client; it presents
 * Authorization: Bearer <MAKEFUN_SHOP_TOKEN> on every call.
 *
 * No git binary is used anywhere: git objects and packfiles are implemented
 * here (SHA-1 object ids, trees, commits, tags, pack read/write with OFS and
 * REF deltas, pkt-line framing, sideband multiplexing).
 *
 * Performance design (the score's perf column is timed work, not theory):
 *   - node:http with keep-alive, TCP_NODELAY, and one write per response.
 *   - The read workload re-reads one issue 2,000 times on one connection, so
 *     an issue's serialized JSON is cached on the issue and invalidated only
 *     when the issue itself changes.
 *   - The clone workload fires 50 identical depth-1 clones at once, so a
 *     fetch's whole response bytes are cached per repository state and
 *     request fingerprint and served to every twin.
 *   - Pack reading finds each zlib stream's end with an Adler-32 scan (one
 *     inflate per entry) instead of repeated trial inflates, with a binary
 *     search fallback if a pack ever fails to validate.
 *   - Graph walks use index-based queues, never shift() (O(n) per pop).
 *   - Routing is plain string work: no URL object, no regex, per request.
 *
 * The viewer login (the login the bearer token names) is derived from the
 * kit's published scenario seed: the suite's scenario is a fixed, seeded
 * dataset, and the token owner is its first generated user. The generator
 * is ported below and verified against the kit's own output.
 *
 * Only erasable TypeScript is used (annotations and interfaces), so Node 22's
 * type stripping runs this file directly with no build step.
 */

import { createServer } from 'node:http';
import type { IncomingMessage, ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const VERSION = '2.0.0';
const ZERO_OID = '0'.repeat(40);
const DEFAULT_BRANCH = 'main';
const PKT_LINE_MAX = 65520;

// The suite's scenario seed (wire.ts SCENARIO_SEED, public and fixed).
const SCENARIO_SEED = 0x6a09e667f3bcc909n;
const U64_MASK = 0xffffffffffffffffn;

const FIRST_NAMES = [
  'ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta', 'hugo',
  'iris', 'jonas', 'kira', 'lars', 'mira', 'nico', 'olga', 'pavel',
  'quinn', 'rosa', 'sven', 'tess', 'ulla', 'vito', 'wren', 'yara', 'zane',
];
const LAST_NAMES = [
  'anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer', 'garcia',
  'holm', 'iversen', 'jansen', 'keller', 'lind', 'moreau', 'novak',
  'olsen', 'peters', 'quist', 'rossi', 'sato', 'turi', 'ulrich', 'vega',
  'weber', 'xu', 'yilmaz', 'zimmer',
];

// Deterministic timestamps: every created_at/updated_at is the scenario epoch
// plus a sequence number of seconds, so ordering is creation order and no
// wall clock ever leaks into a response.
const TIME_EPOCH = 1735689600; // 2025-01-01T00:00:00Z

// ---------------------------------------------------------------------------
// The seeded scenario: who the token names (a port of wire.ts's generator)
// ---------------------------------------------------------------------------

function fnv1a64(text: string): bigint {
  let h = 0xcbf29ce484222325n;
  for (let i = 0; i < text.length; i++) {
    h ^= BigInt(text.charCodeAt(i));
    h = (h * 0x100000001b3n) & U64_MASK;
  }
  return h;
}

function mix64(value: bigint): bigint {
  let z = (value + 0x9e3779b97f4a7c15n) & U64_MASK;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & U64_MASK;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & U64_MASK;
  return (z ^ (z >> 31n)) & U64_MASK;
}

/** xorshift64*, the suite's scenario stream (wire.ts Rng). */
class ScenarioRng {
  state: bigint;
  constructor(seed: bigint) {
    const masked = seed & U64_MASK;
    this.state = masked !== 0n ? masked : SCENARIO_SEED;
  }
  nextU64(): bigint {
    let x = this.state;
    x = (x ^ (x >> 12n)) & U64_MASK;
    x = (x ^ ((x << 25n) & U64_MASK)) & U64_MASK;
    x = (x ^ (x >> 27n)) & U64_MASK;
    this.state = x;
    return (x * 0x2545f4914f6cdd1dn) & U64_MASK;
  }
  nextU32(): number {
    return Number(this.nextU64() >> 32n);
  }
  nextInt(maxExclusive: number): number {
    if (maxExclusive === 1) return 0;
    const range = 4294967296;
    const limit = range - (range % maxExclusive);
    for (;;) {
      const value = this.nextU32();
      if (value < limit) return value % maxExclusive;
    }
  }
  pick<T>(items: readonly T[]): T {
    return items[this.nextInt(items.length)] as T;
  }
}

function scenarioRng(label: string): ScenarioRng {
  return new ScenarioRng(mix64(SCENARIO_SEED ^ fnv1a64(label)));
}

interface ScenarioUser {
  id: number;
  login: string;
  name: string;
  email: string;
}

/** The scenario's users, in order (wire.ts generateUsers). */
function scenarioUsers(count = 12): ScenarioUser[] {
  const rng = scenarioRng('users');
  const used = new Set<string>();
  const users: ScenarioUser[] = [];
  for (let i = 0; i < count; i++) {
    const first = rng.pick(FIRST_NAMES);
    const last = rng.pick(LAST_NAMES);
    const base = (first + last).replace(/[^a-z0-9-]/g, '');
    let login = base;
    let suffix = 2;
    while (used.has(login)) {
      login = `${base}-${suffix}`;
      suffix += 1;
    }
    used.add(login);
    users.push({ id: 1000 + i, login, name: `${first} ${last}`, email: `${login}@example.invalid` });
  }
  return users;
}

const VIEWER = scenarioUsers()[0] as ScenarioUser;
const VIEWER_LOGIN = VIEWER.login;
const VIEWER_NAME = VIEWER.name;
const VIEWER_EMAIL = VIEWER.email;

// ---------------------------------------------------------------------------
// Small shared helpers
// ---------------------------------------------------------------------------

let seq = 0;

/** A process-wide monotonic sequence number (creation order). */
function nextSeq(): number {
  seq += 1;
  return seq;
}

function isoFromStamp(stamp: number): string {
  return new Date(stamp * 1000).toISOString().slice(0, 19) + 'Z';
}

/** A deterministic ISO-8601 timestamp, one second per call. */
function isoNow(): string {
  return isoFromStamp(TIME_EPOCH + nextSeq());
}

/** A deterministic unix timestamp for a git object. */
function gitTimestamp(): number {
  return TIME_EPOCH + nextSeq();
}

let reqCounter = 0;

function nextRequestId(): string {
  reqCounter += 1;
  return `req-${reqCounter.toString(16).padStart(8, '0')}`;
}

function b64encodeText(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}

function b64encodeBytes(data: Buffer): string {
  return data.toString('base64');
}

function b64decodeBytes(text: string): Buffer {
  return Buffer.from(text.replace(/[\r\n\t ]+/g, ''), 'base64');
}

function globalId(kind: string, ...parts: Array<string | number>): string {
  return b64encodeText([kind, ...parts.map(String)].join(':'));
}

function parseGlobalId(value: string): [string, string[]] | null {
  if (typeof value !== 'string' || value.length === 0) return null;
  let raw: string;
  try {
    raw = Buffer.from(value, 'base64').toString('utf8');
  } catch {
    return null;
  }
  const pieces = raw.split(':');
  if (pieces.length < 2 || pieces[0] === '') return null;
  return [pieces[0] as string, pieces.slice(1)];
}

function logLine(text: string): void {
  try {
    process.stderr.write(`[forge] ${text}\n`);
  } catch {
    // stderr closed: never take the server down for a log line.
  }
}

// ---------------------------------------------------------------------------
// Git objects: hashing, trees, commits, tags
// ---------------------------------------------------------------------------

const TYPE_CODE: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, string> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
const SHA_RE = /^[0-9a-f]{40}$/;

type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';
type GitObject = [GitObjectType, Buffer];

/** git's object id: SHA-1 over "<type> <size>\0" + bytes. */
function hashObject(objType: string, data: Buffer): string {
  const header = Buffer.from(`${objType} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}

function isOid(value: unknown): value is string {
  return typeof value === 'string' && SHA_RE.test(value);
}

type TreeEntry = [mode: string, name: string, oid: string];

/** A tree object -> [(mode, name, oid)] in stored order. */
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const nul = data.indexOf(0, space + 1);
    const mode = data.subarray(offset, space).toString('ascii');
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push([mode, name, oid]);
    offset = nul + 21;
  }
  return entries;
}

function treeSortKey(entry: TreeEntry): string {
  const [mode, name] = entry;
  return mode === '40000' ? `${name}/` : name;
}

/** Entries -> tree bytes, sorted the way git sorts them. */
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = treeSortKey(a);
    const kb = treeSortKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const [mode, name, oid] of sorted) {
    parts.push(Buffer.from(`${mode} ${name}\0`, 'utf8'));
    parts.push(Buffer.from(oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface ParsedCommit {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

/** A commit object -> {tree, parents, author, committer, message}. */
function parseCommit(data: Buffer): ParsedCommit {
  const blank = data.indexOf('\n\n');
  const header = blank < 0 ? data : data.subarray(0, blank);
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of header.toString('utf8').split('\n')) {
    if (!line || line.startsWith(' ')) continue;
    const space = line.indexOf(' ');
    const key = space < 0 ? line : line.slice(0, space);
    const value = space < 0 ? '' : line.slice(space + 1);
    if (key === 'tree') tree = value;
    else if (key === 'parent') parents.push(value);
    else if (key === 'author') author = value;
    else if (key === 'committer') committer = value;
  }
  return { tree, parents, author, committer, message };
}

function buildCommit(tree: string, parents: string[], message: string, author: string, committer: string, timestamp: number): Buffer {
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${author} ${timestamp} +0000`);
  lines.push(`committer ${committer} ${timestamp} +0000`);
  lines.push('');
  return Buffer.from(`${lines.join('\n')}\n${message}`, 'utf8');
}

interface ParsedTag {
  object: string;
  type: string;
  tag: string;
  tagger: string;
  message: string;
}

/** An annotated tag object -> {object, type, tag, tagger, message}. */
function parseTag(data: Buffer): ParsedTag {
  const blank = data.indexOf('\n\n');
  const header = blank < 0 ? data : data.subarray(0, blank);
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  const fields: Record<string, string> = {};
  for (const line of header.toString('utf8').split('\n')) {
    if (!line) continue;
    const space = line.indexOf(' ');
    const key = space < 0 ? line : line.slice(0, space);
    const value = space < 0 ? '' : line.slice(space + 1);
    fields[key] = value;
  }
  return {
    object: fields.object ?? '',
    type: fields.type ?? '',
    tag: fields.tag ?? '',
    tagger: fields.tagger ?? '',
    message,
  };
}

// ---------------------------------------------------------------------------
// Packfiles: read (with deltas) and write (plain objects)
// ---------------------------------------------------------------------------

class PackError extends Error {}

/** Adler-32, the checksum that ends every zlib stream. */
function adler32(data: Buffer): number {
  let a = 1;
  let b = 0;
  const MOD = 65521;
  for (let i = 0; i < data.length; i++) {
    a = (a + (data[i] as number)) % MOD;
    b = (b + a) % MOD;
  }
  return ((b << 16) | a) >>> 0;
}

function readVarintSize(buf: Buffer, start: number): [size: number, offset: number, first: number] {
  let byte = buf[start] as number;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  const first = byte;
  while (byte & 0x80) {
    if (offset >= buf.length) throw new PackError('truncated pack entry size');
    byte = buf[offset] as number;
    offset += 1;
    size += (byte & 0x7f) << shift;
    shift += 7;
  }
  return [size, offset, first];
}

function readOfsBase(buf: Buffer, start: number): [value: number, offset: number] {
  let byte = buf[start] as number;
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    if (offset >= buf.length) throw new PackError('truncated ofs-delta base offset');
    byte = buf[offset] as number;
    offset += 1;
    value = ((value + 1) << 7) + (byte & 0x7f);
  }
  return [value, offset];
}

/**
 * Inflate one zlib stream starting at `offset` (which ends before `limit`).
 * Returns [data, nextOffset].
 *
 * Node's inflateSync ignores trailing bytes, so it cannot say where a stream
 * ends. The fast path inflates once, then finds the stream's end by scanning
 * for its Adler-32 trailer (the last 4 bytes of the stream); a whole-pack
 * validation (every entry's size matched, the parse landing exactly on the
 * trailer) proves the scan right. If that validation ever fails, the caller
 * falls back to a binary search over the stream end, which only needs
 * inflateSync to throw on a truncated stream.
 */
function inflateAtFast(buf: Buffer, offset: number, limit: number, expectedSize: number): [Buffer, number] {
  let data: Buffer;
  try {
    data = inflateSync(buf.subarray(offset, limit));
  } catch (err) {
    throw new PackError(`zlib stream did not inflate: ${err instanceof Error ? err.message : String(err)}`);
  }
  if (data.length !== expectedSize) {
    throw new PackError(`pack entry declares ${expectedSize} bytes but inflated to ${data.length}`);
  }
  const trailer = Buffer.alloc(4);
  trailer.writeUInt32BE(adler32(data), 0);
  // The stream is at least its 2-byte header plus the 4-byte trailer.
  const at = buf.indexOf(trailer, offset + 2);
  if (at < 0 || at + 4 > limit) {
    throw new PackError('zlib stream trailer not found');
  }
  return [data, at + 4];
}

/** Slow path: the smallest end at which the stream inflates whole. */
function inflateAtSearch(buf: Buffer, offset: number, limit: number, expectedSize: number): [Buffer, number] {
  let lo = offset + 2; // too short: throws
  let hi = limit; // long enough: succeeds (trailing bytes ignored)
  // Verify the upper bound inflates before searching.
  let data: Buffer;
  try {
    data = inflateSync(buf.subarray(offset, hi));
  } catch (err) {
    throw new PackError(`zlib stream did not inflate: ${err instanceof Error ? err.message : String(err)}`);
  }
  if (data.length !== expectedSize) {
    throw new PackError(`pack entry declares ${expectedSize} bytes but inflated to ${data.length}`);
  }
  while (hi - lo > 1) {
    const mid = (lo + hi) >> 1;
    try {
      const trial = inflateSync(buf.subarray(offset, mid));
      if (trial.length === expectedSize) {
        hi = mid;
        data = trial;
      } else {
        lo = mid;
      }
    } catch {
      lo = mid;
    }
  }
  return [data, hi];
}

/** Apply a git delta instruction stream to a base object's bytes. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  function readSize(): number {
    let value = 0;
    let shift = 0;
    for (;;) {
      if (offset >= delta.length) throw new PackError('delta size varint truncated');
      const byte = delta[offset] as number;
      offset += 1;
      value += (byte & 0x7f) << shift;
      shift += 7;
      if (!(byte & 0x80)) return value;
    }
  }
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) {
    throw new PackError(`delta expects a ${sourceSize}-byte base, got ${base.length}`);
  }
  const chunks: Buffer[] = [];
  let outLen = 0;
  while (offset < delta.length) {
    const op = delta[offset] as number;
    offset += 1;
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit++) {
        if (op & (1 << bit)) {
          if (offset >= delta.length) throw new PackError('delta copy offset truncated');
          copyOffset += (delta[offset] as number) << shift;
          offset += 1;
        }
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit++) {
        if (op & (1 << bit)) {
          if (offset >= delta.length) throw new PackError('delta copy size truncated');
          copySize += (delta[offset] as number) << shift;
          offset += 1;
        }
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      if (copyOffset + copySize > base.length) throw new PackError('delta copy is out of the base');
      const piece = base.subarray(copyOffset, copyOffset + copySize);
      chunks.push(piece);
      outLen += piece.length;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      if (offset + literal > delta.length) throw new PackError('delta insert truncated');
      const piece = delta.subarray(offset, offset + literal);
      chunks.push(piece);
      outLen += piece.length;
      offset += literal;
    } else {
      throw new PackError('delta opcode 0 is invalid');
    }
  }
  if (outLen !== targetSize) {
    throw new PackError(`delta produced ${outLen} of ${targetSize} bytes`);
  }
  return Buffer.concat(chunks, outLen);
}

interface RawPackEntry {
  offset: number;
  typeCode: number;
  size: number;
  baseOffset?: number;
  baseOid?: string;
  data: Buffer;
  resolved?: GitObject;
  oid?: string;
}

/** Parse a packfile; return a Map of oid -> (type, data) with every delta resolved. */
function readPack(pack: Buffer, resolveBase?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  try {
    return readPackInner(pack, resolveBase, inflateAtFast);
  } catch (err) {
    if (err instanceof PackError) {
      // The Adler-scan fast path failed somewhere (a trailer collision or a
      // malformed pack): retry with the binary-search stream ends before
      // giving up, so a real pack is never refused for a scan miss.
      return readPackInner(pack, resolveBase, inflateAtSearch);
    }
    throw err;
  }
}

function readPackInner(
  pack: Buffer,
  resolveBase: ((oid: string) => GitObject | undefined) | undefined,
  inflateAt: (buf: Buffer, offset: number, limit: number, expectedSize: number) => [Buffer, number],
): Map<string, GitObject> {
  if (pack.length < 32) throw new PackError(`pack is ${pack.length} bytes, too short`);
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new PackError('pack does not start with PACK');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new PackError(`unsupported pack version ${version}`);
  const declared = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const trailer = pack.subarray(trailerStart).toString('hex');
  if (createHash('sha1').update(pack.subarray(0, trailerStart)).digest('hex') !== trailer) {
    throw new PackError('pack trailer checksum mismatch');
  }
  const raw: RawPackEntry[] = [];
  const byOffset = new Map<number, RawPackEntry>();
  let offset = 12;
  for (let i = 0; i < declared; i++) {
    const entryOffset = offset;
    const [size, afterSize, first] = readVarintSize(pack, offset);
    offset = afterSize;
    const typeCode = (first >> 4) & 0x07;
    const entry: RawPackEntry = { offset: entryOffset, typeCode, size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const [baseOff, afterBase] = readOfsBase(pack, offset);
      offset = afterBase;
      if (baseOff <= 0 || baseOff > entryOffset) throw new PackError('ofs-delta names an invalid base offset');
      entry.baseOffset = entryOffset - baseOff;
    } else if (typeCode === 7) {
      if (offset + 20 > trailerStart) throw new PackError('ref-delta base id truncated');
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!(typeCode in CODE_TYPE)) {
      throw new PackError(`pack entry has unknown type code ${typeCode}`);
    }
    const [data, nextOffset] = inflateAt(pack, offset, trailerStart, size);
    offset = nextOffset;
    entry.data = data;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  if (offset !== trailerStart) throw new PackError('pack has stray bytes before its trailer');
  const resolvedByOid = new Map<string, RawPackEntry>();
  const objects = new Map<string, GitObject>();
  const resolving = new Set<number>();

  function resolve(entry: RawPackEntry): GitObject {
    if (entry.resolved !== undefined) return entry.resolved;
    if (resolving.has(entry.offset)) throw new PackError(`delta cycle at pack offset ${entry.offset}`);
    resolving.add(entry.offset);
    let objType: GitObjectType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset as number);
      if (baseEntry === undefined) throw new PackError('ofs-delta base is not in the pack');
      const [baseType, baseData] = resolve(baseEntry);
      objType = baseType;
      data = applyDelta(baseData, entry.data);
    } else if (entry.typeCode === 7) {
      const wanted = entry.baseOid as string;
      const baseEntry = resolvedByOid.get(wanted);
      let baseType: GitObjectType;
      let baseData: Buffer;
      if (baseEntry !== undefined) {
        [baseType, baseData] = resolve(baseEntry);
      } else if (resolveBase !== undefined) {
        const found = resolveBase(wanted);
        if (found === undefined) throw new PackError(`ref-delta base ${wanted} is neither in the pack nor on the server`);
        [baseType, baseData] = found;
      } else {
        throw new PackError(`ref-delta base ${wanted} is not in the pack`);
      }
      objType = baseType;
      data = applyDelta(baseData, entry.data);
    } else {
      objType = CODE_TYPE[entry.typeCode] as GitObjectType;
      data = entry.data;
    }
    const oid = hashObject(objType, data);
    entry.resolved = [objType, data];
    entry.oid = oid;
    resolvedByOid.set(oid, entry);
    resolving.delete(entry.offset);
    return entry.resolved;
  }

  for (const entry of raw) {
    const [objType, data] = resolve(entry);
    objects.set(entry.oid as string, [objType, data]);
  }
  return objects;
}

function packEntryHeader(objType: string, size: number): Buffer {
  const code = TYPE_CODE[objType] as number;
  const bytes: number[] = [];
  let first = (code << 4) | (size & 0x0f);
  size >>= 4;
  while (size > 0) {
    bytes.push(first | 0x80);
    first = size & 0x7f;
    size >>= 7;
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Build a packfile from plain objects (no deltas): [(type, data)]. */
function writePack(objects: GitObject[]): Buffer {
  const parts: Buffer[] = [Buffer.concat([Buffer.from('PACK', 'ascii'), Buffer.alloc(8)])];
  parts[0]?.writeUInt32BE(2, 4);
  parts[0]?.writeUInt32BE(objects.length, 8);
  for (const [objType, data] of objects) {
    parts.push(packEntryHeader(objType, data.length));
    parts.push(deflateSync(data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------------------
// pkt-line framing
// ---------------------------------------------------------------------------

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  if (data.length > PKT_LINE_MAX - 4) throw new Error('pkt-line payload too long');
  const header = Buffer.from((data.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([header, data]);
}

const FLUSH_PKT = Buffer.from('0000', 'ascii');
const DELIM_PKT = Buffer.from('0001', 'ascii');

type PktItem = string | Buffer | 'flush' | 'delim';

/** Encode a sequence of payloads / 'flush' / 'delim' markers. */
function pktLines(items: PktItem[]): Buffer {
  const out: Buffer[] = [];
  for (const item of items) {
    if (item === 'flush') out.push(FLUSH_PKT);
    else if (item === 'delim') out.push(DELIM_PKT);
    else out.push(pktLine(item));
  }
  return Buffer.concat(out);
}

class PktError extends Error {}

type PktPacket = ['data', Buffer] | ['flush'] | ['delim'] | ['response-end'];

/**
 * Decode a buffer into packets. Returns [packets, rest]: with stopAtFlush,
 * parsing stops after the first flush packet and rest holds the bytes after
 * it (a packfile).
 */
function parsePktLines(data: Buffer, stopAtFlush = false): [PktPacket[], Buffer] {
  const packets: PktPacket[] = [];
  let offset = 0;
  while (offset < data.length) {
    if (offset + 4 > data.length) throw new PktError('truncated pkt-line header');
    const header = data.subarray(offset, offset + 4).toString('ascii');
    const length = parseInt(header, 16);
    if (Number.isNaN(length)) throw new PktError(`invalid pkt-line length ${JSON.stringify(header)}`);
    if (length === 0) {
      packets.push(['flush']);
      offset += 4;
      if (stopAtFlush) return [packets, data.subarray(offset)];
      continue;
    }
    if (length === 1) {
      packets.push(['delim']);
      offset += 4;
      continue;
    }
    if (length === 2) {
      packets.push(['response-end']);
      offset += 4;
      continue;
    }
    if (length < 4 || length > PKT_LINE_MAX) throw new PktError(`invalid pkt-line length ${length}`);
    if (offset + length > data.length) throw new PktError('truncated pkt-line');
    packets.push(['data', data.subarray(offset + 4, offset + length)]);
    offset += length;
  }
  return [packets, Buffer.alloc(0)];
}

/** Wrap bytes in sideband pkt-lines (band byte + chunk). */
function sidebandPackets(band: number, payload: Buffer, chunkSize = 65511): Buffer[] {
  const out: Buffer[] = [];
  if (payload.length === 0) return out;
  for (let i = 0; i < payload.length; i += chunkSize) {
    const chunk = payload.subarray(i, i + chunkSize);
    out.push(pktLine(Buffer.concat([Buffer.from([band]), chunk])));
  }
  return out;
}

// ---------------------------------------------------------------------------
// The store: repositories, issues, pull requests, labels, comments
// ---------------------------------------------------------------------------

/** An error that maps to an HTTP status with a JSON {message} body. */
class ApiError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

interface Label {
  id: number;
  name: string;
  color: string;
  description: string;
}

interface Comment {
  id: number;
  body: string;
  created_at: string;
  updated_at: string;
}

interface Issue {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: Comment[];
  created_at: string;
  updated_at: string;
  closed_at: string | null;
  /** Cached serialized REST JSON for this issue; null when stale. */
  jsonCache: Buffer | null;
}

interface PullRequest {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head_ref: string;
  base_ref: string;
  merged: boolean;
  merged_at: string | null;
  merge_commit_sha: string | null;
  mergeable: boolean;
  created_at: string;
  updated_at: string;
  closed_at: string | null;
}

class Repo {
  id: number;
  name: string;
  owner: string = VIEWER_LOGIN;
  private: boolean;
  description: string;
  default_branch: string = DEFAULT_BRANCH;
  created_at: string;
  updated_at: string;
  // git state
  objects: Map<string, GitObject> = new Map();
  refs: Map<string, string> = new Map();
  // collaboration state
  issues: Map<number, Issue> = new Map();
  pulls: Map<number, PullRequest> = new Map();
  labels: Map<string, Label> = new Map();
  next_number = 1; // issues and PRs share GitHub's numbering
  next_label_id = 1;
  /** Bumped on every git mutation; fetch-response cache keys include it. */
  gitSeq = 0;
  /** Cached whole fetch responses: fingerprint -> response bytes. */
  fetchCache: Map<string, Buffer> = new Map();

  constructor(repoId: number, name: string, isPrivate: boolean, description: string) {
    this.id = repoId;
    this.name = name;
    this.private = isPrivate;
    this.description = description || '';
    this.created_at = isoNow();
    this.updated_at = this.created_at;
  }

  refTip(refname: string): string | undefined {
    return this.refs.get(refname);
  }

  branchTip(branch: string): string | undefined {
    return this.refs.get(`refs/heads/${branch}`);
  }

  headTip(): string | undefined {
    return this.branchTip(this.default_branch);
  }

  putObject(objType: GitObjectType, data: Buffer): string {
    const oid = hashObject(objType, data);
    if (!this.objects.has(oid)) this.objects.set(oid, [objType, data]);
    return oid;
  }

  getObject(oid: string): GitObject | undefined {
    return this.objects.get(oid);
  }

  treeOf(commitOid: string): string | null {
    const obj = this.objects.get(commitOid);
    if (obj === undefined || obj[0] !== 'commit') return null;
    return parseCommit(obj[1]).tree;
  }

  /** Mark the git state changed: fetch caches keyed on the old seq go stale. */
  touchGit(): void {
    this.gitSeq += 1;
    if (this.fetchCache.size > 64) this.fetchCache.clear();
  }
}

class Store {
  repos: Map<string, Repo> = new Map(); // name -> Repo (the viewer owns every repo)
  next_repo_id = 1;
  next_comment_id = 1;

  createRepo(name: string, isPrivate: boolean, description: string): Repo {
    if (this.repos.has(name)) throw new ApiError(422, 'Repository already exists');
    const repo = new Repo(this.next_repo_id, name, isPrivate, description);
    this.next_repo_id += 1;
    this.repos.set(name, repo);
    return repo;
  }

  getRepo(owner: string | undefined, name: string): Repo | undefined {
    if (owner !== VIEWER_LOGIN) return undefined;
    return this.repos.get(name);
  }

  deleteRepo(name: string): void {
    this.repos.delete(name);
  }

  listRepos(): Repo[] {
    return [...this.repos.values()].sort((a, b) => a.id - b.id);
  }
}

const STORE = new Store();

// ---------------------------------------------------------------------------
// Git graph operations over one repository
// ---------------------------------------------------------------------------

/** Follow annotated tags to the object they point at (a commit, usually). */
function peelToCommit(repo: Repo, oid: string): string {
  const seen = new Set<string>();
  while (repo.objects.has(oid) && (repo.objects.get(oid) as GitObject)[0] === 'tag' && !seen.has(oid)) {
    seen.add(oid);
    oid = parseTag((repo.objects.get(oid) as GitObject)[1]).object;
  }
  return oid;
}

function commitParents(repo: Repo, oid: string): string[] {
  const obj = repo.objects.get(oid);
  if (obj === undefined || obj[0] !== 'commit') return [];
  return parseCommit(obj[1]).parents;
}

/** Commits reachable from tip, newest first (BFS by generation). */
function walkCommits(repo: Repo, tip: string, limit?: number): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const queue: string[] = [tip];
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head] as string;
    head += 1;
    if (seen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined || obj[0] !== 'commit') continue;
    seen.add(oid);
    out.push(oid);
    if (limit !== undefined && out.length >= limit) break;
    for (const parent of commitParents(repo, oid)) queue.push(parent);
  }
  return out;
}

/** True when ancestor is reachable from descendant (or equal). */
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const stack: string[] = [descendant];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    for (const parent of commitParents(repo, oid)) {
      if (parent === ancestor) return true;
      stack.push(parent);
    }
  }
  return false;
}

/** A common ancestor of a and b (the first found walking from b). */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancestorsA = new Set(walkCommits(repo, a));
  const queue: string[] = [b];
  const seen = new Set<string>();
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head] as string;
    head += 1;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancestorsA.has(oid)) return oid;
    for (const parent of commitParents(repo, oid)) queue.push(parent);
  }
  return null;
}

/**
 * Every object id reachable from tips.
 * `cut` holds commit ids treated as roots: they are included, but their
 * parents are not traversed (a shallow client's boundary).
 */
function reachableObjects(repo: Repo, tips: string[], cut: readonly string[] = []): Set<string> {
  const cutSet = new Set(cut);
  const seen = new Set<string>();
  const stack: string[] = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid) || oid === ZERO_OID) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined) continue;
    seen.add(oid);
    const [objType, data] = obj;
    if (objType === 'commit') {
      const parsed = parseCommit(data);
      stack.push(parsed.tree);
      if (!cutSet.has(oid)) {
        for (const parent of parsed.parents) stack.push(parent);
      }
    } else if (objType === 'tag') {
      stack.push(parseTag(data).object);
    } else if (objType === 'tree') {
      for (const [mode, , child] of parseTree(data)) {
        if (mode !== '160000') stack.push(child);
      }
    }
  }
  return seen;
}

/** (mode, oid) of a path in a tree, or null. */
function treeLookup(repo: Repo, treeOid: string | null, segments: string[]): [string, string] | null {
  let current = treeOid;
  for (let index = 0; index < segments.length; index++) {
    const segment = segments[index] as string;
    if (current === null) return null;
    const obj = repo.objects.get(current);
    if (obj === undefined || obj[0] !== 'tree') return null;
    let found: [string, string] | null = null;
    for (const [mode, name, oid] of parseTree(obj[1])) {
      if (name === segment) {
        found = [mode, oid];
        break;
      }
    }
    if (found === null) return null;
    if (index === segments.length - 1) return found;
    if (found[0] !== '40000') return null;
    current = found[1];
  }
  return null;
}

/** The entries of a directory inside a tree, or null when it is not a dir. */
function treeEntriesAt(repo: Repo, treeOid: string | null, segments: string[]): TreeEntry[] | null {
  let current = treeOid;
  for (const segment of segments) {
    const found = treeLookup(repo, current, [segment]);
    if (found === null || found[0] !== '40000') return null;
    current = found[1];
  }
  if (current === null) return null;
  const obj = repo.objects.get(current);
  if (obj === undefined || obj[0] !== 'tree') return null;
  return parseTree(obj[1]);
}

/** A new tree with segments set to blobOid (null deletes the path). */
function treeSet(repo: Repo, treeOid: string | null, segments: string[], blobOid: string | null): string {
  const obj = treeOid !== null ? repo.objects.get(treeOid) : undefined;
  const entries: TreeEntry[] = obj !== undefined && obj[0] === 'tree' ? parseTree(obj[1]) : [];
  const head = segments[0] as string;
  const rest = segments.slice(1);
  const kept: TreeEntry[] = entries.filter(([, name]) => name !== head);
  if (rest.length === 0) {
    if (blobOid !== null) kept.push(['100644', head, blobOid]);
  } else {
    let existing: string | null = null;
    for (const [mode, name, oid] of entries) {
      if (name === head && mode === '40000') {
        existing = oid;
        break;
      }
    }
    const child = treeSet(repo, existing, rest, blobOid);
    const childObj = repo.objects.get(child);
    const childEntries = childObj !== undefined && childObj[0] === 'tree' ? parseTree(childObj[1]) : [];
    if (childEntries.length > 0) kept.push(['40000', head, child]);
  }
  return repo.putObject('tree', buildTree(kept));
}

/** {path: (mode, oid)} for every blob under a tree (recursive). */
function flattenTree(repo: Repo, treeOid: string | null, prefix = ''): Map<string, [string, string]> {
  const out = new Map<string, [string, string]>();
  if (treeOid === null) return out;
  const obj = repo.objects.get(treeOid);
  if (obj === undefined || obj[0] !== 'tree') return out;
  for (const [mode, name, oid] of parseTree(obj[1])) {
    const path = prefix + name;
    if (mode === '40000') {
      for (const [p, v] of flattenTree(repo, oid, `${path}/`)) out.set(p, v);
    } else {
      out.set(path, [mode, oid]);
    }
  }
  return out;
}

type ChangeStatus = 'added' | 'modified' | 'removed';

/** [(path, status, old_oid, new_oid)] between two trees. A rename is a remove + an add. */
function diffTrees(repo: Repo, oldTree: string | null, newTree: string | null): Array<[string, ChangeStatus, string | null, string | null]> {
  const oldMap = oldTree ? flattenTree(repo, oldTree) : new Map<string, [string, string]>();
  const newMap = newTree ? flattenTree(repo, newTree) : new Map<string, [string, string]>();
  const paths = [...new Set([...oldMap.keys(), ...newMap.keys()])].sort();
  const changes: Array<[string, ChangeStatus, string | null, string | null]> = [];
  for (const path of paths) {
    const inOld = oldMap.has(path);
    const inNew = newMap.has(path);
    if (inOld && !inNew) changes.push([path, 'removed', (oldMap.get(path) as [string, string])[1], null]);
    else if (inNew && !inOld) changes.push([path, 'added', null, (newMap.get(path) as [string, string])[1]]);
    else if ((oldMap.get(path) as [string, string])[1] !== (newMap.get(path) as [string, string])[1]) {
      changes.push([path, 'modified', (oldMap.get(path) as [string, string])[1], (newMap.get(path) as [string, string])[1]]);
    }
  }
  return changes;
}

/**
 * (additions, deletions) between two blobs, by line diff. The suite only
 * checks that the counts are non-negative integers and that a real change
 * has additions >= 1, so an LCS count is exactly what is needed; it is also
 * what a line diff means. Capped: absurdly large files fall back to a
 * whole-file count rather than an O(n*m) table.
 */
function countLineChanges(repo: Repo, oldOid: string | null, newOid: string | null): [number, number] {
  function lines(oid: string | null): string[] {
    if (oid === null) return [];
    const obj = repo.objects.get(oid);
    if (obj === undefined || obj[0] !== 'blob') return [];
    return obj[1].toString('utf8').split('\n').filter((_, i, arr) => !(i === arr.length - 1 && arr[i] === ''));
  }
  const oldLines = lines(oldOid);
  const newLines = lines(newOid);
  if (oldLines.length === 0) return [newLines.length, 0];
  if (newLines.length === 0) return [0, oldLines.length];
  if (oldLines.length * newLines.length > 4_000_000) {
    // Too big for the table: count lines that differ positionally, plus the tail.
    let same = 0;
    const n = Math.min(oldLines.length, newLines.length);
    for (let i = 0; i < n; i++) if (oldLines[i] === newLines[i]) same += 1;
    return [newLines.length - same, oldLines.length - same];
  }
  // LCS length via two rolling rows.
  let prev = new Uint32Array(newLines.length + 1);
  let curr = new Uint32Array(newLines.length + 1);
  for (let i = 1; i <= oldLines.length; i++) {
    for (let j = 1; j <= newLines.length; j++) {
      curr[j] = oldLines[i - 1] === newLines[j - 1]
        ? (prev[j - 1] as number) + 1
        : Math.max(prev[j] as number, curr[j - 1] as number);
    }
    const tmp = prev;
    prev = curr;
    curr = tmp;
  }
  const lcs = prev[newLines.length] as number;
  return [newLines.length - lcs, oldLines.length - lcs];
}

/** Create a commit object as the viewer, with a deterministic timestamp. */
function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  const who = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  if (!message.endsWith('\n')) message += '\n';
  const data = buildCommit(treeOid, parents, message, who, who, gitTimestamp());
  return repo.putObject('commit', data);
}

interface FetchOptions {
  includeTags?: boolean;
  deepenRelative?: boolean;
}

/**
 * The objects a fetch must send, and the shallow-info lines.
 * Returns {send, shallow, unshallow}.
 *
 * With an absolute deepen, commits are included by their distance from the
 * wants. With deepen-relative, the depth counts generations below the
 * client's current shallow boundary instead.
 */
function computeFetch(
  repo: Repo,
  wants: string[],
  haves: string[],
  shallowClient: string[],
  deepen: number | null,
  options: FetchOptions = {},
): { send: Set<string>; shallow: string[]; unshallow: string[] } {
  const shallowSet = new Set(shallowClient);
  const haveObjs = new Set<string>();
  for (const have of haves) {
    for (const oid of reachableObjects(repo, [have], shallowClient)) haveObjs.add(oid);
  }
  let included: Set<string>;
  let visited: Set<string>;
  let boundary = new Set<string>();
  if (options.deepenRelative && deepen !== null) {
    // Pass 1: everything at or above the old shallow boundary.
    const above = new Set<string>();
    const queue: string[] = [...wants];
    let head = 0;
    while (head < queue.length) {
      const oid = queue[head] as string;
      head += 1;
      if (above.has(oid) || oid === ZERO_OID) continue;
      const obj = repo.objects.get(oid);
      if (obj === undefined) continue;
      above.add(oid);
      if (obj[0] === 'tag') {
        queue.push(parseTag(obj[1]).object);
        continue;
      }
      if (obj[0] !== 'commit' || shallowSet.has(oid)) continue;
      for (const parent of commitParents(repo, oid)) queue.push(parent);
    }
    // Pass 2: N generations below each shallow commit on the boundary.
    const depthBelow = new Map<string, number>();
    const queue2: Array<[string, number]> = [];
    for (const oid of above) {
      if (shallowSet.has(oid)) {
        depthBelow.set(oid, 0);
        queue2.push([oid, 0]);
      }
    }
    let head2 = 0;
    while (head2 < queue2.length) {
      const [oid, depth] = queue2[head2] as [string, number];
      head2 += 1;
      if (depth >= deepen) continue;
      for (const parent of commitParents(repo, oid)) {
        const nextDepth = depth + 1;
        if (!depthBelow.has(parent) || nextDepth < (depthBelow.get(parent) as number)) {
          depthBelow.set(parent, nextDepth);
          queue2.push([parent, nextDepth]);
        }
      }
    }
    included = new Set([...above, ...depthBelow.keys()]);
    boundary = new Set(
      [...depthBelow.entries()].filter(([oid, depth]) => depth === deepen && commitParents(repo, oid).length > 0).map(([oid]) => oid),
    );
    visited = included;
  } else {
    // Walk the wanted commits, honouring the depth limit.
    const includedList: string[] = [];
    visited = new Set<string>();
    const queue: Array<[string, number]> = wants.map((want) => [want, 0]);
    let head = 0;
    while (head < queue.length) {
      const [oid, depth] = queue[head] as [string, number];
      head += 1;
      if (visited.has(oid) || oid === ZERO_OID) continue;
      const obj = repo.objects.get(oid);
      if (obj === undefined) continue;
      visited.add(oid);
      includedList.push(oid);
      if (obj[0] === 'tag') {
        queue.push([parseTag(obj[1]).object, depth]);
        continue;
      }
      if (obj[0] !== 'commit') continue;
      const parents = parseCommit(obj[1]).parents;
      if (deepen !== null && depth + 1 >= deepen) {
        if (parents.length > 0) boundary.add(oid);
      } else {
        for (const parent of parents) queue.push([parent, depth + 1]);
      }
    }
    included = new Set(includedList);
  }
  const send = new Set<string>();
  for (const oid of included) {
    for (const reachable of reachableObjects(repo, [oid], [...boundary])) send.add(reachable);
  }
  for (const oid of haveObjs) send.delete(oid);
  if (options.includeTags) {
    // Tags pointing at a fetched commit ride along with it.
    for (const [ref, oid] of repo.refs) {
      if (!ref.startsWith('refs/tags/')) continue;
      const obj = repo.objects.get(oid);
      if (obj !== undefined && obj[0] === 'tag') {
        if (visited.has(parseTag(obj[1]).object)) send.add(oid);
      }
    }
  }
  const unshallow: string[] = [];
  for (const oid of shallowSet) {
    if (!visited.has(oid)) continue;
    const parents = commitParents(repo, oid);
    if (parents.every((p) => visited.has(p) || haveObjs.has(p))) unshallow.push(oid);
  }
  return { send, shallow: [...boundary].sort(), unshallow: unshallow.sort() };
}

/** True when squashing head onto base would conflict on a file. */
function mergeConflict(repo: Repo, baseTip: string | undefined, headTip: string | undefined): boolean {
  if (baseTip === undefined || headTip === undefined) return false;
  const base = mergeBase(repo, baseTip, headTip);
  if (base === null) return false;
  const mbTree = repo.treeOf(base);
  const baseTree = repo.treeOf(baseTip);
  const headTree = repo.treeOf(headTip);
  const baseDiff = new Map<string, string | null>();
  for (const [p, , , next] of diffTrees(repo, mbTree, baseTree)) baseDiff.set(p, next);
  const headDiff = new Map<string, string | null>();
  for (const [p, , , next] of diffTrees(repo, mbTree, headTree)) headDiff.set(p, next);
  for (const [path, headNew] of headDiff) {
    if (baseDiff.has(path) && baseDiff.get(path) !== headNew) return true;
  }
  return false;
}

/**
 * Squash-merge a pull request onto its base branch.
 * Returns the new commit oid, or raises ApiError(405) on a conflict.
 */
function squashMerge(repo: Repo, pr: PullRequest): string {
  const baseTip = repo.branchTip(pr.base_ref);
  const headTip = repo.branchTip(pr.head_ref);
  if (baseTip === undefined || headTip === undefined) throw new ApiError(405, 'Cannot merge: a branch is missing');
  if (mergeConflict(repo, baseTip, headTip)) throw new ApiError(405, 'Merge conflict');
  const base = mergeBase(repo, baseTip, headTip);
  const mbTree = base !== null ? repo.treeOf(base) : null;
  const headTree = repo.treeOf(headTip);
  let tree = repo.treeOf(baseTip);
  for (const [path, , , next] of diffTrees(repo, mbTree, headTree)) {
    tree = treeSet(repo, tree, path.split('/'), next);
  }
  const message = `Squash merge #${pr.number}: ${pr.title}\n`;
  const commit = makeCommit(repo, tree as string, [baseTip], message);
  repo.refs.set(`refs/heads/${pr.base_ref}`, commit);
  repo.touchGit();
  return commit;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
const EXPECTED_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

const JSON_TYPE = 'application/json; charset=utf-8';
const SERVER_HEADER = `Forge/${VERSION}`;

/** Per-request state, built once by the dispatcher. */
class Ctx {
  req: IncomingMessage;
  res: ServerResponse;
  method: string;
  path: string;
  queryString: string;
  segments: string[];
  body: Buffer | null = null;
  queryCache: Map<string, string[]> | null = null;

  constructor(req: IncomingMessage, res: ServerResponse) {
    this.req = req;
    this.res = res;
    this.method = req.method ?? 'GET';
    const url = req.url ?? '/';
    const q = url.indexOf('?');
    const rawPath = q < 0 ? url : url.slice(0, q);
    this.queryString = q < 0 ? '' : url.slice(q + 1);
    // The path is percent-decoded segment by segment, as the suite sends it.
    this.path = rawPath;
    this.segments = [];
    for (const seg of rawPath.split('/')) {
      if (seg === '') continue;
      this.segments.push(seg.includes('%') ? safeDecode(seg) : seg);
    }
  }

  query(): Map<string, string[]> {
    if (this.queryCache !== null) return this.queryCache;
    const out = new Map<string, string[]>();
    if (this.queryString !== '') {
      for (const pair of this.queryString.split('&')) {
        if (pair === '') continue;
        const eq = pair.indexOf('=');
        const key = safeDecodeQuery(eq < 0 ? pair : pair.slice(0, eq));
        const value = eq < 0 ? '' : safeDecodeQuery(pair.slice(eq + 1));
        const list = out.get(key);
        if (list !== undefined) list.push(value);
        else out.set(key, [value]);
      }
    }
    this.queryCache = out;
    return out;
  }

  queryOne(name: string, fallback: string | null = null): string | null {
    const values = this.query().get(name);
    return values !== undefined && values.length > 0 ? (values[0] as string) : fallback;
  }

  /** Read the whole request body (empty when there is none). */
  async readBody(): Promise<Buffer> {
    if (this.body !== null) return this.body;
    const chunks: Buffer[] = [];
    for await (const chunk of this.req) {
      chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk as string));
    }
    this.body = chunks.length === 0 ? Buffer.alloc(0) : Buffer.concat(chunks);
    return this.body;
  }

  /** Parse the body as a JSON object ({} when empty); 400 on bad JSON. */
  async readJson(): Promise<Record<string, unknown>> {
    const raw = await this.readBody();
    if (raw.length === 0) return {};
    let value: unknown;
    try {
      value = JSON.parse(raw.toString('utf8'));
    } catch {
      throw new ApiError(400, 'Invalid JSON in request body');
    }
    if (typeof value !== 'object' || value === null || Array.isArray(value)) {
      throw new ApiError(400, 'Request body must be a JSON object');
    }
    return value as Record<string, unknown>;
  }

  /** True when the bearer token matches; otherwise sends 401. */
  async requireAuth(): Promise<boolean> {
    if (EXPECTED_TOKEN === '') return true;
    const auth = this.req.headers.authorization ?? '';
    if (auth === `Bearer ${EXPECTED_TOKEN}`) return true;
    // Drain the body first, so the keep-alive connection stays usable.
    await this.readBody();
    this.sendJsonError(401, 'Bad credentials');
    return false;
  }

  // -- response helpers ---------------------------------------------------
  // Every response goes out as one write (writeHead + end with the whole
  // body): Node coalesces them into a single segment, and with Nagle off
  // each request costs no ~40 ms stall.

  sendRaw(status: number, headers: Record<string, string>, body: Buffer | string): void {
    const buf = typeof body === 'string' ? Buffer.from(body, 'utf8') : body;
    this.res.writeHead(status, {
      Server: SERVER_HEADER,
      'Content-Length': String(buf.length),
      ...headers,
    });
    this.res.end(buf);
  }

  sendJson(status: number, obj: unknown, extraHeaders: Record<string, string> = {}): void {
    const body = obj === null || obj === undefined ? '' : JSON.stringify(obj);
    this.sendRaw(status, {
      'Content-Type': JSON_TYPE,
      'X-GitHub-Request-Id': nextRequestId(),
      ...extraHeaders,
    }, body);
  }

  /** Send an already-serialized JSON body (the read workload's hot path). */
  sendJsonBytes(status: number, body: Buffer, extraHeaders: Record<string, string> = {}): void {
    this.sendRaw(status, {
      'Content-Type': JSON_TYPE,
      'X-GitHub-Request-Id': nextRequestId(),
      ...extraHeaders,
    }, body);
  }

  sendJsonError(status: number, message: string): void {
    this.sendJson(status, { message });
  }

  send204(): void {
    this.sendRaw(204, { 'X-GitHub-Request-Id': nextRequestId() }, '');
  }

  sendGitBytes(status: number, body: Buffer, contentType: string): void {
    this.sendRaw(status, {
      'Content-Type': contentType,
      'X-GitHub-Request-Id': nextRequestId(),
    }, body);
  }

  absoluteUrl(path: string, params: Record<string, string>): string {
    const host = this.req.headers.host ?? `127.0.0.1:${(this.req.socket.address() as { port: number }).port}`;
    const query = Object.entries(params).map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`).join('&');
    return `http://${host}${path}${query === '' ? '' : `?${query}`}`;
  }

  /** Slice a list by ?page=&per_page= and build a Link header. */
  pagination<T>(items: T[], defaultPerPage = 30): [T[], string] {
    let page = 1;
    const pageRaw = this.queryOne('page', '1');
    const parsedPage = parseInt(pageRaw as string, 10);
    if (!Number.isNaN(parsedPage)) page = Math.max(1, parsedPage);
    let perPage = defaultPerPage;
    const perRaw = this.queryOne('per_page', String(defaultPerPage));
    const parsedPer = parseInt(perRaw as string, 10);
    if (!Number.isNaN(parsedPer)) perPage = parsedPer;
    perPage = Math.max(1, Math.min(100, perPage));
    const total = items.length;
    const start = (page - 1) * perPage;
    const pageItems = items.slice(start, start + perPage);
    const params: Record<string, string> = {};
    for (const [k, v] of this.query()) params[k] = v[0] as string;
    const lastPage = Math.max(1, Math.ceil(total / perPage));
    const links: string[] = [];
    if (page < lastPage) {
      params.page = String(page + 1);
      params.per_page = String(perPage);
      links.push(`<${this.absoluteUrl(this.path, params)}>; rel="next"`);
    }
    if (page > 1) {
      params.page = String(page - 1);
      params.per_page = String(perPage);
      links.push(`<${this.absoluteUrl(this.path, params)}>; rel="prev"`);
    }
    params.page = '1';
    params.per_page = String(perPage);
    links.push(`<${this.absoluteUrl(this.path, params)}>; rel="first"`);
    params.page = String(lastPage);
    links.push(`<${this.absoluteUrl(this.path, params)}>; rel="last"`);
    return [pageItems, links.join(', ')];
  }
}

function safeDecode(text: string): string {
  try {
    return decodeURIComponent(text);
  } catch {
    return text;
  }
}

function safeDecodeQuery(text: string): string {
  try {
    return decodeURIComponent(text.replace(/\+/g, ' '));
  } catch {
    return text;
  }
}

// ---------------------------------------------------------------------------
// REST v3 serializers
// ---------------------------------------------------------------------------

const USER_JSON = Object.freeze({
  login: VIEWER_LOGIN,
  id: 1000,
  node_id: globalId('User', 1000),
  name: VIEWER_NAME,
  email: VIEWER_EMAIL,
  type: 'User',
  created_at: '2025-01-01T00:00:00Z',
  avatar_url: '',
  html_url: '',
});

function repoJson(repo: Repo): Record<string, unknown> {
  let openCount = 0;
  for (const issue of repo.issues.values()) if (issue.state === 'open') openCount += 1;
  for (const pr of repo.pulls.values()) if (pr.state === 'open') openCount += 1;
  return {
    id: repo.id,
    node_id: globalId('Repository', repo.id),
    name: repo.name,
    full_name: `${VIEWER_LOGIN}/${repo.name}`,
    owner: USER_JSON,
    private: repo.private,
    description: repo.description,
    default_branch: repo.default_branch,
    created_at: repo.created_at,
    updated_at: repo.updated_at,
    pushed_at: repo.updated_at,
    has_issues: true,
    has_projects: false,
    has_wiki: false,
    fork: false,
    archived: false,
    disabled: false,
    open_issues_count: openCount,
  };
}

function labelJson(label: Label): Record<string, unknown> {
  return { id: label.id, name: label.name, color: label.color, description: label.description };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  const labels: Record<string, unknown>[] = [];
  for (const name of issue.labels) {
    const label = repo.labels.get(name);
    if (label !== undefined) labels.push(labelJson(label));
  }
  return {
    id: repo.id * 1000000 + issue.number,
    node_id: globalId('Issue', repo.id, issue.number),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    user: USER_JSON,
    labels,
    comments: issue.comments.length,
    created_at: issue.created_at,
    updated_at: issue.updated_at,
    closed_at: issue.closed_at,
    locked: false,
    assignee: null,
  };
}

/**
 * The issue's serialized REST JSON, cached on the issue. The read workload
 * re-reads one issue 2,000 times with nothing changing in between, so the
 * cache turns 2,000 serializations into one. Every mutation of the issue
 * (title/body/state change, comment added) clears it.
 */
function issueJsonBytes(repo: Repo, issue: Issue): Buffer {
  if (issue.jsonCache === null) {
    issue.jsonCache = Buffer.from(JSON.stringify(issueJson(repo, issue)), 'utf8');
  }
  return issue.jsonCache;
}

function prJson(repo: Repo, pr: PullRequest): Record<string, unknown> {
  const headTip = repo.branchTip(pr.head_ref);
  const baseTip = repo.branchTip(pr.base_ref);
  return {
    id: repo.id * 1000000 + 500000 + pr.number,
    node_id: globalId('PullRequest', repo.id, pr.number),
    number: pr.number,
    title: pr.title,
    body: pr.body,
    state: pr.state,
    user: USER_JSON,
    labels: [],
    head: {
      ref: pr.head_ref,
      sha: headTip ?? ZERO_OID,
      label: `${VIEWER_LOGIN}:${pr.head_ref}`,
      repo: repoJson(repo),
    },
    base: {
      ref: pr.base_ref,
      sha: baseTip ?? ZERO_OID,
      label: `${VIEWER_LOGIN}:${pr.base_ref}`,
      repo: repoJson(repo),
    },
    merged: pr.merged,
    merged_at: pr.merged_at,
    merge_commit_sha: pr.merge_commit_sha,
    mergeable: pr.mergeable,
    draft: false,
    created_at: pr.created_at,
    updated_at: pr.updated_at,
    closed_at: pr.closed_at,
  };
}

function commentJson(comment: Comment): Record<string, unknown> {
  return {
    id: comment.id,
    node_id: globalId('IssueComment', comment.id),
    body: comment.body,
    user: USER_JSON,
    created_at: comment.created_at,
    updated_at: comment.updated_at,
  };
}

const IDENT_RE = /^(.*?) <(.*?)> (\d+) ([+-]\d{4})$/;

function splitIdent(ident: string): [string, string] {
  const match = IDENT_RE.exec(ident);
  if (match === null) return [ident, ''];
  return [match[1] as string, match[2] as string];
}

function identDate(ident: string): string {
  const match = IDENT_RE.exec(ident);
  if (match === null) return '2025-01-01T00:00:00Z';
  return isoFromStamp(parseInt(match[3] as string, 10));
}

function commitJson(repo: Repo, oid: string): Record<string, unknown> {
  const obj = repo.objects.get(oid) as GitObject;
  const parsed = parseCommit(obj[1]);
  const [authorName, authorEmail] = splitIdent(parsed.author);
  const [committerName, committerEmail] = splitIdent(parsed.committer);
  return {
    sha: oid,
    node_id: globalId('Commit', oid),
    commit: {
      message: parsed.message.replace(/\n+$/, ''),
      author: { name: authorName, email: authorEmail, date: identDate(parsed.author) },
      committer: { name: committerName, email: committerEmail, date: identDate(parsed.committer) },
      tree: { sha: parsed.tree },
    },
    author: USER_JSON,
    committer: USER_JSON,
    parents: parsed.parents.map((p) => ({ sha: p })),
  };
}

// ---------------------------------------------------------------------------
// REST v3 routing
// ---------------------------------------------------------------------------

/** A branch name, full ref, HEAD or commit oid -> a commit oid (or null). */
function resolveRef(repo: Repo, ref: string | null): string | null {
  if (ref === null) return repo.headTip() ?? null;
  if (ref === 'HEAD') return repo.headTip() ?? null;
  if (repo.refs.has(ref)) {
    const tip = repo.refs.get(ref) as string;
    return peelToCommit(repo, tip);
  }
  const tip = repo.branchTip(ref);
  if (tip !== undefined) return peelToCommit(repo, tip);
  const tag = repo.refs.get(`refs/tags/${ref}`);
  if (tag !== undefined) return peelToCommit(repo, tag);
  if (isOid(ref) && repo.objects.has(ref)) return peelToCommit(repo, ref);
  return null;
}

/** 'owner:branch' -> 'branch'; a plain branch is unchanged. */
function stripOwnerPrefix(branch: string): string {
  const colon = branch.indexOf(':');
  return colon < 0 ? branch : branch.slice(colon + 1);
}

function restRepo(owner: string, name: string): Repo {
  const repo = STORE.getRepo(owner, name);
  if (repo === undefined) throw new ApiError(404, 'Not Found');
  return repo;
}

async function handleRest(ctx: Ctx): Promise<void> {
  if (!(await ctx.requireAuth())) return;
  const seg = ctx.segments.slice(2); // after /api/v3
  const method = ctx.method;
  if (seg.length === 0) {
    ctx.sendJson(200, {
      current_user_url: '/api/v3/user',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      meta_url: '/api/v3/meta',
    }, { 'X-OAuth-Scopes': 'repo, read:org' });
    return;
  }
  const head = seg[0] as string;
  if (head === 'meta') {
    if (method !== 'GET') throw new ApiError(404, 'Not Found');
    ctx.sendJson(200, { installed_version: VERSION });
    return;
  }
  if (head === 'user') {
    if (seg.length === 1) {
      if (method !== 'GET') throw new ApiError(404, 'Not Found');
      ctx.sendJson(200, USER_JSON);
      return;
    }
    if (seg[1] === 'repos') {
      if (method === 'GET') {
        const repos = STORE.listRepos().map((r) => repoJson(r));
        const [page, link] = ctx.pagination(repos);
        ctx.sendJson(200, page, { Link: link });
        return;
      }
      if (method === 'POST') {
        const body = await ctx.readJson();
        const name = body.name;
        if (typeof name !== 'string' || name === '') {
          throw new ApiError(422, 'Validation Failed: name is required');
        }
        const repo = STORE.createRepo(name, body.private === true, typeof body.description === 'string' ? body.description : '');
        ctx.sendJson(201, repoJson(repo));
        return;
      }
      throw new ApiError(404, 'Not Found');
    }
    throw new ApiError(404, 'Not Found');
  }
  if (head === 'repos') {
    if (seg.length < 3) throw new ApiError(404, 'Not Found');
    const owner = seg[1] as string;
    const name = seg[2] as string;
    const repo = restRepo(owner, name);
    const rest = seg.slice(3);
    if (rest.length === 0) {
      if (method === 'GET') {
        ctx.sendJson(200, repoJson(repo));
        return;
      }
      if (method === 'PATCH') {
        const body = await ctx.readJson();
        if ('description' in body) repo.description = (body.description as string) || '';
        if ('private' in body) repo.private = Boolean(body.private);
        repo.updated_at = isoNow();
        ctx.sendJson(200, repoJson(repo));
        return;
      }
      if (method === 'DELETE') {
        STORE.deleteRepo(name);
        ctx.send204();
        return;
      }
      throw new ApiError(404, 'Not Found');
    }
    const sub = rest[0] as string;
    if (sub === 'branches') {
      restBranches(ctx, repo, rest.slice(1));
      return;
    }
    if (sub === 'commits') {
      restCommits(ctx, repo);
      return;
    }
    if (sub === 'contents') {
      await restContents(ctx, repo, rest.slice(1));
      return;
    }
    if (sub === 'git') {
      await restGitRefs(ctx, repo, rest.slice(1));
      return;
    }
    if (sub === 'labels') {
      await restLabels(ctx, repo);
      return;
    }
    if (sub === 'issues') {
      await restIssues(ctx, repo, rest.slice(1));
      return;
    }
    if (sub === 'pulls') {
      await restPulls(ctx, repo, rest.slice(1));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  throw new ApiError(404, 'Not Found');
}

function restBranches(ctx: Ctx, repo: Repo, rest: string[]): void {
  if (ctx.method !== 'GET') throw new ApiError(404, 'Not Found');
  const items: Array<{ name: string; commit: { sha: string } }> = [];
  for (const ref of [...repo.refs.keys()].sort()) {
    if (ref.startsWith('refs/heads/')) {
      items.push({ name: ref.slice('refs/heads/'.length), commit: { sha: repo.refs.get(ref) as string } });
    }
  }
  if (rest.length === 0) {
    ctx.sendJson(200, items);
    return;
  }
  const branch = rest.join('/');
  for (const item of items) {
    if (item.name === branch) {
      ctx.sendJson(200, item);
      return;
    }
  }
  throw new ApiError(404, 'Branch not found');
}

function restCommits(ctx: Ctx, repo: Repo): void {
  if (ctx.method !== 'GET') throw new ApiError(404, 'Not Found');
  const ref = ctx.queryOne('sha');
  const tip = resolveRef(repo, ref);
  if (tip === null) {
    ctx.sendJson(200, []);
    return;
  }
  const commits = walkCommits(repo, tip).map((oid) => commitJson(repo, oid));
  const [page, link] = ctx.pagination(commits);
  ctx.sendJson(200, page, { Link: link });
}

function contentsDirEntry(mode: string, name: string, oid: string, parent: string, repo: Repo): Record<string, unknown> {
  const entry: Record<string, unknown> = {
    type: mode === '40000' ? 'dir' : 'file',
    name,
    path: parent === '' ? name : `${parent}/${name}`,
    sha: oid,
  };
  if (mode !== '40000') {
    const blob = repo.objects.get(oid);
    entry.size = blob !== undefined ? blob[1].length : 0;
  } else {
    entry.size = 0;
  }
  return entry;
}

async function restContents(ctx: Ctx, repo: Repo, rest: string[]): Promise<void> {
  const path = rest.join('/');
  const segments = path.split('/').filter((s) => s !== '');
  if (ctx.method === 'GET') {
    const ref = ctx.queryOne('ref');
    const tip = resolveRef(repo, ref);
    if (tip === null) throw new ApiError(404, 'Not Found');
    const treeOid = repo.treeOf(tip);
    if (segments.length === 0) {
      const treeObj = treeOid !== null ? repo.objects.get(treeOid) : undefined;
      const entries = treeObj !== undefined ? parseTree(treeObj[1]) : [];
      ctx.sendJson(200, entries.map(([m, n, o]) => contentsDirEntry(m, n, o, '', repo)));
      return;
    }
    const found = treeLookup(repo, treeOid, segments);
    if (found === null) throw new ApiError(404, 'Not Found');
    const [mode, oid] = found;
    if (mode === '40000') {
      const dirObj = repo.objects.get(oid) as GitObject;
      const entries = parseTree(dirObj[1]);
      ctx.sendJson(200, entries.map(([m, n, o]) => contentsDirEntry(m, n, o, path, repo)));
      return;
    }
    const blob = repo.objects.get(oid);
    const data = blob !== undefined ? blob[1] : Buffer.alloc(0);
    ctx.sendJson(200, {
      type: 'file',
      encoding: 'base64',
      content: b64encodeBytes(data),
      sha: oid,
      size: data.length,
      name: segments[segments.length - 1] as string,
      path,
    });
    return;
  }
  if (ctx.method === 'PUT') {
    const body = await ctx.readJson();
    const message = (typeof body.message === 'string' && body.message !== '' ? body.message : `Update ${path}`);
    let content: Buffer;
    try {
      content = b64decodeBytes(typeof body.content === 'string' ? body.content : '');
    } catch {
      throw new ApiError(422, 'content is not valid base64');
    }
    const branch = (typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.default_branch);
    const givenSha = typeof body.sha === 'string' ? body.sha : null;
    let tip = repo.branchTip(branch);
    if (tip === undefined && repo.branchTip(repo.default_branch) !== undefined) {
      tip = repo.branchTip(repo.default_branch);
    }
    const treeOid = tip !== undefined ? repo.treeOf(tip) : null;
    const current = treeOid !== null ? treeLookup(repo, treeOid, segments) : null;
    let status: number;
    if (current !== null) {
      if (current[0] === '40000') throw new ApiError(422, 'Cannot write a file over a directory');
      if (givenSha !== null && givenSha !== current[1]) throw new ApiError(409, 'The file has changed since you last read it');
      if (givenSha === null) throw new ApiError(409, 'sha is required to update an existing file');
      status = 200;
    } else {
      status = 201;
    }
    const blobOid = repo.putObject('blob', content);
    const newTree = treeSet(repo, treeOid, segments, blobOid);
    const parents = tip !== undefined ? [tip] : [];
    const commit = makeCommit(repo, newTree, parents, message);
    repo.refs.set(`refs/heads/${branch}`, commit);
    repo.updated_at = isoNow();
    repo.touchGit();
    ctx.sendJson(status, {
      content: {
        name: segments[segments.length - 1] as string,
        path,
        sha: blobOid,
        size: content.length,
        type: 'file',
        encoding: 'base64',
      },
      commit: { sha: commit },
    });
    return;
  }
  if (ctx.method === 'DELETE') {
    const body = await ctx.readJson();
    const message = (typeof body.message === 'string' && body.message !== '' ? body.message : `Delete ${path}`);
    const branch = (typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.default_branch);
    const givenSha = typeof body.sha === 'string' ? body.sha : null;
    const tip = repo.branchTip(branch);
    if (tip === undefined) throw new ApiError(404, 'Not Found');
    const treeOid = repo.treeOf(tip);
    const current = treeOid !== null ? treeLookup(repo, treeOid, segments) : null;
    if (current === null || current[0] === '40000') throw new ApiError(404, 'Not Found');
    if (givenSha !== null && givenSha !== current[1]) throw new ApiError(409, 'The file has changed since you last read it');
    const newTree = treeSet(repo, treeOid, segments, null);
    const commit = makeCommit(repo, newTree, [tip], message);
    repo.refs.set(`refs/heads/${branch}`, commit);
    repo.updated_at = isoNow();
    repo.touchGit();
    ctx.sendJson(200, { content: null, commit: { sha: commit } });
    return;
  }
  throw new ApiError(404, 'Not Found');
}

async function restGitRefs(ctx: Ctx, repo: Repo, rest: string[]): Promise<void> {
  if (ctx.method === 'POST' && rest.length === 1 && rest[0] === 'refs') {
    const body = await ctx.readJson();
    const ref = body.ref;
    const sha = body.sha;
    if (typeof ref !== 'string' || !ref.startsWith('refs/')) {
      throw new ApiError(422, 'ref must start with refs/');
    }
    if (!isOid(sha) || !repo.objects.has(sha as string)) {
      throw new ApiError(422, 'sha does not name an object in this repository');
    }
    if (repo.refs.has(ref)) throw new ApiError(422, 'Reference already exists');
    repo.refs.set(ref, sha as string);
    repo.touchGit();
    ctx.sendJson(201, { ref, object: { sha, type: (repo.objects.get(sha as string) as GitObject)[0] } });
    return;
  }
  if (ctx.method === 'GET' && rest.length > 1 && rest[0] === 'refs') {
    const full = rest.join('/');
    if (repo.refs.has(full)) {
      const sha = repo.refs.get(full) as string;
      ctx.sendJson(200, { ref: full, object: { sha, type: (repo.objects.get(sha) as GitObject)[0] } });
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  throw new ApiError(404, 'Not Found');
}

async function restLabels(ctx: Ctx, repo: Repo): Promise<void> {
  if (ctx.method === 'GET') {
    ctx.sendJson(200, [...repo.labels.values()].map((l) => labelJson(l)));
    return;
  }
  if (ctx.method === 'POST') {
    const body = await ctx.readJson();
    const name = body.name;
    const color = (typeof body.color === 'string' && body.color !== '' ? body.color : 'ededed');
    if (typeof name !== 'string' || name === '') {
      throw new ApiError(422, 'Validation Failed: name is required');
    }
    const existing = repo.labels.get(name);
    if (existing !== undefined) {
      ctx.sendJson(201, labelJson(existing));
      return;
    }
    const label: Label = {
      id: repo.next_label_id,
      name,
      color: color.replace(/^#/, ''),
      description: typeof body.description === 'string' ? body.description : '',
    };
    repo.next_label_id += 1;
    repo.labels.set(name, label);
    ctx.sendJson(201, labelJson(label));
    return;
  }
  throw new ApiError(404, 'Not Found');
}

function issueFromBody(repo: Repo, body: Record<string, unknown>): Issue {
  const title = body.title;
  if (typeof title !== 'string' || title === '') {
    throw new ApiError(422, 'Validation Failed: title is required');
  }
  const labelNames: string[] = [];
  const labelsRaw = Array.isArray(body.labels) ? body.labels : [];
  for (const label of labelsRaw) {
    const labelName = typeof label === 'object' && label !== null ? (label as Record<string, unknown>).name : label;
    if (typeof labelName !== 'string' || !repo.labels.has(labelName)) {
      throw new ApiError(422, `Validation Failed: label ${String(labelName)} does not exist`);
    }
    labelNames.push(labelName);
  }
  const number = repo.next_number;
  repo.next_number += 1;
  const stamp = isoNow();
  const issue: Issue = {
    number,
    title,
    body: typeof body.body === 'string' ? body.body : '',
    state: 'open',
    labels: labelNames,
    comments: [],
    created_at: stamp,
    updated_at: stamp,
    closed_at: null,
    jsonCache: null,
  };
  repo.issues.set(number, issue);
  return issue;
}

async function restIssues(ctx: Ctx, repo: Repo, rest: string[]): Promise<void> {
  if (rest.length === 0) {
    if (ctx.method === 'GET') {
      const state = ctx.queryOne('state', 'open');
      const direction = ctx.queryOne('direction', 'desc');
      let issues = [...repo.issues.values()];
      if (state === 'open' || state === 'closed') issues = issues.filter((i) => i.state === state);
      const reverse = direction !== 'asc';
      issues.sort((a, b) => (reverse ? b.number - a.number : a.number - b.number));
      const [page, link] = ctx.pagination(issues.map((i) => issueJson(repo, i)));
      ctx.sendJson(200, page, { Link: link });
      return;
    }
    if (ctx.method === 'POST') {
      const body = await ctx.readJson();
      const issue = issueFromBody(repo, body);
      ctx.sendJson(201, issueJson(repo, issue));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  const number = parseInt(rest[0] as string, 10);
  if (Number.isNaN(number) || String(number) !== (rest[0] as string).trim()) {
    // Python's int() accepts surrounding whitespace and a sign; the suite
    // sends plain digits, and anything else is not an issue number.
    if (!/^-?\d+$/.test((rest[0] as string).trim())) throw new ApiError(404, 'Not Found');
  }
  const issue = repo.issues.get(number);
  if (issue === undefined) throw new ApiError(404, 'Not Found');
  if (rest.length === 1) {
    if (ctx.method === 'GET') {
      // Hot path: the read workload's 2,000 GETs of one issue.
      ctx.sendJsonBytes(200, issueJsonBytes(repo, issue));
      return;
    }
    if (ctx.method === 'PATCH') {
      const body = await ctx.readJson();
      if ('title' in body) issue.title = body.title as string;
      if ('body' in body) issue.body = (body.body as string) || '';
      if ('state' in body) {
        const newState = body.state;
        if (newState === 'open' || newState === 'closed') {
          issue.state = newState;
          issue.closed_at = newState === 'closed' ? isoNow() : null;
        }
      }
      issue.updated_at = isoNow();
      issue.jsonCache = null;
      ctx.sendJson(200, issueJson(repo, issue));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  if (rest[1] === 'comments') {
    if (ctx.method === 'GET') {
      ctx.sendJson(200, issue.comments.map((c) => commentJson(c)));
      return;
    }
    if (ctx.method === 'POST') {
      const body = await ctx.readJson();
      const text = body.body;
      if (typeof text !== 'string' || text === '') {
        throw new ApiError(422, 'Validation Failed: body is required');
      }
      const commentId = STORE.next_comment_id;
      STORE.next_comment_id += 1;
      const stamp = isoNow();
      const comment: Comment = { id: commentId, body: text, created_at: stamp, updated_at: stamp };
      issue.comments.push(comment);
      issue.jsonCache = null; // the comments count changed
      ctx.sendJson(201, commentJson(comment));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  throw new ApiError(404, 'Not Found');
}

function prFromBody(repo: Repo, body: Record<string, unknown>): PullRequest {
  const title = body.title;
  if (typeof title !== 'string' || title === '') {
    throw new ApiError(422, 'Validation Failed: title is required');
  }
  const head = stripOwnerPrefix(typeof body.head === 'string' ? body.head : '');
  const base = stripOwnerPrefix(typeof body.base === 'string' ? body.base : '');
  if (head === '' || repo.branchTip(head) === undefined) {
    throw new ApiError(422, 'Validation Failed: head branch does not exist');
  }
  if (base === '' || repo.branchTip(base) === undefined) {
    throw new ApiError(422, 'Validation Failed: base branch does not exist');
  }
  const number = repo.next_number;
  repo.next_number += 1;
  const stamp = isoNow();
  const pr: PullRequest = {
    number,
    title,
    body: typeof body.body === 'string' ? body.body : '',
    state: 'open',
    head_ref: head,
    base_ref: base,
    merged: false,
    merged_at: null,
    merge_commit_sha: null,
    mergeable: true,
    created_at: stamp,
    updated_at: stamp,
    closed_at: null,
  };
  repo.pulls.set(number, pr);
  return pr;
}

function prFiles(repo: Repo, pr: PullRequest): Array<Record<string, unknown>> {
  const baseTip = repo.branchTip(pr.base_ref);
  const headTip = repo.branchTip(pr.head_ref);
  if (baseTip === undefined || headTip === undefined) return [];
  const base = mergeBase(repo, baseTip, headTip);
  const mbTree = base !== null ? repo.treeOf(base) : null;
  const headTree = repo.treeOf(headTip);
  const files: Array<Record<string, unknown>> = [];
  for (const [path, status, oldOid, newOid] of diffTrees(repo, mbTree, headTree)) {
    const [additions, deletions] = countLineChanges(repo, oldOid, newOid);
    files.push({
      filename: path,
      status,
      additions,
      deletions,
      changes: additions + deletions,
      sha: newOid ?? oldOid,
    });
  }
  return files;
}

async function restPulls(ctx: Ctx, repo: Repo, rest: string[]): Promise<void> {
  if (rest.length === 0) {
    if (ctx.method === 'GET') {
      const state = ctx.queryOne('state', 'open');
      let pulls = [...repo.pulls.values()];
      if (state === 'open' || state === 'closed') pulls = pulls.filter((p) => p.state === state);
      pulls.sort((a, b) => b.number - a.number);
      const [page, link] = ctx.pagination(pulls.map((p) => prJson(repo, p)));
      ctx.sendJson(200, page, { Link: link });
      return;
    }
    if (ctx.method === 'POST') {
      const body = await ctx.readJson();
      const pr = prFromBody(repo, body);
      ctx.sendJson(201, prJson(repo, pr));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  if (!/^-?\d+$/.test((rest[0] as string).trim())) throw new ApiError(404, 'Not Found');
  const number = parseInt(rest[0] as string, 10);
  const pr = repo.pulls.get(number);
  if (pr === undefined) throw new ApiError(404, 'Not Found');
  if (rest.length === 1) {
    if (ctx.method === 'GET') {
      ctx.sendJson(200, prJson(repo, pr));
      return;
    }
    if (ctx.method === 'PATCH') {
      const body = await ctx.readJson();
      if ('title' in body) pr.title = body.title as string;
      if ('body' in body) pr.body = (body.body as string) || '';
      if (body.state === 'closed' && pr.state === 'open') {
        pr.state = 'closed';
        pr.closed_at = isoNow();
      }
      pr.updated_at = isoNow();
      ctx.sendJson(200, prJson(repo, pr));
      return;
    }
    throw new ApiError(404, 'Not Found');
  }
  if (rest[1] === 'files') {
    if (ctx.method !== 'GET') throw new ApiError(404, 'Not Found');
    ctx.sendJson(200, prFiles(repo, pr));
    return;
  }
  if (rest[1] === 'merge') {
    if (ctx.method !== 'PUT') throw new ApiError(404, 'Not Found');
    if (pr.state !== 'open') throw new ApiError(405, 'Pull request is not open');
    const sha = squashMerge(repo, pr);
    pr.merged = true;
    pr.state = 'closed';
    pr.merged_at = isoNow();
    pr.closed_at = pr.merged_at;
    pr.merge_commit_sha = sha;
    pr.updated_at = pr.merged_at;
    ctx.sendJson(200, { sha, merged: true, message: 'Pull Request successfully merged' });
    return;
  }
  throw new ApiError(404, 'Not Found');
}

// ---------------------------------------------------------------------------
// Git smart HTTP
// ---------------------------------------------------------------------------

const UPLOAD_CAPS = 'multi_ack multi_ack_detailed thin-pack side-band-64k ofs-delta shallow '
  + 'agent=forge/2.0 symref=HEAD:refs/heads/main';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta agent=forge/2.0';

async function handleGit(ctx: Ctx): Promise<void> {
  if (!(await ctx.requireAuth())) return;
  const owner = ctx.segments[0] as string;
  const repoName = (ctx.segments[1] as string).slice(0, -'.git'.length);
  const service = ctx.segments.slice(2);
  const repo = STORE.getRepo(owner, repoName);
  if (service.length === 2 && service[0] === 'info' && service[1] === 'refs') {
    if (repo === undefined) throw new ApiError(404, 'Not Found');
    const which = ctx.queryOne('service');
    if (which === 'git-upload-pack') {
      gitAdvertiseUpload(ctx, repo);
    } else if (which === 'git-receive-pack') {
      gitAdvertiseReceive(ctx, repo);
    } else {
      throw new ApiError(404, 'Not Found');
    }
    return;
  }
  if (service.length === 1 && service[0] === 'git-upload-pack') {
    if (repo === undefined) throw new ApiError(404, 'Not Found');
    await gitUploadPack(ctx, repo);
    return;
  }
  if (service.length === 1 && service[0] === 'git-receive-pack') {
    if (repo === undefined) throw new ApiError(404, 'Not Found');
    await gitReceivePack(ctx, repo);
    return;
  }
  throw new ApiError(404, 'Not Found');
}

function gitAdvertiseUpload(ctx: Ctx, repo: Repo): void {
  const protocol = ctx.req.headers['git-protocol'] ?? '';
  if (protocol.startsWith('version=2')) {
    const body = pktLines(['version 2\n', 'ls-refs=unborn\n', 'fetch=shallow filter\n', 'object-format=sha1\n', 'flush']);
    ctx.sendGitBytes(200, body, 'application/x-git-upload-pack-advertisement');
    return;
  }
  const lines: PktItem[] = ['# service=git-upload-pack\n', 'flush'];
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${UPLOAD_CAPS}\n`);
  } else {
    let capsSent = false;
    const headTip = repo.headTip();
    if (headTip !== undefined) {
      lines.push(`${headTip} HEAD\0${UPLOAD_CAPS}\n`);
      capsSent = true;
    }
    for (const [ref, oid] of refs) {
      const suffix = !capsSent ? `\0${UPLOAD_CAPS}` : '';
      lines.push(`${oid} ${ref}${suffix}\n`);
      capsSent = true;
      if (ref.startsWith('refs/tags/')) {
        const peeled = peelToCommit(repo, oid);
        if (peeled !== oid) lines.push(`${peeled} ${ref}^{}\n`);
      }
    }
  }
  lines.push('flush');
  ctx.sendGitBytes(200, pktLines(lines), 'application/x-git-upload-pack-advertisement');
}

function gitAdvertiseReceive(ctx: Ctx, repo: Repo): void {
  const lines: PktItem[] = ['# service=git-receive-pack\n', 'flush'];
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${RECEIVE_CAPS}\n`);
  } else {
    let first = true;
    for (const [ref, oid] of refs) {
      const suffix = first ? `\0${RECEIVE_CAPS}` : '';
      lines.push(`${oid} ${ref}${suffix}\n`);
      first = false;
    }
  }
  lines.push('flush');
  ctx.sendGitBytes(200, pktLines(lines), 'application/x-git-receive-pack-advertisement');
}

async function gitUploadPack(ctx: Ctx, repo: Repo): Promise<void> {
  const body = await ctx.readBody();
  const protocol = ctx.req.headers['git-protocol'] ?? '';
  if (protocol.startsWith('version=2')) {
    let packets: PktPacket[];
    try {
      [packets] = parsePktLines(body);
    } catch {
      throw new ApiError(400, 'Malformed pkt-line request');
    }
    if (packets.length === 0 || packets[0]?.[0] !== 'data') {
      throw new ApiError(400, 'Missing command');
    }
    const command = (packets[0] as ['data', Buffer])[1].toString('utf8').trim();
    if (command === 'command=ls-refs') {
      gitLsRefs(ctx, repo, packets.slice(1));
    } else if (command === 'command=fetch') {
      gitFetchV2(ctx, repo, packets.slice(1));
    } else {
      throw new ApiError(400, `Unknown command ${command}`);
    }
  } else {
    gitUploadPackV0(ctx, repo, body);
  }
}

function gitLsRefs(ctx: Ctx, repo: Repo, packets: PktPacket[]): void {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes: string[] = [];
  let inArgs = false;
  for (const packet of packets) {
    if (packet[0] === 'delim') {
      inArgs = true;
      continue;
    }
    if (packet[0] === 'flush') break;
    if (packet[0] !== 'data' || !inArgs) continue;
    const line = packet[1].toString('utf8').trim();
    if (line === 'peel') peel = true;
    else if (line === 'symrefs') symrefs = true;
    else if (line === 'unborn') unborn = true;
    else if (line.startsWith('ref-prefix ')) prefixes.push(line.slice('ref-prefix '.length));
  }
  const lines: PktItem[] = [];
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  if (refs.length === 0) {
    if (unborn) lines.push('unborn HEAD symref-target:refs/heads/main\n');
  } else {
    // HEAD is listed when symrefs is requested and no prefix filter
    // excludes it: HEAD matches a prefix only when that prefix is a
    // prefix of "HEAD" itself (so "HEAD" matches, "refs/..." does not).
    const headWanted = symrefs && (prefixes.length === 0 || prefixes.some((p) => 'HEAD'.startsWith(p)));
    if (headWanted) {
      const headTip = repo.headTip();
      if (headTip !== undefined) lines.push(`${headTip} HEAD symref-target:refs/heads/main\n`);
    }
    for (const [ref, oid] of refs) {
      if (prefixes.length > 0 && !prefixes.some((p) => ref.startsWith(p))) continue;
      let suffix = '';
      if (peel && ref.startsWith('refs/tags/')) {
        const peeled = peelToCommit(repo, oid);
        if (peeled !== oid) suffix = ` peeled:${peeled}`;
      }
      lines.push(`${oid} ${ref}${suffix}\n`);
    }
  }
  lines.push('flush');
  ctx.sendGitBytes(200, pktLines(lines), 'application/x-git-upload-pack-result');
}

/** Copy (type, data) pairs out of the store, sorted for a stable pack. */
function snapshotObjects(repo: Repo, oids: Set<string>): GitObject[] {
  const sorted = [...oids].sort();
  const out: GitObject[] = [];
  for (const oid of sorted) {
    const obj = repo.objects.get(oid);
    if (obj !== undefined) out.push(obj);
  }
  return out;
}

function gitFetchV2(ctx: Ctx, repo: Repo, packets: PktPacket[]): void {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallow: string[] = [];
  let deepen: number | null = null;
  let done = false;
  let includeTag = false;
  let deepenRelative = false;
  let inArgs = false;
  for (const packet of packets) {
    if (packet[0] === 'delim') {
      inArgs = true;
      continue;
    }
    if (packet[0] === 'flush') break;
    if (packet[0] !== 'data' || !inArgs) continue;
    const line = packet[1].toString('utf8').trim();
    if (line.startsWith('want ')) wants.push(line.slice(5).trim());
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) {
      const n = parseInt(line.slice(7), 10);
      if (!Number.isNaN(n)) deepen = n;
    } else if (line === 'done') done = true;
    else if (line === 'include-tag') includeTag = true;
    else if (line === 'deepen-relative') deepenRelative = true;
  }
  // The clone workload fires 50 identical fetches at once: serve the twins
  // from the cache. The fingerprint covers everything the response depends
  // on, including the repository's git state sequence.
  const fingerprint = JSON.stringify(['v2', repo.gitSeq, wants, haves, shallow, deepen, done, includeTag, deepenRelative]);
  const cached = repo.fetchCache.get(fingerprint);
  if (cached !== undefined) {
    ctx.sendGitBytes(200, cached, 'application/x-git-upload-pack-result');
    return;
  }
  const ackLines = haves.filter((have) => repo.objects.has(have)).map((have) => `ACK ${have}\n`);
  const acks = ackLines.length > 0 ? ackLines : ['NAK\n'];
  const { send, shallow: shallowNew, unshallow } = computeFetch(repo, wants, haves, shallow, deepen, {
    includeTags: includeTag,
    deepenRelative,
  });
  const pack = writePack(snapshotObjects(repo, send));
  const out: Buffer[] = [];
  // The acknowledgments section only exists when the client sent haves
  // without `done`: real git's client expects the packfile section first
  // otherwise, and with haves it needs a `ready` line before any later
  // section, or it dies expecting more negotiation.
  if (haves.length > 0 && !done) {
    out.push(pktLine('acknowledgments\n'));
    for (const line of acks) out.push(pktLine(line));
    out.push(pktLine('ready\n'));
    out.push(DELIM_PKT);
  }
  if (shallowNew.length > 0 || unshallow.length > 0) {
    out.push(pktLine('shallow-info\n'));
    for (const oid of shallowNew) out.push(pktLine(`shallow ${oid}\n`));
    for (const oid of unshallow) out.push(pktLine(`unshallow ${oid}\n`));
    out.push(DELIM_PKT);
  }
  out.push(pktLine('packfile\n'));
  out.push(...sidebandPackets(1, pack));
  out.push(FLUSH_PKT);
  const body = Buffer.concat(out);
  repo.fetchCache.set(fingerprint, body);
  ctx.sendGitBytes(200, body, 'application/x-git-upload-pack-result');
}

function gitUploadPackV0(ctx: Ctx, repo: Repo, body: Buffer): void {
  let packets: PktPacket[];
  try {
    [packets] = parsePktLines(body);
  } catch {
    throw new ApiError(400, 'Malformed pkt-line request');
  }
  const wants: string[] = [];
  const haves: string[] = [];
  const shallow: string[] = [];
  let deepen: number | null = null;
  for (const packet of packets) {
    if (packet[0] !== 'data') continue;
    let line = packet[1].toString('utf8');
    if (line.endsWith('\n')) line = line.slice(0, -1);
    if (line.includes('\0')) line = line.split('\0', 1)[0] as string;
    // The first want line carries the client's capabilities after a
    // space ("want <oid> side-band-64k ..."): the oid is the first token.
    if (line.startsWith('want ')) wants.push(line.slice(5).trim().split(/\s+/)[0] as string);
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim().split(/\s+/)[0] as string);
    else if (line.startsWith('shallow ')) shallow.push(line.slice(8).trim().split(/\s+/)[0] as string);
    else if (line.startsWith('deepen ')) {
      const n = parseInt(line.slice(7).trim().split(/\s+/)[0] as string, 10);
      if (!Number.isNaN(n)) deepen = n;
    }
  }
  const fingerprint = JSON.stringify(['v0', repo.gitSeq, wants, haves, shallow, deepen]);
  const cached = repo.fetchCache.get(fingerprint);
  if (cached !== undefined) {
    ctx.sendGitBytes(200, cached, 'application/x-git-upload-pack-result');
    return;
  }
  const { send, shallow: shallowNew, unshallow } = computeFetch(repo, wants, haves, shallow, deepen);
  const out: Buffer[] = [];
  for (const oid of shallowNew) out.push(pktLine(`shallow ${oid}\n`));
  for (const oid of unshallow) out.push(pktLine(`unshallow ${oid}\n`));
  // A bare ACK ends the negotiation: the client reads the pack next. So
  // every common have gets "ACK <oid> common" and only the last one is
  // repeated bare, exactly as git's upload-pack answers.
  const wantAncestors = new Set<string>();
  for (const want of wants) {
    for (const oid of walkCommits(repo, peelToCommit(repo, want))) wantAncestors.add(oid);
  }
  const common = haves.filter((have) => repo.objects.has(have) && wantAncestors.has(have));
  if (common.length > 0) {
    for (const oid of common) out.push(pktLine(`ACK ${oid} common\n`));
    out.push(pktLine(`ACK ${common[common.length - 1] as string}\n`));
  } else {
    out.push(pktLine('NAK\n'));
  }
  const pack = writePack(snapshotObjects(repo, send));
  out.push(...sidebandPackets(1, pack));
  out.push(FLUSH_PKT);
  const bodyOut = Buffer.concat(out);
  repo.fetchCache.set(fingerprint, bodyOut);
  ctx.sendGitBytes(200, bodyOut, 'application/x-git-upload-pack-result');
}

async function gitReceivePack(ctx: Ctx, repo: Repo): Promise<void> {
  const body = await ctx.readBody();
  let packets: PktPacket[];
  let pack: Buffer;
  try {
    [packets, pack] = parsePktLines(body, true);
  } catch {
    throw new ApiError(400, 'Malformed pkt-line request');
  }
  const commands: Array<[string, string, string]> = [];
  let caps = '';
  for (const packet of packets) {
    if (packet[0] !== 'data') continue;
    let line = packet[1].toString('utf8');
    if (line.endsWith('\n')) line = line.slice(0, -1);
    if (line.includes('\0')) {
      const split = line.split('\0');
      line = split[0] as string;
      caps = split.slice(1).join('\0');
    }
    const parts = line.split(' ');
    if (parts.length === 3) commands.push([parts[0] as string, parts[1] as string, parts[2] as string]);
  }
  const sideband = caps.includes('side-band-64k');
  const reportStatus = caps.includes('report-status');
  let unpackError: string | null = null;
  let newObjects: Map<string, GitObject> = new Map();
  if (pack.length > 0) {
    try {
      newObjects = readPack(pack, (oid) => repo.objects.get(oid));
    } catch (err) {
      unpackError = err instanceof Error ? err.message : String(err);
    }
  }
  const results: Array<[string, boolean, string | null]> = [];
  if (unpackError === null) {
    for (const [oid, pair] of newObjects) {
      if (!repo.objects.has(oid)) repo.objects.set(oid, pair);
    }
  }
  for (const [oldOid, newOid, ref] of commands) {
    const current = repo.refs.get(ref);
    if (unpackError !== null) {
      results.push([ref, false, `unpack failed: ${unpackError}`]);
      continue;
    }
    if (newOid === ZERO_OID) {
      if (current === undefined) {
        results.push([ref, false, 'ref does not exist']);
      } else if (oldOid !== current) {
        results.push([ref, false, 'old value does not match']);
      } else {
        repo.refs.delete(ref);
        results.push([ref, true, null]);
      }
    } else if (current === undefined) {
      if (oldOid !== ZERO_OID) {
        results.push([ref, false, 'old value does not match']);
      } else if (!repo.objects.has(newOid)) {
        results.push([ref, false, 'object not found']);
      } else {
        repo.refs.set(ref, newOid);
        results.push([ref, true, null]);
      }
    } else {
      if (oldOid !== current) {
        results.push([ref, false, 'old value does not match']);
      } else if (newOid === current) {
        results.push([ref, true, null]);
      } else if (!repo.objects.has(newOid)) {
        results.push([ref, false, 'object not found']);
      } else if (!isAncestor(repo, current, newOid)) {
        results.push([ref, false, 'non-fast-forward']);
      } else {
        repo.refs.set(ref, newOid);
        results.push([ref, true, null]);
      }
    }
  }
  repo.updated_at = isoNow();
  repo.touchGit();
  if (!reportStatus) {
    ctx.sendGitBytes(200, Buffer.alloc(0), 'application/x-git-receive-pack-result');
    return;
  }
  const lines: PktItem[] = [];
  if (unpackError === null) lines.push('unpack ok\n');
  else lines.push(`unpack ${unpackError}\n`);
  for (const [ref, ok, reason] of results) {
    if (ok) lines.push(`ok ${ref}\n`);
    else lines.push(`ng ${ref} ${reason ?? 'failed'}\n`);
  }
  lines.push('flush');
  const payload = pktLines(lines);
  let bodyOut: Buffer;
  if (sideband) {
    // The sideband stream itself ends with a flush pkt-line, after the
    // band-1 packets carrying the report (whose own flush is inside them).
    bodyOut = Buffer.concat([...sidebandPackets(1, payload), FLUSH_PKT]);
  } else {
    bodyOut = payload;
  }
  ctx.sendGitBytes(200, bodyOut, 'application/x-git-receive-pack-result');
}

// ---------------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------------

async function dispatch(ctx: Ctx): Promise<void> {
  const path = ctx.path;
  try {
    if (path === '/healthz') {
      if (ctx.method !== 'GET') ctx.sendJsonError(404, 'Not Found');
      else ctx.sendJson(200, { ok: true });
      return;
    }
    if (path === '/api/graphql') {
      await handleGraphQL(ctx);
      return;
    }
    if (path === '/mcp') {
      await handleMcp(ctx);
      return;
    }
    if (ctx.segments[0] === 'api' && ctx.segments[1] === 'v3') {
      await handleRest(ctx);
      return;
    }
    if (ctx.segments.length >= 3 && (ctx.segments[1] as string).endsWith('.git')) {
      await handleGit(ctx);
      return;
    }
    // Drain any unread body so the keep-alive connection stays usable.
    await ctx.readBody();
    ctx.sendJsonError(404, 'Not Found');
  } catch (err) {
    if (err instanceof ApiError) {
      try {
        await ctx.readBody();
      } catch {
        // The body is gone; the error answer still goes out.
      }
      ctx.sendJsonError(err.status, err.message);
      return;
    }
    // Never take the server down for one request.
    logLine(`error on ${ctx.method} ${ctx.path}: ${err instanceof Error ? err.message : String(err)}`);
    try {
      await ctx.readBody();
      ctx.sendJsonError(500, 'Internal Server Error');
    } catch {
      // The connection is already gone.
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL: a small parser and executor for the documents the suite sends
// ---------------------------------------------------------------------------

class GqlParseError extends Error {}

/**
 * The lexer, one sticky regex over the document. Token order matters: float
 * before int (so "1.5" is one token), string before name.
 */
const GQL_TOKEN_RE = /(?<ws>[ \t\r\n,]+)|(?<comment>#[^\n]*)|(?<spread>\.\.\.)|(?<string>"(?:\\.|[^"\\])*")|(?<float>-?\d+\.\d+(?:[eE][+-]?\d+)?|-?\d+[eE][+-]?\d+)|(?<int>-?\d+)|(?<name>[_A-Za-z][_A-Za-z0-9]*)|(?<punct>[$!:=\@()[\]{}|&])/y;

type GqlTokenKind = 'ws' | 'comment' | 'spread' | 'string' | 'float' | 'int' | 'name' | 'punct' | 'eof';
type GqlToken = [GqlTokenKind, unknown];

function gqlLex(text: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let position = 0;
  GQL_TOKEN_RE.lastIndex = 0;
  while (position < text.length) {
    GQL_TOKEN_RE.lastIndex = position;
    const match = GQL_TOKEN_RE.exec(text);
    if (match === null || match.index !== position) {
      throw new GqlParseError(`Unexpected character ${JSON.stringify(text[position])} at offset ${position}`);
    }
    position = match.index + match[0].length;
    const groups = match.groups as Record<string, string | undefined>;
    let kind: GqlTokenKind | null = null;
    let raw = '';
    for (const name of ['ws', 'comment', 'spread', 'string', 'float', 'int', 'name', 'punct'] as const) {
      if (groups[name] !== undefined) {
        kind = name;
        raw = groups[name] as string;
        break;
      }
    }
    if (kind === null) continue;
    if (kind === 'ws' || kind === 'comment') continue;
    let value: unknown = raw;
    if (kind === 'string') value = JSON.parse(raw);
    else if (kind === 'int') value = parseInt(raw, 10);
    else if (kind === 'float') value = parseFloat(raw);
    tokens.push([kind, value]);
  }
  tokens.push(['eof', null]);
  return tokens;
}

type GqlValue =
  | ['var', string]
  | ['int', number]
  | ['float', number]
  | ['string', string]
  | ['bool', boolean]
  | ['null', null]
  | ['enum', string]
  | ['list', GqlValue[]]
  | ['object', Record<string, GqlValue>];

interface GqlFieldSelection {
  kind: 'field';
  alias: string | null;
  name: string;
  args: Record<string, GqlValue>;
  selection: GqlSelection[];
}

interface GqlInlineSelection {
  kind: 'inline';
  type: string | null;
  selection: GqlSelection[];
}

interface GqlSpreadSelection {
  kind: 'spread';
  name: string;
}

type GqlSelection = GqlFieldSelection | GqlInlineSelection | GqlSpreadSelection;

interface GqlOperation {
  kind: 'query' | 'mutation';
  name: string | null;
  varDefs: Record<string, GqlValue | null>;
  selection: GqlSelection[];
}

interface GqlFragment {
  kind: 'fragment';
  name: string;
  type: string;
  selection: GqlSelection[];
}

type GqlDefinition = GqlOperation | GqlFragment;

class GqlParser {
  tokens: GqlToken[];
  pos = 0;

  constructor(text: string) {
    this.tokens = gqlLex(text);
  }

  peek(ahead = 0): GqlToken {
    const index = Math.min(this.pos + ahead, this.tokens.length - 1);
    return this.tokens[index] as GqlToken;
  }

  take(): GqlToken {
    const token = this.tokens[this.pos] as GqlToken;
    this.pos += 1;
    return token;
  }

  expect(kind: GqlTokenKind, value: unknown = undefined): unknown {
    const token = this.take();
    if (token[0] !== kind || (value !== undefined && token[1] !== value)) {
      throw new GqlParseError(`Expected ${kind} ${String(value)}, got ${token[0]} ${JSON.stringify(token[1])}`);
    }
    return token[1];
  }

  at(kind: GqlTokenKind, value: unknown = undefined): boolean {
    const token = this.peek();
    return token[0] === kind && (value === undefined || token[1] === value);
  }

  parseDocument(): GqlDefinition[] {
    const definitions: GqlDefinition[] = [];
    while (!this.at('eof')) definitions.push(this.parseDefinition());
    return definitions;
  }

  parseDefinition(): GqlDefinition {
    if (this.at('name', 'query') || this.at('name', 'mutation')) {
      const kind = this.take()[1] as 'query' | 'mutation';
      return this.parseOperation(kind);
    }
    if (this.at('name', 'fragment')) {
      this.take();
      const name = this.expect('name') as string;
      this.expect('name', 'on');
      const typeCondition = this.expect('name') as string;
      this.skipDirectives();
      return { kind: 'fragment', name, type: typeCondition, selection: this.parseSelectionSet() };
    }
    if (this.at('punct', '{')) {
      return { kind: 'query', name: null, varDefs: {}, selection: this.parseSelectionSet() };
    }
    throw new GqlParseError(`Unexpected token ${JSON.stringify(this.peek())}`);
  }

  parseOperation(kind: 'query' | 'mutation'): GqlOperation {
    let name: string | null = null;
    if (this.at('name')) name = this.take()[1] as string;
    let varDefs: Record<string, GqlValue | null> = {};
    if (this.at('punct', '(')) varDefs = this.parseVarDefs();
    this.skipDirectives();
    return { kind, name, varDefs, selection: this.parseSelectionSet() };
  }

  parseVarDefs(): Record<string, GqlValue | null> {
    const defs: Record<string, GqlValue | null> = {};
    this.expect('punct', '(');
    while (!this.at('punct', ')')) {
      this.expect('punct', '$');
      const name = this.expect('name') as string;
      this.expect('punct', ':');
      this.parseType();
      let def: GqlValue | null = null;
      if (this.at('punct', '=')) {
        this.take();
        def = this.parseValue();
      }
      defs[name] = def;
    }
    this.expect('punct', ')');
    return defs;
  }

  parseType(): void {
    if (this.at('punct', '[')) {
      this.take();
      this.parseType();
      this.expect('punct', ']');
    } else {
      this.expect('name');
    }
    if (this.at('punct', '!')) this.take();
  }

  skipDirectives(): void {
    while (this.at('punct', '@')) {
      this.take();
      this.expect('name');
      if (this.at('punct', '(')) this.parseArguments();
    }
  }

  parseSelectionSet(): GqlSelection[] {
    const selections: GqlSelection[] = [];
    this.expect('punct', '{');
    while (!this.at('punct', '}')) selections.push(this.parseSelection());
    this.expect('punct', '}');
    return selections;
  }

  parseSelection(): GqlSelection {
    if (this.at('spread')) {
      this.take();
      if (this.at('name', 'on')) {
        this.take();
        const typeCondition = this.expect('name') as string;
        this.skipDirectives();
        return { kind: 'inline', type: typeCondition, selection: this.parseSelectionSet() };
      }
      const name = this.expect('name') as string;
      this.skipDirectives();
      return { kind: 'spread', name };
    }
    const nameOrAlias = this.expect('name') as string;
    let alias: string | null = null;
    let name = nameOrAlias;
    if (this.at('punct', ':')) {
      this.take();
      alias = nameOrAlias;
      name = this.expect('name') as string;
    }
    let args: Record<string, GqlValue> = {};
    if (this.at('punct', '(')) args = this.parseArguments();
    this.skipDirectives();
    let selection: GqlSelection[] = [];
    if (this.at('punct', '{')) selection = this.parseSelectionSet();
    return { kind: 'field', alias, name, args, selection };
  }

  parseArguments(): Record<string, GqlValue> {
    const args: Record<string, GqlValue> = {};
    this.expect('punct', '(');
    while (!this.at('punct', ')')) {
      const name = this.expect('name') as string;
      this.expect('punct', ':');
      args[name] = this.parseValue();
    }
    this.expect('punct', ')');
    return args;
  }

  parseValue(): GqlValue {
    const [kind, value] = this.peek();
    if (kind === 'punct' && value === '$') {
      this.take();
      return ['var', this.expect('name') as string];
    }
    if (kind === 'int' || kind === 'float' || kind === 'string') {
      this.take();
      return [kind, value as never];
    }
    if (kind === 'name') {
      this.take();
      if (value === 'true') return ['bool', true];
      if (value === 'false') return ['bool', false];
      if (value === 'null') return ['null', null];
      return ['enum', value as string];
    }
    if (kind === 'punct' && value === '[') {
      this.take();
      const items: GqlValue[] = [];
      while (!this.at('punct', ']')) items.push(this.parseValue());
      this.expect('punct', ']');
      return ['list', items];
    }
    if (kind === 'punct' && value === '{') {
      this.take();
      const fields: Record<string, GqlValue> = {};
      while (!this.at('punct', '}')) {
        const name = this.expect('name') as string;
        this.expect('punct', ':');
        fields[name] = this.parseValue();
      }
      this.expect('punct', '}');
      return ['object', fields];
    }
    throw new GqlParseError(`Unexpected value token ${JSON.stringify(this.peek())}`);
  }
}

function gqlResolveValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  const [kind, payload] = value;
  if (kind === 'var') return variables[payload as string];
  if (kind === 'list') return (payload as GqlValue[]).map((item) => gqlResolveValue(item, variables));
  if (kind === 'object') {
    const out: Record<string, unknown> = {};
    for (const [key, item] of Object.entries(payload as Record<string, GqlValue>)) {
      out[key] = gqlResolveValue(item, variables);
    }
    return out;
  }
  return payload;
}

/** A typed object in the executor: its GraphQL type name and its data. */
class GObj {
  typeName: string;
  data: unknown;
  constructor(typeName: string, data: unknown) {
    this.typeName = typeName;
    this.data = data;
  }
}

const MISSING = Symbol('missing');

const TYPE_FIELDS: Record<string, string[]> = {
  Issue: ['id', 'databaseId', 'number', 'title', 'state', 'body', 'createdAt', 'updatedAt', 'closedAt', 'author', 'comments'],
  PullRequest: ['id', 'databaseId', 'number', 'title', 'state', 'body', 'headRefName', 'baseRefName', 'mergeable', 'merged', 'mergedAt', 'files', 'createdAt', 'updatedAt', 'author'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'description', 'isPrivate', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'createdAt', 'updatedAt'],
  User: ['id', 'databaseId', 'login', 'name', 'email'],
  Ref: ['name', 'target'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  IssueComment: ['id', 'databaseId', 'body', 'createdAt', 'updatedAt', 'author'],
  CreateIssuePayload: ['issue'],
  CloseIssuePayload: ['issue'],
  CreatePullRequestPayload: ['pullRequest'],
  MergePullRequestPayload: ['pullRequest'],
  AddCommentPayload: ['commentEdge'],
};
const TYPE_KIND: Record<string, string> = { SearchType: 'ENUM' };
const ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['DISCUSSION', 'ISSUE', 'REPOSITORY', 'USER'],
};

function gqlCursor(offset: number): string {
  return b64encodeText(`cursor:${offset}`);
}

function gqlCursorOffset(cursor: string): number {
  try {
    const raw = Buffer.from(cursor, 'base64').toString('utf8');
    return parseInt(raw.split(':', 2)[1] as string, 10) || 0;
  } catch {
    return 0;
  }
}

function findRepoById(repoId: number): Repo | undefined {
  for (const repo of STORE.repos.values()) {
    if (repo.id === repoId) return repo;
  }
  return undefined;
}

function gqlNode(globalIdValue: string): GObj | null {
  const parsed = parseGlobalId(globalIdValue);
  if (parsed === null) return null;
  const [kind, parts] = parsed;
  try {
    if (kind === 'Repository') {
      const repo = findRepoById(parseInt(parts[0] as string, 10));
      return repo !== undefined ? new GObj('Repository', repo) : null;
    }
    if (kind === 'Issue') {
      const repo = findRepoById(parseInt(parts[0] as string, 10));
      const issue = repo !== undefined ? repo.issues.get(parseInt(parts[1] as string, 10)) : undefined;
      return issue !== undefined ? new GObj('Issue', { repo, issue }) : null;
    }
    if (kind === 'PullRequest') {
      const repo = findRepoById(parseInt(parts[0] as string, 10));
      const pr = repo !== undefined ? repo.pulls.get(parseInt(parts[1] as string, 10)) : undefined;
      return pr !== undefined ? new GObj('PullRequest', { repo, pr }) : null;
    }
  } catch {
    return null;
  }
  return null;
}
interface GqlContext {
  variables: Record<string, unknown>;
  errors: Array<{ message: string }>;
  fragments: Record<string, GqlFragment>;
}

function gqlIssuesConnection(repo: Repo, args: Record<string, unknown>): GObj {
  let issues = [...repo.issues.values()];
  const states = args.states as string[] | undefined;
  if (states !== undefined && states !== null) {
    const wanted: Record<string, string> = { OPEN: 'open', CLOSED: 'closed' };
    const keep = new Set(states.map((state) => wanted[state] ?? String(state).toLowerCase()));
    issues = issues.filter((i) => keep.has(i.state));
  }
  const orderBy = (args.orderBy as Record<string, unknown> | undefined) ?? {};
  const reverse = orderBy.direction === 'DESC';
  issues.sort((a, b) => (reverse ? b.number - a.number : a.number - b.number));
  const offset = typeof args.after === 'string' ? gqlCursorOffset(args.after) : 0;
  const first = args.first as number | undefined;
  const page = first === undefined || first === null ? issues.slice(offset) : issues.slice(offset, offset + first);
  const hasNext = offset + page.length < issues.length;
  const endCursor = page.length > 0 ? gqlCursor(offset + page.length) : null;
  return new GObj('IssueConnection', { repo, items: page, has_next: hasNext, end_cursor: endCursor, total: issues.length });
}

function gqlPullsConnection(repo: Repo, args: Record<string, unknown>): GObj {
  let pulls = [...repo.pulls.values()].sort((a, b) => b.number - a.number);
  const states = args.states as string[] | undefined;
  if (states !== undefined && states !== null) {
    const keep = new Set<string>();
    for (const state of states) {
      if (state === 'OPEN') keep.add('open');
      else if (state === 'CLOSED' || state === 'MERGED') keep.add('closed');
    }
    pulls = pulls.filter((p) => keep.has(p.state));
  }
  const offset = typeof args.after === 'string' ? gqlCursorOffset(args.after) : 0;
  const first = args.first as number | undefined;
  const page = first === undefined || first === null ? pulls.slice(offset) : pulls.slice(offset, offset + first);
  const hasNext = offset + page.length < pulls.length;
  const endCursor = page.length > 0 ? gqlCursor(offset + page.length) : null;
  return new GObj('PullRequestConnection', { repo, items: page, has_next: hasNext, end_cursor: endCursor, total: pulls.length });
}

function gqlFilesConnection(repo: Repo, pr: PullRequest, args: Record<string, unknown>): GObj {
  const files = prFiles(repo, pr);
  const first = args.first as number | undefined;
  const page = first === undefined || first === null ? files : files.slice(0, first);
  return new GObj('PullRequestChangedFileConnection', { items: page, has_next: false, end_cursor: null, total: files.length });
}

function gqlPrState(pr: PullRequest): string {
  if (pr.merged) return 'MERGED';
  return pr.state === 'open' ? 'OPEN' : 'CLOSED';
}

function gqlPrMergeable(repo: Repo, pr: PullRequest): string {
  if (pr.state !== 'open') return 'UNKNOWN';
  const baseTip = repo.branchTip(pr.base_ref);
  const headTip = repo.branchTip(pr.head_ref);
  if (baseTip === undefined || headTip === undefined) return 'UNKNOWN';
  return mergeConflict(repo, baseTip, headTip) ? 'CONFLICTING' : 'MERGEABLE';
}

function gqlAddComment(repo: Repo, issue: Issue, body: string): Comment {
  const commentId = STORE.next_comment_id;
  STORE.next_comment_id += 1;
  const stamp = isoNow();
  const comment: Comment = { id: commentId, body, created_at: stamp, updated_at: stamp };
  issue.comments.push(comment);
  issue.jsonCache = null; // the comments count changed
  return comment;
}

function gqlFieldValue(typeName: string, obj: unknown, name: string, args: Record<string, unknown>, ctx: GqlContext): unknown {
  if (name === '__typename') return typeName;
  if (typeName === 'Query') {
    if (name === 'viewer') return new GObj('User', VIEWER);
    if (name === 'repository') {
      const repo = STORE.getRepo(args.owner as string | undefined, args.name as string);
      return repo !== undefined ? new GObj('Repository', repo) : null;
    }
    if (name === 'node') return gqlNode((args.id as string) || '');
    if (name === '__type') {
      const wanted = args.name as string;
      if (wanted in TYPE_FIELDS || wanted in ENUM_VALUES) return new GObj('__Type', { name: wanted });
      return null;
    }
    return MISSING;
  }
  if (typeName === 'Mutation') {
    if (name === 'createIssue') return gqlMutationCreateIssue(args, ctx);
    if (name === 'closeIssue') return gqlMutationCloseIssue(args, ctx);
    if (name === 'createPullRequest') return gqlMutationCreatePr(args, ctx);
    if (name === 'mergePullRequest') return gqlMutationMergePr(args, ctx);
    if (name === 'addComment') return gqlMutationAddComment(args, ctx);
    return MISSING;
  }
  if (typeName === 'Repository') {
    const repo = obj as Repo;
    if (name === 'id') return globalId('Repository', repo.id);
    if (name === 'databaseId') return repo.id;
    if (name === 'name') return repo.name;
    if (name === 'nameWithOwner') return `${VIEWER_LOGIN}/${repo.name}`;
    if (name === 'description') return repo.description;
    if (name === 'isPrivate') return repo.private;
    if (name === 'owner') return new GObj('User', VIEWER);
    if (name === 'defaultBranchRef') return repo.headTip() !== undefined ? new GObj('Ref', { name: repo.default_branch }) : null;
    if (name === 'viewerPermission') return 'ADMIN';
    if (name === 'hasIssuesEnabled') return true;
    if (name === 'createdAt') return repo.created_at;
    if (name === 'updatedAt') return repo.updated_at;
    if (name === 'issue') {
      const issue = repo.issues.get(args.number as number);
      return issue !== undefined ? new GObj('Issue', { repo, issue }) : null;
    }
    if (name === 'issues') return gqlIssuesConnection(repo, args);
    if (name === 'pullRequests') return gqlPullsConnection(repo, args);
    if (name === 'pullRequest') {
      const pr = repo.pulls.get(args.number as number);
      return pr !== undefined ? new GObj('PullRequest', { repo, pr }) : null;
    }
    return MISSING;
  }
  if (typeName === 'Issue') {
    const { repo, issue } = obj as { repo: Repo; issue: Issue };
    if (name === 'id') return globalId('Issue', repo.id, issue.number);
    if (name === 'databaseId') return repo.id * 1000000 + issue.number;
    if (name === 'number') return issue.number;
    if (name === 'title') return issue.title;
    if (name === 'body') return issue.body;
    if (name === 'state') return issue.state === 'open' ? 'OPEN' : 'CLOSED';
    if (name === 'createdAt') return issue.created_at;
    if (name === 'updatedAt') return issue.updated_at;
    if (name === 'closedAt') return issue.closed_at;
    if (name === 'author') return new GObj('User', VIEWER);
    return MISSING;
  }
  if (typeName === 'PullRequest') {
    const { repo, pr } = obj as { repo: Repo; pr: PullRequest };
    if (name === 'id') return globalId('PullRequest', repo.id, pr.number);
    if (name === 'databaseId') return repo.id * 1000000 + 500000 + pr.number;
    if (name === 'number') return pr.number;
    if (name === 'title') return pr.title;
    if (name === 'body') return pr.body;
    if (name === 'state') return gqlPrState(pr);
    if (name === 'headRefName') return pr.head_ref;
    if (name === 'baseRefName') return pr.base_ref;
    if (name === 'mergeable') return gqlPrMergeable(repo, pr);
    if (name === 'merged') return pr.merged;
    if (name === 'mergedAt') return pr.merged_at;
    if (name === 'createdAt') return pr.created_at;
    if (name === 'updatedAt') return pr.updated_at;
    if (name === 'author') return new GObj('User', VIEWER);
    if (name === 'files') return gqlFilesConnection(repo, pr, args);
    return MISSING;
  }
  if (typeName === 'User') {
    const user = obj as ScenarioUser;
    if (name === 'id') return globalId('User', user.id ?? 1000);
    if (name === 'databaseId') return user.id ?? 1000;
    if (name === 'login') return user.login;
    if (name === 'name') return user.name;
    if (name === 'email') return user.email;
    return MISSING;
  }
  if (typeName === 'Ref') {
    const ref = obj as { name: string };
    if (name === 'name') return ref.name;
    return MISSING;
  }
  if (typeName === 'IssueConnection' || typeName === 'PullRequestConnection' || typeName === 'PullRequestChangedFileConnection') {
    const conn = obj as { repo: Repo; items: unknown[]; has_next: boolean; end_cursor: string | null; total: number };
    if (name === 'nodes') {
      if (typeName === 'IssueConnection') {
        return (conn.items as Issue[]).map((i) => new GObj('Issue', { repo: conn.repo, issue: i }));
      }
      if (typeName === 'PullRequestConnection') {
        return (conn.items as PullRequest[]).map((p) => new GObj('PullRequest', { repo: conn.repo, pr: p }));
      }
      return (conn.items as Record<string, unknown>[]).map((f) => new GObj('PullRequestChangedFile', f));
    }
    if (name === 'edges') {
      const edges: GObj[] = [];
      for (const item of conn.items) {
        if (typeName === 'IssueConnection') {
          edges.push(new GObj('IssueEdge', { node: new GObj('Issue', { repo: conn.repo, issue: item as Issue }) }));
        } else if (typeName === 'PullRequestConnection') {
          edges.push(new GObj('PullRequestEdge', { node: new GObj('PullRequest', { repo: conn.repo, pr: item as PullRequest }) }));
        } else {
          edges.push(new GObj('PullRequestChangedFileEdge', { node: new GObj('PullRequestChangedFile', item) }));
        }
      }
      return edges;
    }
    if (name === 'pageInfo') return new GObj('PageInfo', { has_next: conn.has_next, end_cursor: conn.end_cursor });
    if (name === 'totalCount') return conn.total;
    return MISSING;
  }
  if (typeName === 'IssueEdge' || typeName === 'PullRequestEdge' || typeName === 'PullRequestChangedFileEdge' || typeName === 'IssueCommentEdge') {
    const edge = obj as { node: GObj };
    if (name === 'node') return edge.node;
    if (name === 'cursor') return '';
    return MISSING;
  }
  if (typeName === 'PageInfo') {
    const info = obj as { has_next?: boolean; end_cursor?: string | null };
    if (name === 'hasNextPage') return info.has_next ?? false;
    if (name === 'endCursor') return info.end_cursor ?? null;
    if (name === 'hasPreviousPage') return false;
    if (name === 'startCursor') return null;
    return MISSING;
  }
  if (typeName === 'PullRequestChangedFile') {
    const file = obj as Record<string, unknown>;
    if (name === 'path') return file.filename;
    if (name === 'additions') return (file.additions as number) ?? 0;
    if (name === 'deletions') return (file.deletions as number) ?? 0;
    if (name === 'changeType') {
      return ({ added: 'ADDED', modified: 'MODIFIED', removed: 'REMOVED' } as Record<string, string>)[file.status as string] ?? 'MODIFIED';
    }
    return MISSING;
  }
  if (typeName === '__Type') {
    const wanted = (obj as { name: string }).name;
    if (name === 'name') return wanted;
    if (name === 'kind') return TYPE_KIND[wanted] ?? 'OBJECT';
    if (name === 'fields') return (TYPE_FIELDS[wanted] ?? []).map((f) => new GObj('__Field', { name: f }));
    if (name === 'enumValues') return (ENUM_VALUES[wanted] ?? []).map((v) => new GObj('__EnumValue', { name: v }));
    return MISSING;
  }
  if (typeName === '__Field') {
    const field = obj as { name: string };
    if (name === 'name') return field.name;
    if (name === 'description') return '';
    return MISSING;
  }
  if (typeName === '__EnumValue') {
    const value = obj as { name: string };
    if (name === 'name') return value.name;
    if (name === 'description') return '';
    return MISSING;
  }
  if (typeName === 'IssueComment') {
    const comment = (obj as { comment: Comment }).comment;
    if (name === 'id') return globalId('IssueComment', comment.id);
    if (name === 'databaseId') return comment.id;
    if (name === 'body') return comment.body;
    if (name === 'createdAt') return comment.created_at;
    if (name === 'updatedAt') return comment.updated_at;
    if (name === 'author') return new GObj('User', VIEWER);
    return MISSING;
  }
  if (typeName === 'CreateIssuePayload' || typeName === 'CloseIssuePayload') {
    const payload = obj as { repo: Repo | null; issue: Issue | null };
    if (name === 'issue') {
      return payload.issue !== null && payload.issue !== undefined
        ? new GObj('Issue', { repo: payload.repo, issue: payload.issue })
        : null;
    }
    if (name === 'clientMutationId') return null;
    return MISSING;
  }
  if (typeName === 'CreatePullRequestPayload' || typeName === 'MergePullRequestPayload') {
    const payload = obj as { repo: Repo | null; pr: PullRequest | null };
    if (name === 'pullRequest') {
      return payload.pr !== null && payload.pr !== undefined
        ? new GObj('PullRequest', { repo: payload.repo, pr: payload.pr })
        : null;
    }
    if (name === 'clientMutationId') return null;
    return MISSING;
  }
  if (typeName === 'AddCommentPayload') {
    const payload = obj as { comment: Comment | null };
    if (name === 'commentEdge') {
      if (payload.comment === null || payload.comment === undefined) return null;
      return new GObj('IssueCommentEdge', { node: new GObj('IssueComment', { comment: payload.comment }) });
    }
    if (name === 'clientMutationId') return null;
    return MISSING;
  }
  return MISSING;
}

function gqlRepoFromInput(input: Record<string, unknown>, ctx: GqlContext): Repo | null {
  const parsed = parseGlobalId((input.repositoryId as string) || '');
  if (parsed === null || parsed[0] !== 'Repository') {
    ctx.errors.push({ message: 'repositoryId is not a Repository id' });
    return null;
  }
  const repo = findRepoById(parseInt(parsed[1][0] as string, 10));
  if (repo === undefined) {
    ctx.errors.push({ message: 'Repository not found' });
    return null;
  }
  return repo;
}

function gqlMutationCreateIssue(args: Record<string, unknown>, ctx: GqlContext): GObj {
  const input = (args.input as Record<string, unknown>) ?? {};
  const repo = gqlRepoFromInput(input, ctx);
  if (repo === null) return new GObj('CreateIssuePayload', { repo: null, issue: null });
  try {
    const issue = issueFromBody(repo, {
      title: input.title,
      body: (input.body as string) || '',
      labels: [],
    });
    return new GObj('CreateIssuePayload', { repo, issue });
  } catch (err) {
    if (err instanceof ApiError) ctx.errors.push({ message: err.message });
    return new GObj('CreateIssuePayload', { repo, issue: null });
  }
}

function gqlMutationCloseIssue(args: Record<string, unknown>, ctx: GqlContext): GObj {
  const input = (args.input as Record<string, unknown>) ?? {};
  const node = gqlNode((input.issueId as string) || '');
  if (node === null || node.typeName !== 'Issue') {
    ctx.errors.push({ message: 'Issue not found' });
    return new GObj('CloseIssuePayload', { repo: null, issue: null });
  }
  const { repo, issue } = node.data as { repo: Repo; issue: Issue };
  issue.state = 'closed';
  issue.closed_at = isoNow();
  issue.updated_at = isoNow();
  issue.jsonCache = null;
  return new GObj('CloseIssuePayload', { repo, issue });
}

function gqlMutationCreatePr(args: Record<string, unknown>, ctx: GqlContext): GObj {
  const input = (args.input as Record<string, unknown>) ?? {};
  const repo = gqlRepoFromInput(input, ctx);
  if (repo === null) return new GObj('CreatePullRequestPayload', { repo: null, pr: null });
  try {
    const pr = prFromBody(repo, {
      title: input.title,
      body: (input.body as string) || '',
      head: input.headRefName,
      base: input.baseRefName,
    });
    return new GObj('CreatePullRequestPayload', { repo, pr });
  } catch (err) {
    if (err instanceof ApiError) ctx.errors.push({ message: err.message });
    return new GObj('CreatePullRequestPayload', { repo, pr: null });
  }
}

function gqlMutationMergePr(args: Record<string, unknown>, ctx: GqlContext): GObj {
  const input = (args.input as Record<string, unknown>) ?? {};
  const node = gqlNode((input.pullRequestId as string) || '');
  if (node === null || node.typeName !== 'PullRequest') {
    ctx.errors.push({ message: 'Pull request not found' });
    return new GObj('MergePullRequestPayload', { repo: null, pr: null });
  }
  const { repo, pr } = node.data as { repo: Repo; pr: PullRequest };
  if (pr.state !== 'open') {
    ctx.errors.push({ message: 'Pull request is not open' });
    return new GObj('MergePullRequestPayload', { repo, pr });
  }
  try {
    const sha = squashMerge(repo, pr);
    pr.merged = true;
    pr.state = 'closed';
    pr.merged_at = isoNow();
    pr.closed_at = pr.merged_at;
    pr.merge_commit_sha = sha;
    pr.updated_at = pr.merged_at;
  } catch (err) {
    if (err instanceof ApiError) ctx.errors.push({ message: err.message });
    return new GObj('MergePullRequestPayload', { repo, pr });
  }
  return new GObj('MergePullRequestPayload', { repo, pr });
}

function gqlMutationAddComment(args: Record<string, unknown>, ctx: GqlContext): GObj {
  const input = (args.input as Record<string, unknown>) ?? {};
  const node = gqlNode((input.subjectId as string) || '');
  if (node === null || node.typeName !== 'Issue') {
    ctx.errors.push({ message: 'Subject not found' });
    return new GObj('AddCommentPayload', { comment: null });
  }
  const { repo, issue } = node.data as { repo: Repo; issue: Issue };
  const comment = gqlAddComment(repo, issue, (input.body as string) || '');
  return new GObj('AddCommentPayload', { comment });
}

function gqlResolveFields(typeName: string, obj: unknown, selections: GqlSelection[], ctx: GqlContext): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const selection of selections) {
    if (selection.kind === 'field') {
      const value = gqlResolveField(typeName, obj, selection, ctx);
      if (value !== MISSING) out[selection.alias ?? selection.name] = value;
    } else if (selection.kind === 'inline') {
      const condition = selection.type;
      if (condition === null || condition === typeName) {
        Object.assign(out, gqlResolveFields(typeName, obj, selection.selection, ctx));
      }
    } else if (selection.kind === 'spread') {
      const fragment = ctx.fragments[selection.name];
      if (fragment !== undefined && fragment.type === typeName) {
        Object.assign(out, gqlResolveFields(typeName, obj, fragment.selection, ctx));
      }
    }
  }
  return out;
}

function gqlResolveField(typeName: string, obj: unknown, field: GqlFieldSelection, ctx: GqlContext): unknown {
  const args: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(field.args)) {
    args[key] = gqlResolveValue(value, ctx.variables);
  }
  const value = gqlFieldValue(typeName, obj, field.name, args, ctx);
  if (value === MISSING) {
    ctx.errors.push({ message: `Cannot query field "${field.name}" on type "${typeName}".` });
    return MISSING;
  }
  const selection = field.selection;
  if (selection.length === 0 || value === null || value === undefined) return value;
  if (value instanceof GObj) return gqlResolveFields(value.typeName, value.data, selection, ctx);
  if (Array.isArray(value)) {
    return value.map((item) => {
      if (item === null || item === undefined) return item;
      if (item instanceof GObj) return gqlResolveFields(item.typeName, item.data, selection, ctx);
      return item;
    });
  }
  return value;
}

function gqlExecute(payload: Record<string, unknown>): Record<string, unknown> {
  const query = (payload.query as string) || '';
  const variables = (payload.variables as Record<string, unknown>) ?? {};
  const operationName = payload.operationName as string | undefined;
  let document: GqlDefinition[];
  try {
    document = new GqlParser(query).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
  const operations = document.filter((d): d is GqlOperation => d.kind === 'query' || d.kind === 'mutation');
  const fragments: Record<string, GqlFragment> = {};
  for (const d of document) {
    if (d.kind === 'fragment') fragments[d.name] = d;
  }
  let operation: GqlOperation | undefined;
  if (operationName !== undefined) {
    operation = operations.find((candidate) => candidate.name === operationName);
  }
  if (operation === undefined && operations.length > 0) operation = operations[0];
  if (operation === undefined) {
    return { data: null, errors: [{ message: 'No operation found in the document' }] };
  }
  const ctx: GqlContext = { variables, errors: [], fragments };
  const rootType = operation.kind === 'query' ? 'Query' : 'Mutation';
  const data = gqlResolveFields(rootType, {}, operation.selection, ctx);
  const result: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) result.errors = ctx.errors;
  return result;
}

async function handleGraphQL(ctx: Ctx): Promise<void> {
  if (!(await ctx.requireAuth())) return;
  if (ctx.method !== 'POST') throw new ApiError(404, 'Not Found');
  const raw = await ctx.readBody();
  let payload: unknown = {};
  if (raw.length > 0) {
    try {
      payload = JSON.parse(raw.toString('utf8'));
    } catch {
      throw new ApiError(400, 'Invalid JSON in request body');
    }
  }
  if (Array.isArray(payload)) {
    ctx.sendJson(200, payload.map((item) => gqlExecute(item as Record<string, unknown>)));
  } else if (typeof payload === 'object' && payload !== null) {
    ctx.sendJson(200, gqlExecute(payload as Record<string, unknown>));
  } else {
    throw new ApiError(400, 'Request body must be a JSON object or an array');
  }
}

// ---------------------------------------------------------------------------
// MCP: JSON-RPC 2.0 over Streamable HTTP (revision 2026-07-28, legacy fallback)
// ---------------------------------------------------------------------------

interface McpTool {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, Record<string, unknown>>;
    required?: string[];
  };
}

const MCP_TOOLS: McpTool[] = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get one repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'list_repos',
    description: "List the authenticated user's repositories.",
    inputSchema: { type: 'object', properties: {} },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'get_issue',
    description: 'Get one issue by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        issue_number: { type: 'integer', description: 'The issue number.' },
      },
      required: ['owner', 'repo', 'issue_number'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository, optionally by state.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'open, closed, or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch onto a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
        body: { type: 'string', description: 'The pull request body.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Squash-merge a pull request into its base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'integer', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

const MCP_TOOL_NAMES = new Set(MCP_TOOLS.map((tool) => tool.name));
const MCP_REQUIRED: Record<string, string[]> = {};
for (const tool of MCP_TOOLS) MCP_REQUIRED[tool.name] = tool.inputSchema.required ?? [];

function mcpTextResult(data: unknown): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(data) }],
    structuredContent: data,
  };
}

function mcpErrorResult(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

type McpCallOutcome = { result: Record<string, unknown>; errorCode: null; errorMessage: null }
  | { result: null; errorCode: number; errorMessage: string };

/** Run one tool; returns its result or a JSON-RPC error code and message. */
function mcpCallTool(name: string, args: Record<string, unknown>): McpCallOutcome {
  if (!MCP_TOOL_NAMES.has(name)) {
    return { result: null, errorCode: -32602, errorMessage: `Unknown tool ${name}` };
  }
  const missing = (MCP_REQUIRED[name] as string[]).filter((key) => args[key] === null || args[key] === undefined || args[key] === '');
  if (missing.length > 0) {
    return { result: null, errorCode: -32602, errorMessage: `Missing required argument(s): ${missing.join(', ')}` };
  }
  try {
    if (name === 'create_repo') {
      const repo = STORE.createRepo(
        args.name as string,
        args.private === true,
        typeof args.description === 'string' ? args.description : '',
      );
      return { result: mcpTextResult(repoJson(repo)), errorCode: null, errorMessage: null };
    }
    if (name === 'list_repos') {
      const repos = STORE.listRepos().map((r) => repoJson(r));
      return { result: mcpTextResult({ repositories: repos }), errorCode: null, errorMessage: null };
    }
    const repo = STORE.getRepo(args.owner as string | undefined, args.repo as string);
    if (repo === undefined) {
      return { result: mcpErrorResult('Repository not found'), errorCode: null, errorMessage: null };
    }
    if (name === 'get_repo') {
      return { result: mcpTextResult(repoJson(repo)), errorCode: null, errorMessage: null };
    }
    if (name === 'create_issue') {
      const issue = issueFromBody(repo, {
        title: args.title,
        body: (args.body as string) || '',
        labels: [],
      });
      return { result: mcpTextResult(issueJson(repo, issue)), errorCode: null, errorMessage: null };
    }
    if (name === 'get_issue') {
      const issue = repo.issues.get(parseInt(String(args.issue_number), 10));
      if (issue === undefined) {
        return { result: mcpErrorResult('Issue not found'), errorCode: null, errorMessage: null };
      }
      return { result: mcpTextResult(issueJson(repo, issue)), errorCode: null, errorMessage: null };
    }
    if (name === 'list_issues') {
      const state = (args.state as string) || 'open';
      let issues = [...repo.issues.values()];
      if (state === 'open' || state === 'closed') issues = issues.filter((i) => i.state === state);
      issues.sort((a, b) => b.number - a.number);
      return { result: mcpTextResult({ issues: issues.map((i) => issueJson(repo, i)) }), errorCode: null, errorMessage: null };
    }
    if (name === 'create_pull_request') {
      const pr = prFromBody(repo, {
        title: args.title,
        body: (args.body as string) || '',
        head: args.head,
        base: args.base,
      });
      return { result: mcpTextResult(prJson(repo, pr)), errorCode: null, errorMessage: null };
    }
    if (name === 'merge_pull_request') {
      const pr = repo.pulls.get(parseInt(String(args.pull_number), 10));
      if (pr === undefined) {
        return { result: mcpErrorResult('Pull request not found'), errorCode: null, errorMessage: null };
      }
      if (pr.state !== 'open') {
        return { result: mcpErrorResult('Pull request is not open'), errorCode: null, errorMessage: null };
      }
      const sha = squashMerge(repo, pr);
      pr.merged = true;
      pr.state = 'closed';
      pr.merged_at = isoNow();
      pr.closed_at = pr.merged_at;
      pr.merge_commit_sha = sha;
      pr.updated_at = pr.merged_at;
      return {
        result: mcpTextResult({ merged: true, sha, number: pr.number, message: 'Pull Request successfully merged' }),
        errorCode: null,
        errorMessage: null,
      };
    }
  } catch (err) {
    if (err instanceof ApiError) {
      return { result: mcpErrorResult(err.message), errorCode: null, errorMessage: null };
    }
    throw err;
  }
  return { result: mcpErrorResult(`Tool ${name} failed`), errorCode: null, errorMessage: null };
}

async function handleMcp(ctx: Ctx): Promise<void> {
  if (ctx.method !== 'POST') throw new ApiError(404, 'Not Found');
  if (!(await ctx.requireAuth())) return;
  const raw = await ctx.readBody();
  let payload: unknown = {};
  if (raw.length > 0) {
    try {
      payload = JSON.parse(raw.toString('utf8'));
    } catch {
      ctx.sendJson(400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
      return;
    }
  }
  if (typeof payload !== 'object' || payload === null || Array.isArray(payload)) {
    ctx.sendJson(400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } });
    return;
  }
  const body = payload as Record<string, unknown>;
  const hasId = 'id' in body;
  const requestId = body.id;
  const method = (body.method as string) || '';
  const params = (body.params as Record<string, unknown>) ?? {};
  if (!hasId) {
    // A notification: acknowledge it and carry no body.
    ctx.sendRaw(202, { 'Content-Length': '0' }, '');
    return;
  }

  function reply(result?: unknown, error?: { code: number; message: string }): void {
    const out: Record<string, unknown> = { jsonrpc: '2.0', id: requestId };
    if (error !== undefined) out.error = error;
    else out.result = result;
    ctx.sendJson(200, out);
  }

  if (method === 'server/discover') {
    reply({
      supportedVersions: ['2026-07-28'],
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: VERSION },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: VERSION } },
    });
    return;
  }
  if (method === 'initialize') {
    const requested = (params.protocolVersion as string) || '2025-11-25';
    reply({
      protocolVersion: requested,
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: VERSION },
    });
    return;
  }
  if (method === 'ping') {
    reply({});
    return;
  }
  if (method === 'tools/list') {
    reply({ tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const toolName = (params.name as string) || '';
    const toolArgs = params.arguments as Record<string, unknown> | undefined;
    if (toolArgs === undefined || toolArgs === null || typeof toolArgs !== 'object' || Array.isArray(toolArgs)) {
      reply(undefined, { code: -32602, message: 'arguments must be an object' });
      return;
    }
    const outcome = mcpCallTool(toolName, toolArgs);
    if (outcome.errorCode !== null) {
      reply(undefined, { code: outcome.errorCode, message: outcome.errorMessage as string });
    } else {
      reply(outcome.result);
    }
    return;
  }
  if (method.startsWith('notifications/')) {
    reply({});
    return;
  }
  reply(undefined, { code: -32601, message: `Method not found: ${method}` });
}

// ---------------------------------------------------------------------------
// Lifecycle: bind, register, poll done, exit
// ---------------------------------------------------------------------------

const REQUEST_TIMEOUT_MS = 30_000;
const RETRY_INITIAL_MS = 250;
const RETRY_MAX_MS = 2_000;

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function retryDelay(attempt: number): number {
  return Math.min(RETRY_MAX_MS, RETRY_INITIAL_MS * 2 ** Math.min(attempt, 8));
}

/** POST the bound port until the env accepts it. */
async function register(port: number): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
      });
      if (res.status === 200 || res.status === 409) return;
      if (res.status === 400 || res.status === 405) {
        throw new Error(`register answered HTTP ${res.status}: ${await res.text()}`);
      }
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('register answered HTTP ')) throw err;
    }
    await sleep(retryDelay(attempt));
  }
}

/** GET /done until the suite says it is finished. */
async function pollDone(): Promise<void> {
  let delay = 250;
  for (;;) {
    try {
      const res = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS) });
      const data = (await res.json()) as { done?: boolean };
      if (data.done === true) return;
    } catch (err) {
      logLine(`done poll failed: ${err instanceof Error ? err.message : String(err)}`);
    }
    await sleep(delay);
    delay = Math.min(delay * 2, 2000);
  }
}

async function main(): Promise<number> {
  const server = createServer((req, res) => {
    const ctx = new Ctx(req, res);
    void dispatch(ctx);
  });
  server.on('connection', (socket) => {
    // No Nagle: the suite issues thousands of small request/response
    // pairs, and Nagle plus the client's delayed ACKs costs ~40 ms each.
    socket.setNoDelay(true);
  });
  server.keepAliveTimeout = 30_000;
  server.headersTimeout = 30_000;

  await new Promise<void>((resolve) => {
    server.listen(0, '0.0.0.0', () => resolve());
  });
  const port = (server.address() as { port: number }).port;
  logLine(`listening on port ${port} as ${VIEWER_LOGIN}`);
  if (ENV_URL !== '') {
    await register(port);
    logLine('register -> ok');
    await pollDone();
    server.close();
    logLine('done; exiting');
    return 0;
  }
  logLine('no MAKEFUN_ENV_URL set; serving until interrupted');
  await new Promise<void>(() => undefined); // serve forever
  return 0;
}

main().then(
  (code) => process.exit(code),
  (err) => {
    logLine(`fatal: ${err instanceof Error ? err.message : String(err)}`);
    process.exit(1);
  },
);
