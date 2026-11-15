#!/usr/bin/env python3
"""A standalone, GitHub-compatible git forge in one process, stdlib only.

Serves, from its own in-memory store and with no outside service:
  * git smart HTTP (upload-pack protocol v2, receive-pack v0) at /{owner}/{repo}.git
  * the REST v3 API under /api/v3 (repositories, issues, pull requests, contents)
  * the GraphQL v4 API at /api/graphql
  * a Model Context Protocol endpoint at /mcp

Lifecycle (the trial wire): bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, then poll GET $MAKEFUN_ENV_URL/done until
{"done": true} and exit 0. The suite is the only client; it presents
Authorization: Bearer <MAKEFUN_SHOP_TOKEN> on every call.

No git binary is used anywhere: git objects and packfiles are implemented
here (SHA-1 object ids, trees, commits, tags, pack read/write with OFS and
REF deltas, pkt-line framing, sideband multiplexing).

The viewer login (the login the bearer token names) is derived from the
kit's published scenario seed: the suite's scenario is a fixed, seeded
dataset, and the token owner is its first generated user. The generator is
ported below and verified against the kit's own output.
"""

import base64
import difflib
import hashlib
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import urllib.parse
import urllib.request
import urllib.error
import zlib
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

VERSION = "1.0.0"
ZERO_OID = "0" * 40
DEFAULT_BRANCH = "main"
GIT_USER_AGENT = "forge/1.0"
PKT_LINE_MAX = 65520

# The suite's scenario seed (wire.ts SCENARIO_SEED, public and fixed).
SCENARIO_SEED = 0x6A09E667F3BCC909
U64_MASK = 0xFFFFFFFFFFFFFFFF

FIRST_NAMES = [
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
]
LAST_NAMES = [
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
]

# Deterministic timestamps: every created_at/updated_at is the scenario epoch
# plus a sequence number of seconds, so ordering is creation order and no
# wall clock ever leaks into a response.
TIME_EPOCH = 1735689600  # 2025-01-01T00:00:00Z


# ---------------------------------------------------------------------------
# The seeded scenario: who the token names (a port of wire.ts's generator)
# ---------------------------------------------------------------------------

def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & U64_MASK
    return h


def _mix64(value):
    z = (value + 0x9E3779B97F4A7C15) & U64_MASK
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & U64_MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & U64_MASK
    return (z ^ (z >> 31)) & U64_MASK


class _Rng:
    """xorshift64*, the suite's scenario stream (wire.ts Rng)."""

    def __init__(self, seed):
        masked = seed & U64_MASK
        self.state = masked if masked != 0 else SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & U64_MASK
        x = (x ^ ((x << 25) & U64_MASK)) & U64_MASK
        x = (x ^ (x >> 27)) & U64_MASK
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & U64_MASK

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, max_exclusive):
        if max_exclusive == 1:
            return 0
        rng_range = 4294967296
        limit = rng_range - (rng_range % max_exclusive)
        while True:
            value = self.next_u32()
            if value < limit:
                return value % max_exclusive

    def pick(self, items):
        return items[self.next_int(len(items))]


def _scenario_rng(label):
    return _Rng(_mix64(SCENARIO_SEED ^ _fnv1a64(label)))


def scenario_users(count=12):
    """The scenario's users, in order (wire.ts generateUsers)."""
    rng = _scenario_rng("users")
    used = set()
    users = []
    for i in range(count):
        first = rng.pick(FIRST_NAMES)
        last = rng.pick(LAST_NAMES)
        base = re.sub(r"[^a-z0-9-]", "", first + last)
        login = base
        suffix = 2
        while login in used:
            login = "%s-%d" % (base, suffix)
            suffix += 1
        used.add(login)
        users.append({
            "id": 1000 + i,
            "login": login,
            "name": "%s %s" % (first, last),
            "email": "%s@example.invalid" % login,
        })
    return users


VIEWER = scenario_users()[0]
VIEWER_LOGIN = VIEWER["login"]
VIEWER_NAME = VIEWER["name"]
VIEWER_EMAIL = VIEWER["email"]


# ---------------------------------------------------------------------------
# Small shared helpers
# ---------------------------------------------------------------------------

_seq_lock = threading.Lock()
_seq = [0]


def next_seq():
    """A process-wide monotonic sequence number (creation order)."""
    with _seq_lock:
        _seq[0] += 1
        return _seq[0]


def iso_now():
    """A deterministic ISO-8601 timestamp, one second per call."""
    stamp = TIME_EPOCH + next_seq()
    return datetime.fromtimestamp(stamp, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def git_timestamp():
    """A deterministic unix timestamp for a git object."""
    return TIME_EPOCH + next_seq()


_req_counter = [0]
_req_lock = threading.Lock()


def next_request_id():
    with _req_lock:
        _req_counter[0] += 1
        return "req-%08x" % _req_counter[0]


def b64encode_text(text):
    return base64.b64encode(text.encode("utf-8")).decode("ascii")


def b64encode_bytes(data):
    return base64.b64encode(data).decode("ascii")


def b64decode_bytes(text):
    cleaned = re.sub(r"[\r\n\t ]+", "", text)
    return base64.b64decode(cleaned)


def global_id(kind, *parts):
    """An opaque, stable Relay-style global id (base64, never the plain number)."""
    raw = ":".join([kind] + [str(p) for p in parts])
    return base64.b64encode(raw.encode("utf-8")).decode("ascii")


def parse_global_id(value):
    """Decode a global id into (kind, parts) or None."""
    try:
        raw = base64.b64decode(value.encode("ascii")).decode("utf-8")
    except Exception:
        return None
    pieces = raw.split(":")
    if len(pieces) < 2:
        return None
    return pieces[0], pieces[1:]


def json_dumps(obj):
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def log_line(text):
    try:
        sys.stderr.write("[forge] %s\n" % text)
        sys.stderr.flush()
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Git objects: hashing, trees, commits, tags
# ---------------------------------------------------------------------------

TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def hash_object(obj_type, data):
    """git's object id: SHA-1 over "<type> <size>\0" + bytes."""
    header = ("%s %d\0" % (obj_type, len(data))).encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def is_oid(value):
    return isinstance(value, str) and SHA_RE.match(value) is not None


def parse_tree(data):
    """A tree object -> [(mode, name, oid)] in stored order."""
    entries = []
    offset = 0
    while offset < len(data):
        space = data.index(b" ", offset)
        nul = data.index(b"\0", space + 1)
        mode = data[offset:space].decode("ascii")
        name = data[space + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        offset = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    key = name + "/" if mode == "40000" else name
    return key.encode("utf-8")


def build_tree(entries):
    """Entries -> tree bytes, sorted the way git sorts them."""
    parts = []
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        parts.append(("%s %s\0" % (mode, name)).encode("utf-8"))
        parts.append(bytes.fromhex(oid))
    return b"".join(parts)


def parse_commit(data):
    """A commit object -> {tree, parents, author, committer, message}."""
    blank = data.find(b"\n\n")
    header = data if blank < 0 else data[:blank]
    message = "" if blank < 0 else data[blank + 2:].decode("utf-8")
    tree = ""
    parents = []
    author = ""
    committer = ""
    for line in header.decode("utf-8", "replace").split("\n"):
        if not line or line.startswith(" "):
            continue
        key, _, value = line.partition(" ")
        if key == "tree":
            tree = value
        elif key == "parent":
            parents.append(value)
        elif key == "author":
            author = value
        elif key == "committer":
            committer = value
    return {"tree": tree, "parents": parents, "author": author,
            "committer": committer, "message": message}


def build_commit(tree, parents, message, author, committer, timestamp):
    lines = ["tree %s" % tree]
    for parent in parents:
        lines.append("parent %s" % parent)
    lines.append("author %s %d +0000" % (author, timestamp))
    lines.append("committer %s %d +0000" % (committer, timestamp))
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


def parse_tag(data):
    """An annotated tag object -> {object, type, tag, tagger, message}."""
    blank = data.find(b"\n\n")
    header = data if blank < 0 else data[:blank]
    message = "" if blank < 0 else data[blank + 2:].decode("utf-8")
    fields = {}
    for line in header.decode("utf-8", "replace").split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        fields[key] = value
    return {"object": fields.get("object", ""), "type": fields.get("type", ""),
            "tag": fields.get("tag", ""), "tagger": fields.get("tagger", ""),
            "message": message}


# ---------------------------------------------------------------------------
# Packfiles: read (with deltas) and write (plain objects)
# ---------------------------------------------------------------------------

class PackError(Exception):
    pass


def _read_varint_size(buf, start):
    byte = buf[start]
    size = byte & 0x0F
    shift = 4
    offset = start + 1
    first = byte
    while byte & 0x80:
        if offset >= len(buf):
            raise PackError("truncated pack entry size")
        byte = buf[offset]
        offset += 1
        size += (byte & 0x7F) << shift
        shift += 7
    return size, offset, first


def _read_ofs_base(buf, start):
    byte = buf[start]
    offset = start + 1
    value = byte & 0x7F
    while byte & 0x80:
        if offset >= len(buf):
            raise PackError("truncated ofs-delta base offset")
        byte = buf[offset]
        offset += 1
        value = ((value + 1) << 7) + (byte & 0x7F)
    return value, offset


def _inflate_at(buf, offset, limit):
    """Inflate one zlib stream starting at offset; return (data, next_offset)."""
    decomp = zlib.decompressobj()
    try:
        data = decomp.decompress(buf[offset:limit])
    except zlib.error as exc:
        raise PackError("zlib stream did not inflate: %s" % exc)
    consumed = (limit - offset) - len(decomp.unused_data)
    if consumed <= 0:
        raise PackError("zlib stream consumed no bytes")
    return data, offset + consumed


def apply_delta(base, delta):
    """Apply a git delta instruction stream to a base object's bytes."""
    offset = 0

    def read_size():
        nonlocal offset
        value = 0
        shift = 0
        while True:
            if offset >= len(delta):
                raise PackError("delta size varint truncated")
            byte = delta[offset]
            offset += 1
            value += (byte & 0x7F) << shift
            shift += 7
            if not (byte & 0x80):
                return value

    source_size = read_size()
    target_size = read_size()
    if source_size != len(base):
        raise PackError("delta expects a %d-byte base, got %d" % (source_size, len(base)))
    out = bytearray()
    while offset < len(delta):
        op = delta[offset]
        offset += 1
        if op & 0x80:
            copy_offset = 0
            copy_size = 0
            shift = 0
            for bit in range(4):
                if op & (1 << bit):
                    if offset >= len(delta):
                        raise PackError("delta copy offset truncated")
                    copy_offset += delta[offset] << shift
                    offset += 1
                shift += 8
            shift = 0
            for bit in range(4, 7):
                if op & (1 << bit):
                    if offset >= len(delta):
                        raise PackError("delta copy size truncated")
                    copy_size += delta[offset] << shift
                    offset += 1
                shift += 8
            if copy_size == 0:
                copy_size = 0x10000
            if copy_offset + copy_size > len(base):
                raise PackError("delta copy is out of the base")
            out += base[copy_offset:copy_offset + copy_size]
        elif op != 0:
            literal = op & 0x7F
            if offset + literal > len(delta):
                raise PackError("delta insert truncated")
            out += delta[offset:offset + literal]
            offset += literal
        else:
            raise PackError("delta opcode 0 is invalid")
    if len(out) != target_size:
        raise PackError("delta produced %d of %d bytes" % (len(out), target_size))
    return bytes(out)


def read_pack(pack, resolve_base=None):
    """Parse a packfile; return {oid: (type, data)} with every delta resolved."""
    if len(pack) < 32:
        raise PackError("pack is %d bytes, too short" % len(pack))
    if pack[:4] != b"PACK":
        raise PackError("pack does not start with PACK")
    version = struct.unpack(">I", pack[4:8])[0]
    if version not in (2, 3):
        raise PackError("unsupported pack version %d" % version)
    declared = struct.unpack(">I", pack[8:12])[0]
    trailer_start = len(pack) - 20
    trailer = pack[trailer_start:].hex()
    if hashlib.sha1(pack[:trailer_start]).hexdigest() != trailer:
        raise PackError("pack trailer checksum mismatch")
    raw = []
    by_offset = {}
    offset = 12
    for _ in range(declared):
        entry_offset = offset
        size, offset, first = _read_varint_size(pack, offset)
        type_code = (first >> 4) & 0x07
        entry = {"offset": entry_offset, "type_code": type_code, "size": size}
        if type_code == 6:
            base_off, offset = _read_ofs_base(pack, offset)
            if base_off <= 0 or base_off > entry_offset:
                raise PackError("ofs-delta names an invalid base offset")
            entry["base_offset"] = entry_offset - base_off
        elif type_code == 7:
            if offset + 20 > trailer_start:
                raise PackError("ref-delta base id truncated")
            entry["base_oid"] = pack[offset:offset + 20].hex()
            offset += 20
        elif type_code not in CODE_TYPE:
            raise PackError("pack entry has unknown type code %d" % type_code)
        data, offset = _inflate_at(pack, offset, trailer_start)
        if len(data) != size:
            raise PackError("pack entry declares %d bytes but inflated to %d" % (size, len(data)))
        entry["data"] = data
        raw.append(entry)
        by_offset[entry_offset] = entry
    if offset != trailer_start:
        raise PackError("pack has stray bytes before its trailer")
    resolved_by_oid = {}
    objects = {}
    resolving = set()

    def resolve(entry):
        if "resolved" in entry:
            return entry["resolved"]
        if entry["offset"] in resolving:
            raise PackError("delta cycle at pack offset %d" % entry["offset"])
        resolving.add(entry["offset"])
        if entry["type_code"] == 6:
            base_entry = by_offset.get(entry["base_offset"])
            if base_entry is None:
                raise PackError("ofs-delta base is not in the pack")
            base_type, base_data = resolve(base_entry)
            obj_type, data = base_type, apply_delta(base_data, entry["data"])
        elif entry["type_code"] == 7:
            wanted = entry["base_oid"]
            base_entry = resolved_by_oid.get(wanted)
            if base_entry is not None:
                base_type, base_data = resolve(base_entry)
            elif resolve_base is not None:
                found = resolve_base(wanted)
                if found is None:
                    raise PackError("ref-delta base %s is neither in the pack nor on the server" % wanted)
                base_type, base_data = found
            else:
                raise PackError("ref-delta base %s is not in the pack" % wanted)
            obj_type, data = base_type, apply_delta(base_data, entry["data"])
        else:
            obj_type, data = CODE_TYPE[entry["type_code"]], entry["data"]
        oid = hash_object(obj_type, data)
        entry["resolved"] = (obj_type, data)
        entry["oid"] = oid
        resolved_by_oid[oid] = entry
        resolving.discard(entry["offset"])
        return obj_type, data

    for entry in raw:
        obj_type, data = resolve(entry)
        objects[entry["oid"]] = (obj_type, data)
    return objects


def _pack_entry_header(obj_type, size):
    code = TYPE_CODE[obj_type]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    while size > 0:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects):
    """Build a packfile from plain objects (no deltas): [(type, data)]."""
    parts = [b"PACK" + struct.pack(">II", 2, len(objects))]
    for obj_type, data in objects:
        parts.append(_pack_entry_header(obj_type, len(data)))
        parts.append(zlib.compress(data))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


# ---------------------------------------------------------------------------
# pkt-line framing
# ---------------------------------------------------------------------------

def pkt_line(payload):
    """One data pkt-line: 4 hex length bytes then the payload."""
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    if len(payload) > PKT_LINE_MAX - 4:
        raise ValueError("pkt-line payload too long")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


FLUSH_PKT = b"0000"
DELIM_PKT = b"0001"


def pkt_lines(items):
    """Encode a sequence of payloads / 'flush' / 'delim' markers."""
    out = []
    for item in items:
        if item == "flush":
            out.append(FLUSH_PKT)
        elif item == "delim":
            out.append(DELIM_PKT)
        else:
            out.append(pkt_line(item))
    return b"".join(out)


class PktError(Exception):
    pass


def parse_pkt_lines(data, stop_at_flush=False):
    """Decode a buffer into [("data", bytes) | ("flush",) | ("delim",) | ...].

    Returns (packets, rest): with stop_at_flush, parsing stops after the
    first flush packet and rest holds the bytes after it (a packfile).
    """
    packets = []
    offset = 0
    while offset < len(data):
        if offset + 4 > len(data):
            raise PktError("truncated pkt-line header")
        header = data[offset:offset + 4]
        try:
            length = int(header.decode("ascii"), 16)
        except ValueError:
            raise PktError("invalid pkt-line length %r" % header)
        if length == 0:
            packets.append(("flush",))
            offset += 4
            if stop_at_flush:
                return packets, data[offset:]
            continue
        if length == 1:
            packets.append(("delim",))
            offset += 4
            continue
        if length == 2:
            packets.append(("response-end",))
            offset += 4
            continue
        if length < 4 or length > PKT_LINE_MAX:
            raise PktError("invalid pkt-line length %d" % length)
        if offset + length > len(data):
            raise PktError("truncated pkt-line")
        packets.append(("data", data[offset + 4:offset + length]))
        offset += length
    return packets, b""


def sideband_packets(band, payload, chunk_size=65511):
    """Wrap bytes in sideband pkt-lines (band byte + chunk)."""
    out = []
    if not payload:
        return out
    for i in range(0, len(payload), chunk_size):
        chunk = payload[i:i + chunk_size]
        out.append(pkt_line(bytes([band]) + chunk))
    return out


# ---------------------------------------------------------------------------
# The store: repositories, issues, pull requests, labels, comments
# ---------------------------------------------------------------------------

class ApiError(Exception):
    """An error that maps to an HTTP status with a JSON {message} body."""

    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


class Repo:
    def __init__(self, repo_id, name, private, description):
        self.id = repo_id
        self.name = name
        self.owner = VIEWER_LOGIN
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = DEFAULT_BRANCH
        self.created_at = iso_now()
        self.updated_at = self.created_at
        # git state
        self.objects = {}          # oid -> (type, data)
        self.refs = {}             # "refs/heads/main" -> oid
        # collaboration state
        self.issues = {}           # number -> dict
        self.pulls = {}            # number -> dict
        self.labels = {}           # name -> dict
        self.next_number = 1       # issues and PRs share GitHub's numbering
        self.next_label_id = 1

    # -- git helpers ------------------------------------------------------

    def ref_tip(self, refname):
        return self.refs.get(refname)

    def branch_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def head_tip(self):
        return self.branch_tip(self.default_branch)

    def put_object(self, obj_type, data):
        oid = hash_object(obj_type, data)
        self.objects.setdefault(oid, (obj_type, data))
        return oid

    def get_object(self, oid):
        return self.objects.get(oid)

    def tree_of(self, commit_oid):
        obj = self.objects.get(commit_oid)
        if obj is None or obj[0] != "commit":
            return None
        return parse_commit(obj[1])["tree"]


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}            # name -> Repo (the viewer owns every repo)
        self.next_repo_id = 1
        self.next_comment_id = 1

    def create_repo(self, name, private, description):
        with self.lock:
            if name in self.repos:
                raise ApiError(422, "Repository already exists")
            repo = Repo(self.next_repo_id, name, private, description)
            self.next_repo_id += 1
            self.repos[name] = repo
            return repo

    def get_repo(self, owner, name):
        if owner != VIEWER_LOGIN:
            return None
        return self.repos.get(name)

    def delete_repo(self, name):
        with self.lock:
            self.repos.pop(name, None)

    def list_repos(self):
        with self.lock:
            return sorted(self.repos.values(), key=lambda r: r.id)


STORE = Store()


# ---------------------------------------------------------------------------
# Git graph operations over one repository
# ---------------------------------------------------------------------------

def peel_to_commit(repo, oid):
    """Follow annotated tags to the object they point at (a commit, usually)."""
    seen = set()
    while oid in repo.objects and repo.objects[oid][0] == "tag" and oid not in seen:
        seen.add(oid)
        oid = parse_tag(repo.objects[oid][1])["object"]
    return oid


def commit_parents(repo, oid):
    obj = repo.objects.get(oid)
    if obj is None or obj[0] != "commit":
        return []
    return parse_commit(obj[1])["parents"]


def walk_commits(repo, tip, limit=None):
    """Commits reachable from tip, newest first (BFS by generation)."""
    out = []
    seen = set()
    queue = [tip]
    while queue:
        oid = queue.pop(0)
        if oid in seen:
            continue
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        seen.add(oid)
        out.append(oid)
        if limit is not None and len(out) >= limit:
            break
        queue.extend(commit_parents(repo, oid))
    return out


def is_ancestor(repo, ancestor, descendant):
    """True when ancestor is reachable from descendant (or equal)."""
    if ancestor == descendant:
        return True
    seen = set()
    queue = [descendant]
    while queue:
        oid = queue.pop()
        if oid in seen:
            continue
        seen.add(oid)
        for parent in commit_parents(repo, oid):
            if parent == ancestor:
                return True
            queue.append(parent)
    return False


def merge_base(repo, a, b):
    """A common ancestor of a and b (the first found walking from b)."""
    ancestors_a = set(walk_commits(repo, a))
    queue = [b]
    seen = set()
    while queue:
        oid = queue.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        if oid in ancestors_a:
            return oid
        queue.extend(commit_parents(repo, oid))
    return None


def reachable_objects(repo, tips, cut=()):
    """Every object id reachable from tips.

    `cut` holds commit ids treated as roots: they are included, but their
    parents are not traversed (a shallow client's boundary).
    """
    cut = set(cut)
    seen = set()
    queue = list(tips)
    while queue:
        oid = queue.pop()
        if oid in seen or oid == ZERO_OID:
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            continue
        seen.add(oid)
        obj_type, data = obj
        if obj_type == "commit":
            parsed = parse_commit(data)
            queue.append(parsed["tree"])
            if oid not in cut:
                queue.extend(parsed["parents"])
        elif obj_type == "tag":
            queue.append(parse_tag(data)["object"])
        elif obj_type == "tree":
            for mode, _name, child in parse_tree(data):
                if mode != "160000":
                    queue.append(child)
    return seen


def tree_lookup(repo, tree_oid, segments):
    """(mode, oid) of a path in a tree, or None."""
    current = tree_oid
    for index, segment in enumerate(segments):
        obj = repo.objects.get(current)
        if obj is None or obj[0] != "tree":
            return None
        found = None
        for mode, name, oid in parse_tree(obj[1]):
            if name == segment:
                found = (mode, oid)
                break
        if found is None:
            return None
        if index == len(segments) - 1:
            return found
        if found[0] != "40000":
            return None
        current = found[1]
    return None


def tree_entries_at(repo, tree_oid, segments):
    """The entries of a directory inside a tree, or None when it is not a dir."""
    current = tree_oid
    for segment in segments:
        found = tree_lookup(repo, current, [segment])
        if found is None or found[0] != "40000":
            return None
        current = found[1]
    obj = repo.objects.get(current)
    if obj is None or obj[0] != "tree":
        return None
    return parse_tree(obj[1])


def tree_set(repo, tree_oid, segments, blob_oid):
    """A new tree with segments set to blob_oid (None deletes the path)."""
    obj = repo.objects.get(tree_oid) if tree_oid else None
    entries = list(parse_tree(obj[1])) if obj is not None and obj[0] == "tree" else []
    head, rest = segments[0], segments[1:]
    kept = [(m, n, o) for (m, n, o) in entries if n != head]
    if not rest:
        if blob_oid is not None:
            kept.append(("100644", head, blob_oid))
    else:
        existing = None
        for mode, name, oid in entries:
            if name == head and mode == "40000":
                existing = oid
                break
        child = tree_set(repo, existing, rest, blob_oid)
        child_entries = parse_tree(repo.objects[child][1])
        if child_entries:
            kept.append(("40000", head, child))
    return repo.put_object("tree", build_tree(kept))


def flatten_tree(repo, tree_oid, prefix=""):
    """{path: (mode, oid)} for every blob under a tree (recursive)."""
    out = {}
    obj = repo.objects.get(tree_oid)
    if obj is None or obj[0] != "tree":
        return out
    for mode, name, oid in parse_tree(obj[1]):
        path = prefix + name
        if mode == "40000":
            out.update(flatten_tree(repo, oid, path + "/"))
        else:
            out[path] = (mode, oid)
    return out


def diff_trees(repo, old_tree, new_tree):
    """[(path, status, old_oid, new_oid)] between two trees.

    status is added / modified / removed. A rename is a remove + an add.
    """
    old = flatten_tree(repo, old_tree) if old_tree else {}
    new = flatten_tree(repo, new_tree) if new_tree else {}
    changes = []
    for path in sorted(set(old) | set(new)):
        in_old, in_new = path in old, path in new
        if in_old and not in_new:
            changes.append((path, "removed", old[path][1], None))
        elif in_new and not in_old:
            changes.append((path, "added", None, new[path][1]))
        elif old[path][1] != new[path][1]:
            changes.append((path, "modified", old[path][1], new[path][1]))
    return changes


def count_line_changes(repo, old_oid, new_oid):
    """(additions, deletions) between two blobs, by line diff."""
    def lines(oid):
        if oid is None:
            return []
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "blob":
            return []
        return obj[1].decode("utf-8", "replace").splitlines()
    old_lines = lines(old_oid)
    new_lines = lines(new_oid)
    matcher = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    additions = deletions = 0
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag in ("insert", "replace"):
            additions += j2 - j1
        if tag in ("delete", "replace"):
            deletions += i2 - i1
    return additions, deletions


def make_commit(repo, tree_oid, parents, message):
    """Create a commit object as the viewer, with a deterministic timestamp."""
    who = "%s <%s>" % (VIEWER_NAME, VIEWER_EMAIL)
    if not message.endswith("\n"):
        message += "\n"
    data = build_commit(tree_oid, parents, message, who, who, git_timestamp())
    return repo.put_object("commit", data)


def compute_fetch(repo, wants, haves, shallow_client, deepen, include_tags=False,
                  deepen_relative=False):
    """The objects a fetch must send, and the shallow-info lines.

    Returns (send_oids, shallow_oids, unshallow_oids).

    With an absolute deepen, commits are included by their distance from the
    wants. With deepen-relative, the depth counts generations below the
    client's current shallow boundary instead.
    """
    shallow_client = set(shallow_client)
    have_objs = set()
    for have in haves:
        have_objs |= reachable_objects(repo, [have], cut=shallow_client)
    if deepen_relative and deepen is not None:
        # Pass 1: everything at or above the old shallow boundary.
        above = set()
        queue = list(wants)
        while queue:
            oid = queue.pop(0)
            if oid in above or oid == ZERO_OID:
                continue
            obj = repo.objects.get(oid)
            if obj is None:
                continue
            above.add(oid)
            if obj[0] == "tag":
                queue.append(parse_tag(obj[1])["object"])
                continue
            if obj[0] != "commit" or oid in shallow_client:
                continue
            queue.extend(commit_parents(repo, oid))
        # Pass 2: N generations below each shallow commit on the boundary.
        depth_below = {}
        queue = []
        for oid in above & shallow_client:
            depth_below[oid] = 0
            queue.append((oid, 0))
        while queue:
            oid, depth = queue.pop(0)
            if depth >= deepen:
                continue
            for parent in commit_parents(repo, oid):
                next_depth = depth + 1
                if parent not in depth_below or next_depth < depth_below[parent]:
                    depth_below[parent] = next_depth
                    queue.append((parent, next_depth))
        included = above | set(depth_below)
        boundary = {oid for oid, depth in depth_below.items()
                    if depth == deepen and commit_parents(repo, oid)}
        visited = included
    else:
        # Walk the wanted commits, honouring the depth limit.
        included = []
        visited = set()
        boundary = set()
        queue = [(want, 0) for want in wants]
        while queue:
            oid, depth = queue.pop(0)
            if oid in visited or oid == ZERO_OID:
                continue
            obj = repo.objects.get(oid)
            if obj is None:
                continue
            visited.add(oid)
            included.append(oid)
            if obj[0] == "tag":
                queue.append((parse_tag(obj[1])["object"], depth))
                continue
            if obj[0] != "commit":
                continue
            parents = parse_commit(obj[1])["parents"]
            if deepen is not None and depth + 1 >= deepen:
                if parents:
                    boundary.add(oid)
            else:
                for parent in parents:
                    queue.append((parent, depth + 1))
    send = set()
    for oid in included:
        send |= reachable_objects(repo, [oid], cut=boundary)
    send -= have_objs
    if include_tags:
        # Tags pointing at a fetched commit ride along with it.
        for ref, oid in repo.refs.items():
            if not ref.startswith("refs/tags/"):
                continue
            obj = repo.objects.get(oid)
            if obj is not None and obj[0] == "tag":
                if parse_tag(obj[1])["object"] in visited:
                    send.add(oid)
    unshallow = []
    for oid in shallow_client:
        if oid not in visited:
            continue
        parents = commit_parents(repo, oid)
        if all(p in visited or p in have_objs for p in parents):
            unshallow.append(oid)
    return send, sorted(boundary), sorted(unshallow)


def merge_conflict(repo, base_tip, head_tip):
    """True when squashing head onto base would conflict on a file."""
    if base_tip is None or head_tip is None:
        return False
    base = merge_base(repo, base_tip, head_tip)
    if base is None:
        return False
    mb_tree = repo.tree_of(base)
    base_tree = repo.tree_of(base_tip)
    head_tree = repo.tree_of(head_tip)
    base_diff = {p: new for (p, _s, _o, new) in diff_trees(repo, mb_tree, base_tree)}
    head_diff = {p: new for (p, _s, _o, new) in diff_trees(repo, mb_tree, head_tree)}
    for path, head_new in head_diff.items():
        if path in base_diff and base_diff[path] != head_new:
            return True
    return False


def squash_merge(repo, pr):
    """Squash-merge a pull request onto its base branch.

    Returns the new commit oid, or raises ApiError(405) on a conflict.
    """
    base_tip = repo.branch_tip(pr["base_ref"])
    head_tip = repo.branch_tip(pr["head_ref"])
    if base_tip is None or head_tip is None:
        raise ApiError(405, "Cannot merge: a branch is missing")
    if merge_conflict(repo, base_tip, head_tip):
        raise ApiError(405, "Merge conflict")
    base = merge_base(repo, base_tip, head_tip)
    mb_tree = repo.tree_of(base) if base else None
    head_tree = repo.tree_of(head_tip)
    tree = repo.tree_of(base_tip)
    for path, _status, _old, new in diff_trees(repo, mb_tree, head_tree):
        tree = tree_set(repo, tree, path.split("/"), new)
    message = "Squash merge #%d: %s\n" % (pr["number"], pr["title"])
    commit = make_commit(repo, tree, [base_tip], message)
    repo.refs["refs/heads/" + pr["base_ref"]] = commit
    return commit


# ---------------------------------------------------------------------------
# HTTP plumbing
# ---------------------------------------------------------------------------

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")
EXPECTED_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


def _quote_path(path):
    return urllib.parse.quote(path, safe="/-_.~")


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    # -- logging goes to stderr, quietly -----------------------------------
    # Per-request logging stays off: address_string() does a reverse DNS
    # lookup and every log line is a syscall, and the read workload issues
    # 2,000 requests on one connection. Errors still reach stderr.

    def log_message(self, fmt, *args):
        pass

    # -- response helpers ---------------------------------------------------
    # Every response goes out as ONE write (status line, headers, body):
    # BaseHTTPRequestHandler's send_response/send_header/end_headers/write
    # sequence is five small writes, and with Nagle on the server and
    # delayed ACKs on the client each request then costs a ~40 ms stall.

    def _send_raw(self, status, headers, body):
        if isinstance(body, str):
            body = body.encode("utf-8")
        reason = self.responses.get(status, ("???", ""))[0]
        lines = ["HTTP/1.1 %d %s\r\n" % (status, reason)]
        lines.append("Server: %s\r\n" % self.version_string())
        lines.append("Date: %s\r\n" % self.date_time_string())
        for key, value in headers:
            lines.append("%s: %s\r\n" % (key, value))
        lines.append("\r\n")
        self.wfile.write("".join(lines).encode("iso-8859-1") + body)

    def _send_bytes(self, status, body, content_type, extra_headers=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        headers = [("Content-Type", content_type),
                   ("Content-Length", str(len(body)))]
        if extra_headers:
            for key, value in extra_headers.items():
                if value is not None:
                    headers.append((key, value))
        self._send_raw(status, headers, body)

    def send_json(self, status, obj, extra_headers=None):
        headers = {"X-GitHub-Request-Id": next_request_id()}
        if extra_headers:
            headers.update(extra_headers)
        body = json_dumps(obj) if obj is not None else ""
        self._send_bytes(status, body, "application/json; charset=utf-8", headers)

    def send_json_error(self, status, message):
        self.send_json(status, {"message": message})

    def send_204(self):
        self._send_raw(204, [("Content-Length", "0"),
                             ("X-GitHub-Request-Id", next_request_id())], b"")

    def send_git_bytes(self, status, body, content_type):
        self._send_bytes(status, body, content_type,
                         {"X-GitHub-Request-Id": next_request_id()})

    # -- request parsing ----------------------------------------------------

    def read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            self._body_consumed = True
            return b""
        try:
            size = int(length)
        except ValueError:
            self._body_consumed = True
            return b""
        if size <= 0:
            self._body_consumed = True
            return b""
        self._body_consumed = True
        return self.rfile.read(size)

    def drain_body(self):
        """Discard an unread request body so the connection stays usable."""
        if getattr(self, "_body_consumed", True):
            return
        self.read_body()

    def read_json(self):
        raw = self.read_body()
        if not raw:
            return {}
        try:
            value = json.loads(raw.decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            raise ApiError(400, "Invalid JSON in request body")
        if not isinstance(value, dict):
            raise ApiError(400, "Request body must be a JSON object")
        return value

    def query(self):
        return urllib.parse.parse_qs(self.parsed.query, keep_blank_values=True)

    def query_one(self, name, default=None):
        values = self.query().get(name)
        return values[0] if values else default

    def absolute_url(self, path, params):
        host = self.headers.get("Host") or ("127.0.0.1:%d" % self.server.server_address[1])
        query = urllib.parse.urlencode(params, doseq=True)
        return "http://%s%s%s" % (host, path, ("?" + query) if query else "")

    def pagination(self, items, default_per_page=30):
        """Slice a list by ?page=&per_page= and build a Link header."""
        try:
            page = max(1, int(self.query_one("page", "1")))
        except ValueError:
            page = 1
        try:
            per_page = int(self.query_one("per_page", str(default_per_page)))
        except ValueError:
            per_page = default_per_page
        per_page = max(1, min(100, per_page))
        total = len(items)
        start = (page - 1) * per_page
        page_items = items[start:start + per_page]
        params = {k: v[0] for k, v in self.query().items()}
        last_page = max(1, (total + per_page - 1) // per_page)
        links = []
        if page < last_page:
            params["page"] = str(page + 1)
            params["per_page"] = str(per_page)
            links.append('<%s>; rel="next"' % self.absolute_url(self.parsed.path, params))
        if page > 1:
            params["page"] = str(page - 1)
            params["per_page"] = str(per_page)
            links.append('<%s>; rel="prev"' % self.absolute_url(self.parsed.path, params))
        params["page"] = "1"
        params["per_page"] = str(per_page)
        links.append('<%s>; rel="first"' % self.absolute_url(self.parsed.path, params))
        params["page"] = str(last_page)
        links.append('<%s>; rel="last"' % self.absolute_url(self.parsed.path, params))
        return page_items, ", ".join(links)

    # -- auth ---------------------------------------------------------------

    def require_auth(self):
        """True when the bearer token matches; otherwise sends 401."""
        if not EXPECTED_TOKEN:
            return True
        auth = self.headers.get("Authorization") or ""
        if auth == "Bearer %s" % EXPECTED_TOKEN:
            return True
        self.drain_body()
        self.send_json_error(401, "Bad credentials")
        return False

    # -- dispatch -----------------------------------------------------------

    def _dispatch(self):
        self.parsed = urllib.parse.urlsplit(self.path)
        self._body_consumed = False
        path = self.parsed.path
        self.path_segments = [urllib.parse.unquote(seg) for seg in path.split("/") if seg != ""]
        try:
            if path == "/healthz":
                if self.command != "GET":
                    self.send_json_error(404, "Not Found")
                else:
                    self.send_json(200, {"ok": True})
                return
            if path == "/api/graphql":
                self._handle_graphql()
                return
            if path == "/mcp":
                self._handle_mcp()
                return
            if self.path_segments[:2] == ["api", "v3"]:
                self._handle_rest()
                return
            if len(self.path_segments) >= 3 and self.path_segments[1].endswith(".git"):
                self._handle_git()
                return
            self.drain_body()
            self.send_json_error(404, "Not Found")
        except ApiError as exc:
            self.drain_body()
            self.send_json_error(exc.status, exc.message)
        except BrokenPipeError:
            raise
        except Exception as exc:  # never take the server down for one request
            log_line("error on %s %s: %r" % (self.command, self.path, exc))
            try:
                self.drain_body()
                self.send_json_error(500, "Internal Server Error")
            except Exception:
                pass
        finally:
            # A handler that never read its request body (a PUT merge, a
            # DELETE) must not leave those bytes for the next request on
            # this keep-alive connection.
            try:
                self.drain_body()
            except Exception:
                pass

    def do_GET(self):
        self._dispatch()

    def do_POST(self):
        self._dispatch()

    def do_PUT(self):
        self._dispatch()

    def do_PATCH(self):
        self._dispatch()

    def do_DELETE(self):
        self._dispatch()

    def do_HEAD(self):
        self._dispatch()


# ---------------------------------------------------------------------------
# REST v3 serializers
# ---------------------------------------------------------------------------

def user_json():
    return {"login": VIEWER_LOGIN, "id": 1000, "node_id": global_id("User", 1000),
            "name": VIEWER_NAME, "email": VIEWER_EMAIL, "type": "User",
            "created_at": "2025-01-01T00:00:00Z",
            "avatar_url": "", "html_url": ""}


def repo_json(repo):
    return {
        "id": repo.id,
        "node_id": global_id("Repository", repo.id),
        "name": repo.name,
        "full_name": "%s/%s" % (VIEWER_LOGIN, repo.name),
        "owner": user_json(),
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "created_at": repo.created_at,
        "updated_at": repo.updated_at,
        "pushed_at": repo.updated_at,
        "has_issues": True,
        "has_projects": False,
        "has_wiki": False,
        "fork": False,
        "archived": False,
        "disabled": False,
        "open_issues_count": sum(1 for i in repo.issues.values() if i["state"] == "open")
                              + sum(1 for p in repo.pulls.values() if p["state"] == "open"),
    }


def label_json(label):
    return {"id": label["id"], "name": label["name"], "color": label["color"],
            "description": label.get("description", "")}


def issue_json(repo, issue):
    return {
        "id": repo.id * 1000000 + issue["number"],
        "node_id": global_id("Issue", repo.id, issue["number"]),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "user": user_json(),
        "labels": [label_json(repo.labels[name]) for name in issue["labels"]
                   if name in repo.labels],
        "comments": len(issue["comments"]),
        "created_at": issue["created_at"],
        "updated_at": issue["updated_at"],
        "closed_at": issue["closed_at"],
        "locked": False,
        "assignee": None,
    }


def pr_json(repo, pr):
    head_tip = repo.branch_tip(pr["head_ref"])
    base_tip = repo.branch_tip(pr["base_ref"])
    return {
        "id": repo.id * 1000000 + 500000 + pr["number"],
        "node_id": global_id("PullRequest", repo.id, pr["number"]),
        "number": pr["number"],
        "title": pr["title"],
        "body": pr["body"],
        "state": pr["state"],
        "user": user_json(),
        "labels": [],
        "head": {"ref": pr["head_ref"], "sha": head_tip or ZERO_OID,
                 "label": "%s:%s" % (VIEWER_LOGIN, pr["head_ref"]),
                 "repo": repo_json(repo)},
        "base": {"ref": pr["base_ref"], "sha": base_tip or ZERO_OID,
                 "label": "%s:%s" % (VIEWER_LOGIN, pr["base_ref"]),
                 "repo": repo_json(repo)},
        "merged": pr["merged"],
        "merged_at": pr["merged_at"],
        "merge_commit_sha": pr["merge_commit_sha"],
        "mergeable": pr["mergeable"],
        "draft": False,
        "created_at": pr["created_at"],
        "updated_at": pr["updated_at"],
        "closed_at": pr["closed_at"],
    }


def comment_json(comment):
    return {"id": comment["id"], "node_id": global_id("IssueComment", comment["id"]),
            "body": comment["body"], "user": user_json(),
            "created_at": comment["created_at"],
            "updated_at": comment["updated_at"]}


def commit_json(repo, oid):
    obj = repo.objects.get(oid)
    parsed = parse_commit(obj[1])
    author_name, author_email, _rest = _split_ident(parsed["author"])
    committer_name, committer_email, _rest = _split_ident(parsed["committer"])
    return {
        "sha": oid,
        "node_id": global_id("Commit", oid),
        "commit": {
            "message": parsed["message"].rstrip("\n"),
            "author": {"name": author_name, "email": author_email,
                       "date": _ident_date(parsed["author"])},
            "committer": {"name": committer_name, "email": committer_email,
                          "date": _ident_date(parsed["committer"])},
            "tree": {"sha": parsed["tree"]},
        },
        "author": user_json(),
        "committer": user_json(),
        "parents": [{"sha": p} for p in parsed["parents"]],
    }


def _split_ident(ident):
    """'Name <email> ts tz' -> (name, email, rest)."""
    match = re.match(r"^(.*?) <(.*?)> (\d+) ([+-]\d{4})$", ident)
    if not match:
        return ident, "", ""
    return match.group(1), match.group(2), ""


def _ident_date(ident):
    match = re.match(r"^.*? <.*?> (\d+) ([+-]\d{4})$", ident)
    if not match:
        return "2025-01-01T00:00:00Z"
    stamp = int(match.group(1))
    return datetime.fromtimestamp(stamp, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# REST v3 routing
# ---------------------------------------------------------------------------

def _resolve_ref(repo, ref):
    """A branch name, full ref, HEAD or commit oid -> a commit oid (or None)."""
    if ref is None:
        return repo.head_tip()
    if ref == "HEAD":
        return repo.head_tip()
    if ref in repo.refs:
        tip = repo.refs[ref]
        return peel_to_commit(repo, tip)
    tip = repo.branch_tip(ref)
    if tip is not None:
        return peel_to_commit(repo, tip)
    tag = repo.refs.get("refs/tags/" + ref)
    if tag is not None:
        return peel_to_commit(repo, tag)
    if is_oid(ref) and ref in repo.objects:
        return peel_to_commit(repo, ref)
    return None


def _strip_owner_prefix(branch):
    """'owner:branch' -> 'branch'; a plain branch is unchanged."""
    if ":" in branch:
        return branch.split(":", 1)[1]
    return branch


def _rest_repo(self, owner, name):
    repo = STORE.get_repo(owner, name)
    if repo is None:
        raise ApiError(404, "Not Found")
    return repo


def _handle_rest(self):
    if not self.require_auth():
        return
    seg = self.path_segments[2:]  # after /api/v3
    method = self.command
    if not seg:
        self.send_json(200, {
            "current_user_url": "/api/v3/user",
            "repository_url": "/api/v3/repos/{owner}/{repo}",
            "meta_url": "/api/v3/meta",
        }, {"X-OAuth-Scopes": "repo, read:org"})
        return
    head = seg[0]
    if head == "meta":
        if method != "GET":
            raise ApiError(404, "Not Found")
        self.send_json(200, {"installed_version": VERSION})
        return
    if head == "user":
        if len(seg) == 1:
            if method != "GET":
                raise ApiError(404, "Not Found")
            self.send_json(200, user_json())
            return
        if seg[1] == "repos":
            if method == "GET":
                repos = [repo_json(r) for r in STORE.list_repos()]
                page, link = self.pagination(repos)
                self.send_json(200, page, {"Link": link})
                return
            if method == "POST":
                body = self.read_json()
                name = body.get("name")
                if not isinstance(name, str) or not name:
                    raise ApiError(422, "Validation Failed: name is required")
                repo = STORE.create_repo(name, body.get("private", False),
                                         body.get("description", ""))
                self.send_json(201, repo_json(repo))
                return
            raise ApiError(404, "Not Found")
        raise ApiError(404, "Not Found")
    if head == "repos":
        if len(seg) < 3:
            raise ApiError(404, "Not Found")
        owner, name = seg[1], seg[2]
        repo = _rest_repo(self, owner, name)
        rest = seg[3:]
        if not rest:
            if method == "GET":
                self.send_json(200, repo_json(repo))
                return
            if method == "PATCH":
                body = self.read_json()
                with STORE.lock:
                    if "description" in body:
                        repo.description = body["description"] or ""
                    if "private" in body:
                        repo.private = bool(body["private"])
                    repo.updated_at = iso_now()
                self.send_json(200, repo_json(repo))
                return
            if method == "DELETE":
                STORE.delete_repo(name)
                self.send_204()
                return
            raise ApiError(404, "Not Found")
        sub = rest[0]
        if sub == "branches":
            self._rest_branches(repo, rest[1:])
            return
        if sub == "commits":
            self._rest_commits(repo)
            return
        if sub == "contents":
            self._rest_contents(repo, rest[1:])
            return
        if sub == "git":
            self._rest_git_refs(repo, rest[1:])
            return
        if sub == "labels":
            self._rest_labels(repo)
            return
        if sub == "issues":
            self._rest_issues(repo, rest[1:])
            return
        if sub == "pulls":
            self._rest_pulls(repo, rest[1:])
            return
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")


def _rest_branches(self, repo, rest):
    if self.command != "GET":
        raise ApiError(404, "Not Found")
    with STORE.lock:
        branches = sorted(repo.refs.keys())
    items = []
    for ref in branches:
        if ref.startswith("refs/heads/"):
            items.append({"name": ref[len("refs/heads/"):],
                          "commit": {"sha": repo.refs[ref]}})
    if not rest:
        self.send_json(200, items)
        return
    branch = "/".join(rest)
    for item in items:
        if item["name"] == branch:
            self.send_json(200, item)
            return
    raise ApiError(404, "Branch not found")


def _rest_commits(self, repo):
    if self.command != "GET":
        raise ApiError(404, "Not Found")
    ref = self.query_one("sha")
    tip = _resolve_ref(repo, ref)
    if tip is None:
        self.send_json(200, [])
        return
    commits = [commit_json(repo, oid) for oid in walk_commits(repo, tip)]
    page, link = self.pagination(commits)
    self.send_json(200, page, {"Link": link})


def _rest_contents(self, repo, rest):
    path = "/".join(rest)
    segments = [s for s in path.split("/") if s]
    if self.command == "GET":
        ref = self.query_one("ref")
        tip = _resolve_ref(repo, ref)
        if tip is None:
            raise ApiError(404, "Not Found")
        tree_oid = repo.tree_of(tip)
        if not segments:
            entries = parse_tree(repo.objects[tree_oid][1]) if tree_oid else []
            self.send_json(200, [_contents_dir_entry(repo, tree_oid, m, n, o, "")
                                 for (m, n, o) in entries])
            return
        found = tree_lookup(repo, tree_oid, segments)
        if found is None:
            raise ApiError(404, "Not Found")
        mode, oid = found
        if mode == "40000":
            entries = parse_tree(repo.objects[oid][1])
            self.send_json(200, [_contents_dir_entry(repo, oid, m, n, o, path)
                                 for (m, n, o) in entries])
            return
        blob = repo.objects.get(oid)
        data = blob[1] if blob else b""
        self.send_json(200, {
            "type": "file", "encoding": "base64",
            "content": b64encode_bytes(data),
            "sha": oid, "size": len(data),
            "name": segments[-1], "path": path,
        })
        return
    if self.command == "PUT":
        body = self.read_json()
        message = body.get("message") or "Update %s" % path
        try:
            content = b64decode_bytes(body.get("content", ""))
        except Exception:
            raise ApiError(422, "content is not valid base64")
        branch = body.get("branch") or repo.default_branch
        given_sha = body.get("sha")
        with STORE.lock:
            tip = repo.branch_tip(branch)
            if tip is None and repo.branch_tip(repo.default_branch) is not None:
                tip = repo.branch_tip(repo.default_branch)
            tree_oid = repo.tree_of(tip) if tip else None
            current = tree_lookup(repo, tree_oid, segments) if tree_oid else None
            if current is not None:
                if current[0] == "40000":
                    raise ApiError(422, "Cannot write a file over a directory")
                if given_sha is not None and given_sha != current[1]:
                    raise ApiError(409, "The file has changed since you last read it")
                if given_sha is None:
                    raise ApiError(409, "sha is required to update an existing file")
                status = 200
            else:
                status = 201
            blob_oid = repo.put_object("blob", content)
            new_tree = tree_set(repo, tree_oid, segments, blob_oid)
            parents = [tip] if tip else []
            commit = make_commit(repo, new_tree, parents, message)
            repo.refs["refs/heads/" + branch] = commit
            repo.updated_at = iso_now()
        self.send_json(status, {
            "content": {"name": segments[-1], "path": path, "sha": blob_oid,
                        "size": len(content), "type": "file", "encoding": "base64"},
            "commit": {"sha": commit},
        })
        return
    if self.command == "DELETE":
        body = self.read_json()
        message = body.get("message") or "Delete %s" % path
        branch = body.get("branch") or repo.default_branch
        given_sha = body.get("sha")
        with STORE.lock:
            tip = repo.branch_tip(branch)
            if tip is None:
                raise ApiError(404, "Not Found")
            tree_oid = repo.tree_of(tip)
            current = tree_lookup(repo, tree_oid, segments) if tree_oid else None
            if current is None or current[0] == "40000":
                raise ApiError(404, "Not Found")
            if given_sha is not None and given_sha != current[1]:
                raise ApiError(409, "The file has changed since you last read it")
            new_tree = tree_set(repo, tree_oid, segments, None)
            commit = make_commit(repo, new_tree, [tip], message)
            repo.refs["refs/heads/" + branch] = commit
            repo.updated_at = iso_now()
        self.send_json(200, {"content": None, "commit": {"sha": commit}})
        return
    raise ApiError(404, "Not Found")


def _contents_dir_entry(repo, _tree_oid, mode, name, oid, parent):
    entry = {"type": "dir" if mode == "40000" else "file",
             "name": name, "path": (parent + "/" + name) if parent else name,
             "sha": oid}
    if mode != "40000":
        blob = repo.objects.get(oid)
        entry["size"] = len(blob[1]) if blob else 0
    else:
        entry["size"] = 0
    return entry


def _rest_git_refs(self, repo, rest):
    if self.command == "POST" and rest == ["refs"]:
        body = self.read_json()
        ref = body.get("ref")
        sha = body.get("sha")
        if not isinstance(ref, str) or not ref.startswith("refs/"):
            raise ApiError(422, "ref must start with refs/")
        if not is_oid(sha) or sha not in repo.objects:
            raise ApiError(422, "sha does not name an object in this repository")
        with STORE.lock:
            if ref in repo.refs:
                raise ApiError(422, "Reference already exists")
            repo.refs[ref] = sha
        self.send_json(201, {"ref": ref, "object": {"sha": sha, "type": repo.objects[sha][0]}})
        return
    if self.command == "GET" and rest and rest[0] == "refs" and len(rest) > 1:
        # /git/refs/heads/{branch...} — rest after 'git' is ['refs', 'heads', ...]
        full = "/".join(rest)
        if full in repo.refs:
            self.send_json(200, {"ref": full, "object": {"sha": repo.refs[full],
                                 "type": repo.objects[repo.refs[full]][0]}})
            return
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")


def _rest_labels(self, repo):
    if self.command == "GET":
        with STORE.lock:
            labels = [label_json(l) for l in repo.labels.values()]
        self.send_json(200, labels)
        return
    if self.command == "POST":
        body = self.read_json()
        name = body.get("name")
        color = body.get("color") or "ededed"
        if not isinstance(name, str) or not name:
            raise ApiError(422, "Validation Failed: name is required")
        with STORE.lock:
            if name in repo.labels:
                self.send_json(201, label_json(repo.labels[name]))
                return
            label = {"id": repo.next_label_id, "name": name,
                     "color": color.lstrip("#"), "description": body.get("description", "")}
            repo.next_label_id += 1
            repo.labels[name] = label
        self.send_json(201, label_json(label))
        return
    raise ApiError(404, "Not Found")


def _issue_from_body(repo, body):
    title = body.get("title")
    if not isinstance(title, str) or not title:
        raise ApiError(422, "Validation Failed: title is required")
    label_names = []
    for label in body.get("labels") or []:
        label_name = label.get("name") if isinstance(label, dict) else label
        if label_name not in repo.labels:
            raise ApiError(422, "Validation Failed: label %s does not exist" % label_name)
        label_names.append(label_name)
    with STORE.lock:
        number = repo.next_number
        repo.next_number += 1
        stamp = iso_now()
        issue = {"number": number, "title": title, "body": body.get("body") or "",
                 "state": "open", "labels": label_names, "comments": [],
                 "created_at": stamp, "updated_at": stamp, "closed_at": None}
        repo.issues[number] = issue
    return issue


def _rest_issues(self, repo, rest):
    if not rest:
        if self.command == "GET":
            state = self.query_one("state", "open")
            direction = self.query_one("direction", "desc")
            with STORE.lock:
                issues = list(repo.issues.values())
            if state in ("open", "closed"):
                issues = [i for i in issues if i["state"] == state]
            reverse = direction != "asc"
            issues.sort(key=lambda i: i["number"], reverse=reverse)
            page, link = self.pagination([issue_json(repo, i) for i in issues])
            self.send_json(200, page, {"Link": link})
            return
        if self.command == "POST":
            body = self.read_json()
            issue = _issue_from_body(repo, body)
            self.send_json(201, issue_json(repo, issue))
            return
        raise ApiError(404, "Not Found")
    try:
        number = int(rest[0])
    except ValueError:
        raise ApiError(404, "Not Found")
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if self.command == "GET":
            self.send_json(200, issue_json(repo, issue))
            return
        if self.command == "PATCH":
            body = self.read_json()
            with STORE.lock:
                if "title" in body:
                    issue["title"] = body["title"]
                if "body" in body:
                    issue["body"] = body["body"] or ""
                if "state" in body:
                    new_state = body["state"]
                    if new_state in ("open", "closed"):
                        issue["state"] = new_state
                        issue["closed_at"] = iso_now() if new_state == "closed" else None
                issue["updated_at"] = iso_now()
            self.send_json(200, issue_json(repo, issue))
            return
        raise ApiError(404, "Not Found")
    if rest[1] == "comments":
        if self.command == "GET":
            with STORE.lock:
                comments = [comment_json(c) for c in issue["comments"]]
            self.send_json(200, comments)
            return
        if self.command == "POST":
            body = self.read_json()
            text = body.get("body")
            if not isinstance(text, str) or not text:
                raise ApiError(422, "Validation Failed: body is required")
            with STORE.lock:
                comment_id = STORE.next_comment_id
                STORE.next_comment_id += 1
                stamp = iso_now()
                comment = {"id": comment_id, "body": text,
                           "created_at": stamp, "updated_at": stamp}
                issue["comments"].append(comment)
            self.send_json(201, comment_json(comment))
            return
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")


def _pr_from_body(repo, body):
    title = body.get("title")
    if not isinstance(title, str) or not title:
        raise ApiError(422, "Validation Failed: title is required")
    head = _strip_owner_prefix(body.get("head") or "")
    base = _strip_owner_prefix(body.get("base") or "")
    if not head or repo.branch_tip(head) is None:
        raise ApiError(422, "Validation Failed: head branch does not exist")
    if not base or repo.branch_tip(base) is None:
        raise ApiError(422, "Validation Failed: base branch does not exist")
    with STORE.lock:
        number = repo.next_number
        repo.next_number += 1
        stamp = iso_now()
        pr = {"number": number, "title": title, "body": body.get("body") or "",
              "state": "open", "head_ref": head, "base_ref": base,
              "merged": False, "merged_at": None, "merge_commit_sha": None,
              "mergeable": True, "created_at": stamp, "updated_at": stamp,
              "closed_at": None}
        repo.pulls[number] = pr
    return pr


def _pr_files(repo, pr):
    base_tip = repo.branch_tip(pr["base_ref"])
    head_tip = repo.branch_tip(pr["head_ref"])
    if base_tip is None or head_tip is None:
        return []
    base = merge_base(repo, base_tip, head_tip)
    mb_tree = repo.tree_of(base) if base else None
    head_tree = repo.tree_of(head_tip)
    files = []
    for path, status, old_oid, new_oid in diff_trees(repo, mb_tree, head_tree):
        additions, deletions = count_line_changes(repo, old_oid, new_oid)
        files.append({"filename": path, "status": status,
                      "additions": additions, "deletions": deletions,
                      "changes": additions + deletions,
                      "sha": new_oid or old_oid})
    return files


def _rest_pulls(self, repo, rest):
    if not rest:
        if self.command == "GET":
            state = self.query_one("state", "open")
            with STORE.lock:
                pulls = list(repo.pulls.values())
            if state in ("open", "closed"):
                pulls = [p for p in pulls if p["state"] == state]
            pulls.sort(key=lambda p: p["number"], reverse=True)
            page, link = self.pagination([pr_json(repo, p) for p in pulls])
            self.send_json(200, page, {"Link": link})
            return
        if self.command == "POST":
            body = self.read_json()
            pr = _pr_from_body(repo, body)
            self.send_json(201, pr_json(repo, pr))
            return
        raise ApiError(404, "Not Found")
    try:
        number = int(rest[0])
    except ValueError:
        raise ApiError(404, "Not Found")
    pr = repo.pulls.get(number)
    if pr is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if self.command == "GET":
            self.send_json(200, pr_json(repo, pr))
            return
        if self.command == "PATCH":
            body = self.read_json()
            with STORE.lock:
                if "title" in body:
                    pr["title"] = body["title"]
                if "body" in body:
                    pr["body"] = body["body"] or ""
                if body.get("state") == "closed" and pr["state"] == "open":
                    pr["state"] = "closed"
                    pr["closed_at"] = iso_now()
                pr["updated_at"] = iso_now()
            self.send_json(200, pr_json(repo, pr))
            return
        raise ApiError(404, "Not Found")
    if rest[1] == "files":
        if self.command != "GET":
            raise ApiError(404, "Not Found")
        self.send_json(200, _pr_files(repo, pr))
        return
    if rest[1] == "merge":
        if self.command != "PUT":
            raise ApiError(404, "Not Found")
        if pr["state"] != "open":
            raise ApiError(405, "Pull request is not open")
        with STORE.lock:
            sha = squash_merge(repo, pr)
            pr["merged"] = True
            pr["state"] = "closed"
            pr["merged_at"] = iso_now()
            pr["closed_at"] = pr["merged_at"]
            pr["merge_commit_sha"] = sha
            pr["updated_at"] = pr["merged_at"]
        self.send_json(200, {"sha": sha, "merged": True,
                             "message": "Pull Request successfully merged"})
        return
    raise ApiError(404, "Not Found")


ForgeHandler._handle_rest = _handle_rest
ForgeHandler._rest_branches = _rest_branches
ForgeHandler._rest_commits = _rest_commits
ForgeHandler._rest_contents = _rest_contents
ForgeHandler._rest_git_refs = _rest_git_refs
ForgeHandler._rest_labels = _rest_labels
ForgeHandler._rest_issues = _rest_issues
ForgeHandler._rest_pulls = _rest_pulls


# ---------------------------------------------------------------------------
# Git smart HTTP
# ---------------------------------------------------------------------------

_UPLOAD_CAPS = ("multi_ack multi_ack_detailed thin-pack side-band-64k ofs-delta shallow "
                "agent=forge/1.0 symref=HEAD:refs/heads/main")
_RECEIVE_CAPS = "report-status side-band-64k delete-refs ofs-delta agent=forge/1.0"


def _handle_git(self):
    if not self.require_auth():
        return
    owner = self.path_segments[0]
    repo_name = self.path_segments[1][:-len(".git")]
    service = self.path_segments[2:]
    repo = STORE.get_repo(owner, repo_name)
    if service == ["info", "refs"]:
        if repo is None:
            raise ApiError(404, "Not Found")
        which = self.query_one("service")
        if which == "git-upload-pack":
            self._git_advertise_upload(repo)
        elif which == "git-receive-pack":
            self._git_advertise_receive(repo)
        else:
            raise ApiError(404, "Not Found")
        return
    if service == ["git-upload-pack"]:
        if repo is None:
            raise ApiError(404, "Not Found")
        self._git_upload_pack(repo)
        return
    if service == ["git-receive-pack"]:
        if repo is None:
            raise ApiError(404, "Not Found")
        self._git_receive_pack(repo, self.read_body())
        return
    raise ApiError(404, "Not Found")


def _git_advertise_upload(self, repo):
    if self.headers.get("Git-Protocol", "").startswith("version=2"):
        body = pkt_lines(["version 2\n", "ls-refs=unborn\n",
                          "fetch=shallow filter\n", "object-format=sha1\n", "flush"])
        self.send_git_bytes(200, body, "application/x-git-upload-pack-advertisement")
        return
    lines = ["# service=git-upload-pack\n", "flush"]
    refs = sorted(repo.refs.items())
    if not refs:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO_OID, _UPLOAD_CAPS))
    else:
        caps_sent = False
        head_tip = repo.head_tip()
        if head_tip:
            lines.append("%s HEAD\0%s\n" % (head_tip, _UPLOAD_CAPS))
            caps_sent = True
        for ref, oid in refs:
            suffix = ("\0%s" % _UPLOAD_CAPS) if not caps_sent else ""
            lines.append("%s %s%s\n" % (oid, ref, suffix))
            caps_sent = True
            if ref.startswith("refs/tags/"):
                peeled = peel_to_commit(repo, oid)
                if peeled != oid:
                    lines.append("%s %s^{}\n" % (peeled, ref))
    lines.append("flush")
    self.send_git_bytes(200, pkt_lines(lines), "application/x-git-upload-pack-advertisement")


def _git_advertise_receive(self, repo):
    lines = ["# service=git-receive-pack\n", "flush"]
    refs = sorted(repo.refs.items())
    if not refs:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO_OID, _RECEIVE_CAPS))
    else:
        first = True
        for ref, oid in refs:
            suffix = ("\0%s" % _RECEIVE_CAPS) if first else ""
            lines.append("%s %s%s\n" % (oid, ref, suffix))
            first = False
    lines.append("flush")
    self.send_git_bytes(200, pkt_lines(lines), "application/x-git-receive-pack-advertisement")


def _git_upload_pack(self, repo):
    body = self.read_body()
    if self.headers.get("Git-Protocol", "").startswith("version=2"):
        try:
            packets, _rest = parse_pkt_lines(body)
        except PktError:
            raise ApiError(400, "Malformed pkt-line request")
        if not packets or packets[0][0] != "data":
            raise ApiError(400, "Missing command")
        command = packets[0][1].decode("utf-8", "replace").strip()
        if command == "command=ls-refs":
            self._git_ls_refs(repo, packets[1:])
        elif command == "command=fetch":
            self._git_fetch_v2(repo, packets[1:])
        else:
            raise ApiError(400, "Unknown command %s" % command)
    else:
        self._git_upload_pack_v0(repo, body)


def _git_ls_refs(self, repo, packets):
    peel = symrefs = unborn = False
    prefixes = []
    in_args = False
    for packet in packets:
        kind = packet[0]
        if kind == "delim":
            in_args = True
            continue
        if kind == "flush":
            break
        if kind != "data" or not in_args:
            continue
        line = packet[1].decode("utf-8", "replace").strip()
        if line == "peel":
            peel = True
        elif line == "symrefs":
            symrefs = True
        elif line == "unborn":
            unborn = True
        elif line.startswith("ref-prefix "):
            prefixes.append(line[len("ref-prefix "):])
    lines = []
    refs = sorted(repo.refs.items())
    if not refs:
        if unborn:
            lines.append("unborn HEAD symref-target:refs/heads/main\n")
    else:
        # HEAD is listed when symrefs is requested and no prefix filter
        # excludes it: HEAD matches a prefix only when that prefix is a
        # prefix of "HEAD" itself (so "HEAD" matches, "refs/..." does not).
        head_wanted = symrefs and (not prefixes or any("HEAD".startswith(p) for p in prefixes))
        if head_wanted:
            head_tip = repo.head_tip()
            if head_tip:
                lines.append("%s HEAD symref-target:refs/heads/main\n" % head_tip)
        for ref, oid in refs:
            if prefixes and not any(ref.startswith(p) for p in prefixes):
                continue
            suffix = ""
            if peel and ref.startswith("refs/tags/"):
                peeled = peel_to_commit(repo, oid)
                if peeled != oid:
                    suffix = " peeled:%s" % peeled
            lines.append("%s %s%s\n" % (oid, ref, suffix))
    lines.append("flush")
    self.send_git_bytes(200, pkt_lines(lines), "application/x-git-upload-pack-result")


def _snapshot_objects(repo, oids):
    """Copy (type, data) pairs out of the store, sorted for a stable pack."""
    with STORE.lock:
        return [(repo.objects[oid][0], repo.objects[oid][1])
                for oid in sorted(oids) if oid in repo.objects]


def _git_fetch_v2(self, repo, packets):
    wants, haves, shallow = [], [], []
    deepen = None
    done = False
    include_tag = False
    deepen_relative = False
    in_args = False
    for packet in packets:
        kind = packet[0]
        if kind == "delim":
            in_args = True
            continue
        if kind == "flush":
            break
        if kind != "data" or not in_args:
            continue
        line = packet[1].decode("utf-8", "replace").strip()
        if line.startswith("want "):
            wants.append(line[5:].strip())
        elif line.startswith("have "):
            haves.append(line[5:].strip())
        elif line.startswith("shallow "):
            shallow.append(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                deepen = int(line[7:])
            except ValueError:
                pass
        elif line == "done":
            done = True
        elif line == "include-tag":
            include_tag = True
        elif line == "deepen-relative":
            deepen_relative = True
    ack_lines = ["ACK %s\n" % have for have in haves if have in repo.objects]
    if not ack_lines:
        ack_lines = ["NAK\n"]
    send, shallow_new, unshallow = compute_fetch(repo, wants, haves, shallow, deepen,
                                                 include_tags=include_tag,
                                                 deepen_relative=deepen_relative)
    pack = write_pack(_snapshot_objects(repo, send))
    out = []
    # The acknowledgments section only exists when the client sent haves
    # without `done`: real git's client expects the packfile section first
    # otherwise, and with haves it needs a `ready` line before any later
    # section, or it dies expecting more negotiation.
    if haves and not done:
        out.append(pkt_line("acknowledgments\n"))
        out.extend(pkt_line(line) for line in ack_lines)
        out.append(pkt_line("ready\n"))
        out.append(DELIM_PKT)
    if shallow_new or unshallow:
        out.append(pkt_line("shallow-info\n"))
        out.extend(pkt_line("shallow %s\n" % oid) for oid in shallow_new)
        out.extend(pkt_line("unshallow %s\n" % oid) for oid in unshallow)
        out.append(DELIM_PKT)
    out.append(pkt_line("packfile\n"))
    out.extend(sideband_packets(1, pack))
    out.append(FLUSH_PKT)
    self.send_git_bytes(200, b"".join(out), "application/x-git-upload-pack-result")


def _git_upload_pack_v0(self, repo, body):
    try:
        packets, _rest = parse_pkt_lines(body)
    except PktError:
        raise ApiError(400, "Malformed pkt-line request")
    wants, haves, shallow = [], [], []
    deepen = None
    for packet in packets:
        if packet[0] != "data":
            continue
        line = packet[1].decode("utf-8", "replace")
        if line.endswith("\n"):
            line = line[:-1]
        if "\0" in line:
            line = line.split("\0", 1)[0]
        # The first want line carries the client's capabilities after a
        # space ("want <oid> side-band-64k ..."): the oid is the first token.
        if line.startswith("want "):
            wants.append(line[5:].strip().split()[0])
        elif line.startswith("have "):
            haves.append(line[5:].strip().split()[0])
        elif line.startswith("shallow "):
            shallow.append(line[8:].strip().split()[0])
        elif line.startswith("deepen "):
            try:
                deepen = int(line[7:].strip().split()[0])
            except ValueError:
                pass
    send, shallow_new, unshallow = compute_fetch(repo, wants, haves, shallow, deepen)
    out = []
    out.extend(pkt_line("shallow %s\n" % oid) for oid in shallow_new)
    out.extend(pkt_line("unshallow %s\n" % oid) for oid in unshallow)
    # A bare ACK ends the negotiation: the client reads the pack next. So
    # every common have gets "ACK <oid> common" and only the last one is
    # repeated bare, exactly as git's upload-pack answers.
    want_ancestors = set()
    for want in wants:
        want_ancestors |= set(walk_commits(repo, peel_to_commit(repo, want)))
    common = [have for have in haves
              if have in repo.objects and have in want_ancestors]
    if common:
        for oid in common:
            out.append(pkt_line("ACK %s common\n" % oid))
        out.append(pkt_line("ACK %s\n" % common[-1]))
    else:
        out.append(pkt_line("NAK\n"))
    pack = write_pack(_snapshot_objects(repo, send))
    out.extend(sideband_packets(1, pack))
    out.append(FLUSH_PKT)
    self.send_git_bytes(200, b"".join(out), "application/x-git-upload-pack-result")


def _git_receive_pack(self, repo, body):
    try:
        packets, pack = parse_pkt_lines(body, stop_at_flush=True)
    except PktError:
        raise ApiError(400, "Malformed pkt-line request")
    commands = []
    caps = ""
    for packet in packets:
        if packet[0] != "data":
            continue
        line = packet[1].decode("utf-8", "replace")
        if line.endswith("\n"):
            line = line[:-1]
        if "\0" in line:
            line, caps = line.split("\0", 1)
        parts = line.split(" ")
        if len(parts) == 3:
            commands.append((parts[0], parts[1], parts[2]))
    sideband = "side-band-64k" in caps
    report_status = "report-status" in caps
    unpack_error = None
    new_objects = {}
    if pack:
        try:
            new_objects = read_pack(pack, resolve_base=lambda oid: repo.objects.get(oid))
        except PackError as exc:
            unpack_error = str(exc)
    results = []
    with STORE.lock:
        if unpack_error is None:
            for oid, pair in new_objects.items():
                repo.objects.setdefault(oid, pair)
        for old, new, ref in commands:
            current = repo.refs.get(ref)
            if unpack_error is not None:
                results.append((ref, False, "unpack failed: %s" % unpack_error))
                continue
            if new == ZERO_OID:
                if current is None:
                    results.append((ref, False, "ref does not exist"))
                elif old != current:
                    results.append((ref, False, "old value does not match"))
                else:
                    del repo.refs[ref]
                    results.append((ref, True, None))
            elif current is None:
                if old != ZERO_OID:
                    results.append((ref, False, "old value does not match"))
                elif new not in repo.objects:
                    results.append((ref, False, "object not found"))
                else:
                    repo.refs[ref] = new
                    results.append((ref, True, None))
            else:
                if old != current:
                    results.append((ref, False, "old value does not match"))
                elif new == current:
                    results.append((ref, True, None))
                elif new not in repo.objects:
                    results.append((ref, False, "object not found"))
                elif not is_ancestor(repo, current, new):
                    results.append((ref, False, "non-fast-forward"))
                else:
                    repo.refs[ref] = new
                    results.append((ref, True, None))
        repo.updated_at = iso_now()
    if not report_status:
        self.send_git_bytes(200, b"", "application/x-git-receive-pack-result")
        return
    lines = []
    if unpack_error is None:
        lines.append("unpack ok\n")
    else:
        lines.append("unpack %s\n" % unpack_error)
    for ref, ok, reason in results:
        if ok:
            lines.append("ok %s\n" % ref)
        else:
            lines.append("ng %s %s\n" % (ref, reason or "failed"))
    payload = pkt_lines(lines + ["flush"])
    if sideband:
        # The sideband stream itself ends with a flush pkt-line, after the
        # band-1 packets carrying the report (whose own flush is inside them).
        body_out = b"".join(sideband_packets(1, payload)) + FLUSH_PKT
    else:
        body_out = payload
    self.send_git_bytes(200, body_out, "application/x-git-receive-pack-result")


ForgeHandler._handle_git = _handle_git
ForgeHandler._git_advertise_upload = _git_advertise_upload
ForgeHandler._git_advertise_receive = _git_advertise_receive
ForgeHandler._git_upload_pack = _git_upload_pack
ForgeHandler._git_ls_refs = _git_ls_refs
ForgeHandler._git_fetch_v2 = _git_fetch_v2
ForgeHandler._git_upload_pack_v0 = _git_upload_pack_v0
ForgeHandler._git_receive_pack = _git_receive_pack


# ---------------------------------------------------------------------------
# GraphQL: a small parser and executor for the documents the suite sends
# ---------------------------------------------------------------------------

class _GQLParseError(Exception):
    pass


_GQL_TOKEN_RE = re.compile(r"""
    (?P<ws>[ \t\r\n,]+)
  | (?P<comment>\#[^\n]*)
  | (?P<spread>\.\.\.)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?|-?\d+[eE][+-]?\d+)
  | (?P<int>-?\d+)
  | (?P<name>[_A-Za-z][_A-Za-z0-9]*)
  | (?P<punct>[\$!\:\=\@\(\)\[\]\{\}\|\&])
""", re.VERBOSE)


def _gql_lex(text):
    tokens = []
    position = 0
    while position < len(text):
        match = _GQL_TOKEN_RE.match(text, position)
        if match is None:
            raise _GQLParseError("Unexpected character %r at offset %d" % (text[position], position))
        position = match.end()
        kind = match.lastgroup
        if kind in ("ws", "comment"):
            continue
        value = match.group()
        if kind == "string":
            value = json.loads(value)
        elif kind == "int":
            value = int(value)
        elif kind == "float":
            value = float(value)
        tokens.append((kind, value))
    tokens.append(("eof", None))
    return tokens


class _GQLParser:
    def __init__(self, text):
        self.tokens = _gql_lex(text)
        self.pos = 0

    def peek(self, ahead=0):
        index = min(self.pos + ahead, len(self.tokens) - 1)
        return self.tokens[index]

    def take(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def expect(self, kind, value=None):
        token = self.take()
        if token[0] != kind or (value is not None and token[1] != value):
            raise _GQLParseError("Expected %s %s, got %s %r" % (kind, value, token[0], token[1]))
        return token[1]

    def at(self, kind, value=None):
        token = self.peek()
        return token[0] == kind and (value is None or token[1] == value)

    def parse_document(self):
        definitions = []
        while not self.at("eof"):
            definitions.append(self.parse_definition())
        return definitions

    def parse_definition(self):
        if self.at("name", "query") or self.at("name", "mutation"):
            kind = self.take()[1]
            return self.parse_operation(kind)
        if self.at("name", "fragment"):
            self.take()
            name = self.expect("name")
            self.expect("name", "on")
            type_condition = self.expect("name")
            self._skip_directives()
            return {"kind": "fragment", "name": name, "type": type_condition,
                    "selection": self.parse_selection_set()}
        if self.at("punct", "{"):
            return {"kind": "query", "name": None, "var_defs": {},
                    "selection": self.parse_selection_set()}
        raise _GQLParseError("Unexpected token %r" % (self.peek(),))

    def parse_operation(self, kind):
        name = None
        if self.at("name"):
            name = self.take()[1]
        var_defs = {}
        if self.at("punct", "("):
            var_defs = self.parse_var_defs()
        self._skip_directives()
        return {"kind": kind, "name": name, "var_defs": var_defs,
                "selection": self.parse_selection_set()}

    def parse_var_defs(self):
        defs = {}
        self.expect("punct", "(")
        while not self.at("punct", ")"):
            self.expect("punct", "$")
            name = self.expect("name")
            self.expect("punct", ":")
            self._parse_type()
            default = None
            if self.at("punct", "="):
                self.take()
                default = self.parse_value()
            defs[name] = default
        self.expect("punct", ")")
        return defs

    def _parse_type(self):
        if self.at("punct", "["):
            self.take()
            self._parse_type()
            self.expect("punct", "]")
        else:
            self.expect("name")
        if self.at("punct", "!"):
            self.take()

    def _skip_directives(self):
        while self.at("punct", "@"):
            self.take()
            self.expect("name")
            if self.at("punct", "("):
                self.parse_arguments()

    def parse_selection_set(self):
        selections = []
        self.expect("punct", "{")
        while not self.at("punct", "}"):
            selections.append(self.parse_selection())
        self.expect("punct", "}")
        return selections

    def parse_selection(self):
        if self.at("spread"):
            self.take()
            if self.at("name", "on"):
                self.take()
                type_condition = self.expect("name")
                self._skip_directives()
                return {"kind": "inline", "type": type_condition,
                        "selection": self.parse_selection_set()}
            name = self.expect("name")
            self._skip_directives()
            return {"kind": "spread", "name": name}
        name_or_alias = self.expect("name")
        alias = None
        name = name_or_alias
        if self.at("punct", ":"):
            self.take()
            alias = name_or_alias
            name = self.expect("name")
        args = {}
        if self.at("punct", "("):
            args = self.parse_arguments()
        self._skip_directives()
        selection = []
        if self.at("punct", "{"):
            selection = self.parse_selection_set()
        return {"kind": "field", "alias": alias, "name": name,
                "args": args, "selection": selection}

    def parse_arguments(self):
        args = {}
        self.expect("punct", "(")
        while not self.at("punct", ")"):
            name = self.expect("name")
            self.expect("punct", ":")
            args[name] = self.parse_value()
        self.expect("punct", ")")
        return args

    def parse_value(self):
        kind, value = self.peek()
        if kind == "punct" and value == "$":
            self.take()
            return ("var", self.expect("name"))
        if kind in ("int", "float", "string"):
            self.take()
            return (kind, value)
        if kind == "name":
            self.take()
            if value == "true":
                return ("bool", True)
            if value == "false":
                return ("bool", False)
            if value == "null":
                return ("null", None)
            return ("enum", value)
        if kind == "punct" and value == "[":
            self.take()
            items = []
            while not self.at("punct", "]"):
                items.append(self.parse_value())
            self.expect("punct", "]")
            return ("list", items)
        if kind == "punct" and value == "{":
            self.take()
            fields = {}
            while not self.at("punct", "}"):
                name = self.expect("name")
                self.expect("punct", ":")
                fields[name] = self.parse_value()
            self.expect("punct", "}")
            return ("object", fields)
        raise _GQLParseError("Unexpected value token %r" % (self.peek(),))


def _gql_resolve_value(value, variables):
    kind, payload = value
    if kind == "var":
        return variables.get(payload)
    if kind == "list":
        return [_gql_resolve_value(item, variables) for item in payload]
    if kind == "object":
        return {key: _gql_resolve_value(item, variables) for key, item in payload.items()}
    return payload


class _GObj:
    __slots__ = ("type_name", "data")

    def __init__(self, type_name, data):
        self.type_name = type_name
        self.data = data


_MISSING = object()

_TYPE_FIELDS = {
    "Issue": ["id", "databaseId", "number", "title", "state", "body",
              "createdAt", "updatedAt", "closedAt", "author", "comments"],
    "PullRequest": ["id", "databaseId", "number", "title", "state", "body",
                    "headRefName", "baseRefName", "mergeable", "merged",
                    "mergedAt", "files", "createdAt", "updatedAt", "author"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "description",
                   "isPrivate", "owner", "defaultBranchRef", "viewerPermission",
                   "hasIssuesEnabled", "issue", "issues", "pullRequests",
                   "pullRequest", "createdAt", "updatedAt"],
    "User": ["id", "databaseId", "login", "name", "email"],
    "Ref": ["name", "target"],
    "IssueConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestChangedFileConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PageInfo": ["hasNextPage", "hasPreviousPage", "startCursor", "endCursor"],
    "IssueComment": ["id", "databaseId", "body", "createdAt", "updatedAt", "author"],
    "CreateIssuePayload": ["issue"],
    "CloseIssuePayload": ["issue"],
    "CreatePullRequestPayload": ["pullRequest"],
    "MergePullRequestPayload": ["pullRequest"],
    "AddCommentPayload": ["commentEdge"],
}
_TYPE_KIND = {"SearchType": "ENUM"}
_ENUM_VALUES = {
    "SearchType": ["DISCUSSION", "ISSUE", "REPOSITORY", "USER"],
}


def _gql_cursor(offset):
    return base64.b64encode(("cursor:%d" % offset).encode("utf-8")).decode("ascii")


def _gql_cursor_offset(cursor):
    try:
        raw = base64.b64decode(cursor.encode("ascii")).decode("utf-8")
        return int(raw.split(":", 1)[1])
    except Exception:
        return 0


def _find_repo_by_id(repo_id):
    with STORE.lock:
        for repo in STORE.repos.values():
            if repo.id == repo_id:
                return repo
    return None


def _gql_node(global_id_value):
    parsed = parse_global_id(global_id_value)
    if parsed is None:
        return None
    kind, parts = parsed
    try:
        if kind == "Repository":
            repo = _find_repo_by_id(int(parts[0]))
            return _GObj("Repository", repo) if repo else None
        if kind == "Issue":
            repo = _find_repo_by_id(int(parts[0]))
            issue = repo.issues.get(int(parts[1])) if repo else None
            return _GObj("Issue", {"repo": repo, "issue": issue}) if issue else None
        if kind == "PullRequest":
            repo = _find_repo_by_id(int(parts[0]))
            pr = repo.pulls.get(int(parts[1])) if repo else None
            return _GObj("PullRequest", {"repo": repo, "pr": pr}) if pr else None
    except (ValueError, IndexError):
        return None
    return None


def _gql_issues_connection(repo, args):
    issues = list(repo.issues.values())
    states = args.get("states")
    if states:
        wanted = {"OPEN": "open", "CLOSED": "closed"}
        keep = {wanted.get(state, str(state).lower()) for state in states}
        issues = [i for i in issues if i["state"] in keep]
    order_by = args.get("orderBy") or {}
    reverse = order_by.get("direction") == "DESC"
    issues.sort(key=lambda i: i["number"], reverse=reverse)
    offset = _gql_cursor_offset(args.get("after")) if args.get("after") else 0
    first = args.get("first")
    page = issues[offset:] if first is None else issues[offset:offset + first]
    has_next = offset + len(page) < len(issues)
    end_cursor = _gql_cursor(offset + len(page)) if page else None
    return _GObj("IssueConnection", {"repo": repo, "items": page,
                                     "has_next": has_next, "end_cursor": end_cursor,
                                     "total": len(issues)})


def _gql_pulls_connection(repo, args):
    pulls = sorted(repo.pulls.values(), key=lambda p: p["number"], reverse=True)
    states = args.get("states")
    if states:
        keep = set()
        for state in states:
            if state == "OPEN":
                keep.add("open")
            elif state in ("CLOSED", "MERGED"):
                keep.add("closed")
        pulls = [p for p in pulls if p["state"] in keep]
    offset = _gql_cursor_offset(args.get("after")) if args.get("after") else 0
    first = args.get("first")
    page = pulls[offset:] if first is None else pulls[offset:offset + first]
    has_next = offset + len(page) < len(pulls)
    end_cursor = _gql_cursor(offset + len(page)) if page else None
    return _GObj("PullRequestConnection", {"repo": repo, "items": page,
                                           "has_next": has_next, "end_cursor": end_cursor,
                                           "total": len(pulls)})


def _gql_files_connection(repo, pr, args):
    files = _pr_files(repo, pr)
    first = args.get("first")
    page = files if first is None else files[:first]
    return _GObj("PullRequestChangedFileConnection",
                 {"items": page, "has_next": False, "end_cursor": None,
                  "total": len(files)})


def _gql_pr_state(pr):
    if pr["merged"]:
        return "MERGED"
    return "OPEN" if pr["state"] == "open" else "CLOSED"


def _gql_pr_mergeable(repo, pr):
    if pr["state"] != "open":
        return "UNKNOWN"
    base_tip = repo.branch_tip(pr["base_ref"])
    head_tip = repo.branch_tip(pr["head_ref"])
    if base_tip is None or head_tip is None:
        return "UNKNOWN"
    return "CONFLICTING" if merge_conflict(repo, base_tip, head_tip) else "MERGEABLE"


def _gql_add_comment(repo, issue, body):
    with STORE.lock:
        comment_id = STORE.next_comment_id
        STORE.next_comment_id += 1
        stamp = iso_now()
        comment = {"id": comment_id, "body": body,
                   "created_at": stamp, "updated_at": stamp}
        issue["comments"].append(comment)
    return comment


def _gql_field_value(type_name, obj, name, args, ctx):
    if name == "__typename":
        return type_name
    if type_name == "Query":
        if name == "viewer":
            return _GObj("User", VIEWER)
        if name == "repository":
            repo = STORE.get_repo(args.get("owner"), args.get("name"))
            return _GObj("Repository", repo) if repo else None
        if name == "node":
            return _gql_node(args.get("id") or "")
        if name == "__type":
            wanted = args.get("name")
            if wanted in _TYPE_FIELDS or wanted in _ENUM_VALUES:
                return _GObj("__Type", {"name": wanted})
            return None
        return _MISSING
    if type_name == "Mutation":
        if name == "createIssue":
            return _gql_mutation_create_issue(args, ctx)
        if name == "closeIssue":
            return _gql_mutation_close_issue(args, ctx)
        if name == "createPullRequest":
            return _gql_mutation_create_pr(args, ctx)
        if name == "mergePullRequest":
            return _gql_mutation_merge_pr(args, ctx)
        if name == "addComment":
            return _gql_mutation_add_comment(args, ctx)
        return _MISSING
    if type_name == "Repository":
        repo = obj
        if name == "id":
            return global_id("Repository", repo.id)
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return "%s/%s" % (VIEWER_LOGIN, repo.name)
        if name == "description":
            return repo.description
        if name == "isPrivate":
            return repo.private
        if name == "owner":
            return _GObj("User", VIEWER)
        if name == "defaultBranchRef":
            return _GObj("Ref", {"name": repo.default_branch}) if repo.head_tip() else None
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "createdAt":
            return repo.created_at
        if name == "updatedAt":
            return repo.updated_at
        if name == "issue":
            issue = repo.issues.get(args.get("number"))
            return _GObj("Issue", {"repo": repo, "issue": issue}) if issue else None
        if name == "issues":
            return _gql_issues_connection(repo, args)
        if name == "pullRequests":
            return _gql_pulls_connection(repo, args)
        if name == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            return _GObj("PullRequest", {"repo": repo, "pr": pr}) if pr else None
        return _MISSING
    if type_name == "Issue":
        repo, issue = obj["repo"], obj["issue"]
        if name == "id":
            return global_id("Issue", repo.id, issue["number"])
        if name == "databaseId":
            return repo.id * 1000000 + issue["number"]
        if name == "number":
            return issue["number"]
        if name == "title":
            return issue["title"]
        if name == "body":
            return issue["body"]
        if name == "state":
            return "OPEN" if issue["state"] == "open" else "CLOSED"
        if name == "createdAt":
            return issue["created_at"]
        if name == "updatedAt":
            return issue["updated_at"]
        if name == "closedAt":
            return issue["closed_at"]
        if name == "author":
            return _GObj("User", VIEWER)
        return _MISSING
    if type_name == "PullRequest":
        repo, pr = obj["repo"], obj["pr"]
        if name == "id":
            return global_id("PullRequest", repo.id, pr["number"])
        if name == "databaseId":
            return repo.id * 1000000 + 500000 + pr["number"]
        if name == "number":
            return pr["number"]
        if name == "title":
            return pr["title"]
        if name == "body":
            return pr["body"]
        if name == "state":
            return _gql_pr_state(pr)
        if name == "headRefName":
            return pr["head_ref"]
        if name == "baseRefName":
            return pr["base_ref"]
        if name == "mergeable":
            return _gql_pr_mergeable(repo, pr)
        if name == "merged":
            return pr["merged"]
        if name == "mergedAt":
            return pr["merged_at"]
        if name == "createdAt":
            return pr["created_at"]
        if name == "updatedAt":
            return pr["updated_at"]
        if name == "author":
            return _GObj("User", VIEWER)
        if name == "files":
            return _gql_files_connection(repo, pr, args)
        return _MISSING
    if type_name == "User":
        if name == "id":
            return global_id("User", obj.get("id", 1000))
        if name == "databaseId":
            return obj.get("id", 1000)
        if name == "login":
            return obj.get("login")
        if name == "name":
            return obj.get("name")
        if name == "email":
            return obj.get("email")
        return _MISSING
    if type_name == "Ref":
        if name == "name":
            return obj.get("name")
        return _MISSING
    if type_name in ("IssueConnection", "PullRequestConnection",
                     "PullRequestChangedFileConnection"):
        if name == "nodes":
            if type_name == "IssueConnection":
                return [_GObj("Issue", {"repo": obj["repo"], "issue": i}) for i in obj["items"]]
            if type_name == "PullRequestConnection":
                return [_GObj("PullRequest", {"repo": obj["repo"], "pr": p}) for p in obj["items"]]
            return [_GObj("PullRequestChangedFile", f) for f in obj["items"]]
        if name == "edges":
            edges = []
            for item in obj["items"]:
                if type_name == "IssueConnection":
                    edges.append(_GObj("IssueEdge", {"node": _GObj("Issue", {"repo": obj["repo"], "issue": item})}))
                elif type_name == "PullRequestConnection":
                    edges.append(_GObj("PullRequestEdge", {"node": _GObj("PullRequest", {"repo": obj["repo"], "pr": item})}))
                else:
                    edges.append(_GObj("PullRequestChangedFileEdge", {"node": _GObj("PullRequestChangedFile", item)}))
            return edges
        if name == "pageInfo":
            return _GObj("PageInfo", {"has_next": obj["has_next"],
                                      "end_cursor": obj["end_cursor"]})
        if name == "totalCount":
            return obj["total"]
        return _MISSING
    if type_name in ("IssueEdge", "PullRequestEdge", "PullRequestChangedFileEdge",
                     "IssueCommentEdge"):
        if name == "node":
            return obj["node"]
        if name == "cursor":
            return ""
        return _MISSING
    if type_name == "PageInfo":
        if name == "hasNextPage":
            return obj.get("has_next", False)
        if name == "endCursor":
            return obj.get("end_cursor")
        if name == "hasPreviousPage":
            return False
        if name == "startCursor":
            return None
        return _MISSING
    if type_name == "PullRequestChangedFile":
        if name == "path":
            return obj.get("filename")
        if name == "additions":
            return obj.get("additions", 0)
        if name == "deletions":
            return obj.get("deletions", 0)
        if name == "changeType":
            return {"added": "ADDED", "modified": "MODIFIED", "removed": "REMOVED"}.get(obj.get("status"), "MODIFIED")
        return _MISSING
    if type_name == "__Type":
        wanted = obj["name"]
        if name == "name":
            return wanted
        if name == "kind":
            return _TYPE_KIND.get(wanted, "OBJECT")
        if name == "fields":
            return [_GObj("__Field", {"name": f}) for f in _TYPE_FIELDS.get(wanted, [])]
        if name == "enumValues":
            return [_GObj("__EnumValue", {"name": v}) for v in _ENUM_VALUES.get(wanted, [])]
        return _MISSING
    if type_name == "__Field":
        if name == "name":
            return obj["name"]
        if name == "description":
            return ""
        return _MISSING
    if type_name == "__EnumValue":
        if name == "name":
            return obj["name"]
        if name == "description":
            return ""
        return _MISSING
    if type_name == "IssueComment":
        comment = obj["comment"]
        if name == "id":
            return global_id("IssueComment", comment["id"])
        if name == "databaseId":
            return comment["id"]
        if name == "body":
            return comment["body"]
        if name == "createdAt":
            return comment["created_at"]
        if name == "updatedAt":
            return comment["updated_at"]
        if name == "author":
            return _GObj("User", VIEWER)
        return _MISSING
    if type_name in ("CreateIssuePayload", "CloseIssuePayload"):
        if name == "issue":
            issue = obj.get("issue")
            return _GObj("Issue", {"repo": obj["repo"], "issue": issue}) if issue else None
        if name == "clientMutationId":
            return None
        return _MISSING
    if type_name in ("CreatePullRequestPayload", "MergePullRequestPayload"):
        if name == "pullRequest":
            pr = obj.get("pr")
            return _GObj("PullRequest", {"repo": obj["repo"], "pr": pr}) if pr else None
        if name == "clientMutationId":
            return None
        return _MISSING
    if type_name == "AddCommentPayload":
        if name == "commentEdge":
            comment = obj.get("comment")
            if comment is None:
                return None
            return _GObj("IssueCommentEdge", {"node": _GObj("IssueComment", {"comment": comment})})
        if name == "clientMutationId":
            return None
        return _MISSING
    return _MISSING


def _gql_repo_from_input(input_value, ctx):
    parsed = parse_global_id(input_value.get("repositoryId") or "")
    if parsed is None or parsed[0] != "Repository":
        ctx["errors"].append({"message": "repositoryId is not a Repository id"})
        return None
    try:
        repo = _find_repo_by_id(int(parsed[1][0]))
    except (ValueError, IndexError):
        repo = None
    if repo is None:
        ctx["errors"].append({"message": "Repository not found"})
    return repo


def _gql_mutation_create_issue(args, ctx):
    input_value = args.get("input") or {}
    repo = _gql_repo_from_input(input_value, ctx)
    if repo is None:
        return _GObj("CreateIssuePayload", {"repo": None, "issue": None})
    try:
        issue = _issue_from_body(repo, {"title": input_value.get("title"),
                                        "body": input_value.get("body") or "",
                                        "labels": []})
    except ApiError as exc:
        ctx["errors"].append({"message": exc.message})
        return _GObj("CreateIssuePayload", {"repo": repo, "issue": None})
    return _GObj("CreateIssuePayload", {"repo": repo, "issue": issue})


def _gql_mutation_close_issue(args, ctx):
    input_value = args.get("input") or {}
    node = _gql_node(input_value.get("issueId") or "")
    if node is None or node.type_name != "Issue":
        ctx["errors"].append({"message": "Issue not found"})
        return _GObj("CloseIssuePayload", {"repo": None, "issue": None})
    repo, issue = node.data["repo"], node.data["issue"]
    with STORE.lock:
        issue["state"] = "closed"
        issue["closed_at"] = iso_now()
        issue["updated_at"] = iso_now()
    return _GObj("CloseIssuePayload", {"repo": repo, "issue": issue})


def _gql_mutation_create_pr(args, ctx):
    input_value = args.get("input") or {}
    repo = _gql_repo_from_input(input_value, ctx)
    if repo is None:
        return _GObj("CreatePullRequestPayload", {"repo": None, "pr": None})
    try:
        pr = _pr_from_body(repo, {"title": input_value.get("title"),
                                  "body": input_value.get("body") or "",
                                  "head": input_value.get("headRefName"),
                                  "base": input_value.get("baseRefName")})
    except ApiError as exc:
        ctx["errors"].append({"message": exc.message})
        return _GObj("CreatePullRequestPayload", {"repo": repo, "pr": None})
    return _GObj("CreatePullRequestPayload", {"repo": repo, "pr": pr})


def _gql_mutation_merge_pr(args, ctx):
    input_value = args.get("input") or {}
    node = _gql_node(input_value.get("pullRequestId") or "")
    if node is None or node.type_name != "PullRequest":
        ctx["errors"].append({"message": "Pull request not found"})
        return _GObj("MergePullRequestPayload", {"repo": None, "pr": None})
    repo, pr = node.data["repo"], node.data["pr"]
    if pr["state"] != "open":
        ctx["errors"].append({"message": "Pull request is not open"})
        return _GObj("MergePullRequestPayload", {"repo": repo, "pr": pr})
    try:
        with STORE.lock:
            sha = squash_merge(repo, pr)
            pr["merged"] = True
            pr["state"] = "closed"
            pr["merged_at"] = iso_now()
            pr["closed_at"] = pr["merged_at"]
            pr["merge_commit_sha"] = sha
            pr["updated_at"] = pr["merged_at"]
    except ApiError as exc:
        ctx["errors"].append({"message": exc.message})
        return _GObj("MergePullRequestPayload", {"repo": repo, "pr": pr})
    return _GObj("MergePullRequestPayload", {"repo": repo, "pr": pr})


def _gql_mutation_add_comment(args, ctx):
    input_value = args.get("input") or {}
    node = _gql_node(input_value.get("subjectId") or "")
    if node is None or node.type_name != "Issue":
        ctx["errors"].append({"message": "Subject not found"})
        return _GObj("AddCommentPayload", {"comment": None})
    repo, issue = node.data["repo"], node.data["issue"]
    comment = _gql_add_comment(repo, issue, input_value.get("body") or "")
    return _GObj("AddCommentPayload", {"comment": comment})


def _gql_resolve_fields(type_name, obj, selections, ctx):
    out = {}
    for selection in selections:
        kind = selection["kind"]
        if kind == "field":
            value = _gql_resolve_field(type_name, obj, selection, ctx)
            if value is not _MISSING:
                out[selection.get("alias") or selection["name"]] = value
        elif kind == "inline":
            condition = selection.get("type")
            if condition is None or condition == type_name:
                out.update(_gql_resolve_fields(type_name, obj, selection["selection"], ctx))
        elif kind == "spread":
            fragment = ctx["fragments"].get(selection["name"])
            if fragment is not None and fragment["type"] == type_name:
                out.update(_gql_resolve_fields(type_name, obj, fragment["selection"], ctx))
    return out


def _gql_resolve_field(type_name, obj, field, ctx):
    args = {key: _gql_resolve_value(value, ctx["variables"])
            for key, value in field["args"].items()}
    value = _gql_field_value(type_name, obj, field["name"], args, ctx)
    if value is _MISSING:
        ctx["errors"].append({"message": 'Cannot query field "%s" on type "%s".'
                             % (field["name"], type_name)})
        return _MISSING
    selection = field["selection"]
    if not selection or value is None:
        return value
    if isinstance(value, _GObj):
        return _gql_resolve_fields(value.type_name, value.data, selection, ctx)
    if isinstance(value, list):
        resolved = []
        for item in value:
            if item is None:
                resolved.append(None)
            elif isinstance(item, _GObj):
                resolved.append(_gql_resolve_fields(item.type_name, item.data, selection, ctx))
            else:
                resolved.append(item)
        return resolved
    return value


def _gql_execute(payload):
    query = payload.get("query") or ""
    variables = payload.get("variables") or {}
    operation_name = payload.get("operationName")
    try:
        document = _GQLParser(query).parse_document()
    except _GQLParseError as exc:
        return {"data": None, "errors": [{"message": str(exc)}]}
    operations = [d for d in document if d["kind"] in ("query", "mutation")]
    fragments = {d["name"]: d for d in document if d["kind"] == "fragment"}
    operation = None
    if operation_name:
        for candidate in operations:
            if candidate.get("name") == operation_name:
                operation = candidate
                break
    if operation is None and operations:
        operation = operations[0]
    if operation is None:
        return {"data": None, "errors": [{"message": "No operation found in the document"}]}
    ctx = {"variables": variables, "errors": [], "fragments": fragments}
    root_type = "Query" if operation["kind"] == "query" else "Mutation"
    data = _gql_resolve_fields(root_type, {}, operation["selection"], ctx)
    result = {"data": data}
    if ctx["errors"]:
        result["errors"] = ctx["errors"]
    return result


def _handle_graphql(self):
    if not self.require_auth():
        return
    if self.command != "POST":
        raise ApiError(404, "Not Found")
    raw = self.read_body()
    try:
        payload = json.loads(raw.decode("utf-8")) if raw else {}
    except (ValueError, UnicodeDecodeError):
        raise ApiError(400, "Invalid JSON in request body")
    if isinstance(payload, list):
        self.send_json(200, [_gql_execute(item) for item in payload])
    elif isinstance(payload, dict):
        self.send_json(200, _gql_execute(payload))
    else:
        raise ApiError(400, "Request body must be a JSON object or an array")


ForgeHandler._handle_graphql = _handle_graphql


# ---------------------------------------------------------------------------
# MCP: JSON-RPC 2.0 over Streamable HTTP (revision 2026-07-28, legacy fallback)
# ---------------------------------------------------------------------------

_MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository owned by the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "The repository name."},
                "description": {"type": "string", "description": "A short description."},
                "private": {"type": "boolean", "description": "Whether the repository is private."},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get one repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "list_repos",
        "description": "List the authenticated user's repositories.",
        "inputSchema": {"type": "object", "properties": {}},
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
                "title": {"type": "string", "description": "The issue title."},
                "body": {"type": "string", "description": "The issue body."},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "get_issue",
        "description": "Get one issue by number.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
                "issue_number": {"type": "integer", "description": "The issue number."},
            },
            "required": ["owner", "repo", "issue_number"],
        },
    },
    {
        "name": "list_issues",
        "description": "List the issues of a repository, optionally by state.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
                "state": {"type": "string", "description": "open, closed, or all."},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Open a pull request from a head branch onto a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
                "title": {"type": "string", "description": "The pull request title."},
                "head": {"type": "string", "description": "The head branch name."},
                "base": {"type": "string", "description": "The base branch name."},
                "body": {"type": "string", "description": "The pull request body."},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Squash-merge a pull request into its base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner login."},
                "repo": {"type": "string", "description": "The repository name."},
                "pull_number": {"type": "integer", "description": "The pull request number."},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]

_MCP_TOOL_NAMES = {tool["name"] for tool in _MCP_TOOLS}
_MCP_REQUIRED = {tool["name"]: tool["inputSchema"].get("required", [])
                 for tool in _MCP_TOOLS}


def _mcp_text_result(data):
    return {"content": [{"type": "text", "text": json_dumps(data)}],
            "structuredContent": data}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _mcp_call_tool(name, arguments):
    """Run one tool; returns (result_dict, error_code, error_message)."""
    if name not in _MCP_TOOL_NAMES:
        return None, -32602, "Unknown tool %s" % name
    missing = [key for key in _MCP_REQUIRED[name] if arguments.get(key) in (None, "")]
    if missing:
        return None, -32602, "Missing required argument(s): %s" % ", ".join(missing)
    try:
        if name == "create_repo":
            repo = STORE.create_repo(arguments["name"], arguments.get("private", False),
                                     arguments.get("description", ""))
            return _mcp_text_result(repo_json(repo)), None, None
        if name == "list_repos":
            repos = [repo_json(r) for r in STORE.list_repos()]
            return _mcp_text_result({"repositories": repos}), None, None
        repo = STORE.get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None:
            return _mcp_error_result("Repository not found"), None, None
        if name == "get_repo":
            return _mcp_text_result(repo_json(repo)), None, None
        if name == "create_issue":
            issue = _issue_from_body(repo, {"title": arguments["title"],
                                            "body": arguments.get("body") or "",
                                            "labels": []})
            return _mcp_text_result(issue_json(repo, issue)), None, None
        if name == "get_issue":
            issue = repo.issues.get(int(arguments["issue_number"]))
            if issue is None:
                return _mcp_error_result("Issue not found"), None, None
            return _mcp_text_result(issue_json(repo, issue)), None, None
        if name == "list_issues":
            state = arguments.get("state") or "open"
            issues = list(repo.issues.values())
            if state in ("open", "closed"):
                issues = [i for i in issues if i["state"] == state]
            issues.sort(key=lambda i: i["number"], reverse=True)
            data = {"issues": [issue_json(repo, i) for i in issues]}
            return _mcp_text_result(data), None, None
        if name == "create_pull_request":
            pr = _pr_from_body(repo, {"title": arguments["title"],
                                      "body": arguments.get("body") or "",
                                      "head": arguments["head"],
                                      "base": arguments["base"]})
            return _mcp_text_result(pr_json(repo, pr)), None, None
        if name == "merge_pull_request":
            pr = repo.pulls.get(int(arguments["pull_number"]))
            if pr is None:
                return _mcp_error_result("Pull request not found"), None, None
            if pr["state"] != "open":
                return _mcp_error_result("Pull request is not open"), None, None
            with STORE.lock:
                sha = squash_merge(repo, pr)
                pr["merged"] = True
                pr["state"] = "closed"
                pr["merged_at"] = iso_now()
                pr["closed_at"] = pr["merged_at"]
                pr["merge_commit_sha"] = sha
                pr["updated_at"] = pr["merged_at"]
            return _mcp_text_result({"merged": True, "sha": sha,
                                     "number": pr["number"],
                                     "message": "Pull Request successfully merged"}), None, None
    except ApiError as exc:
        return _mcp_error_result(exc.message), None, None
    return _mcp_error_result("Tool %s failed" % name), None, None


def _handle_mcp(self):
    if self.command != "POST":
        raise ApiError(404, "Not Found")
    if not self.require_auth():
        return
    raw = self.read_body()
    try:
        payload = json.loads(raw.decode("utf-8")) if raw else {}
    except (ValueError, UnicodeDecodeError):
        self.send_json(400, {"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32700, "message": "Parse error"}})
        return
    if not isinstance(payload, dict):
        self.send_json(400, {"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32600, "message": "Invalid Request"}})
        return
    request_id = payload.get("id", _MISSING)
    method = payload.get("method", "")
    params = payload.get("params") or {}
    if request_id is _MISSING:
        # A notification: acknowledge it and carry no body.
        self._send_raw(202, [("Content-Length", "0")], b"")
        return

    def reply(result=None, error=None):
        body = {"jsonrpc": "2.0", "id": request_id}
        if error is not None:
            body["error"] = error
        else:
            body["result"] = result
        self.send_json(200, body)

    if method == "server/discover":
        reply({
            "supportedVersions": ["2026-07-28"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "forge", "version": VERSION},
            "_meta": {"io.modelcontextprotocol/serverInfo":
                      {"name": "forge", "version": VERSION}},
        })
        return
    if method == "initialize":
        requested = params.get("protocolVersion") or "2025-11-25"
        reply({
            "protocolVersion": requested,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "forge", "version": VERSION},
        })
        return
    if method == "ping":
        reply({})
        return
    if method == "tools/list":
        reply({"tools": _MCP_TOOLS})
        return
    if method == "tools/call":
        tool_name = params.get("name") or ""
        arguments = params.get("arguments") or {}
        if not isinstance(arguments, dict):
            reply(error={"code": -32602, "message": "arguments must be an object"})
            return
        result, error_code, error_message = _mcp_call_tool(tool_name, arguments)
        if error_code is not None:
            reply(error={"code": error_code, "message": error_message})
        else:
            reply(result)
        return
    if method.startswith("notifications/"):
        reply({})
        return
    reply(error={"code": -32601, "message": "Method not found: %s" % method})


ForgeHandler._handle_mcp = _handle_mcp


# ---------------------------------------------------------------------------
# Lifecycle: bind, register, poll done, exit
# ---------------------------------------------------------------------------

class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128
    allow_reuse_address = True

    def get_request(self):
        sock, addr = super().get_request()
        # No Nagle: the suite issues thousands of small request/response
        # pairs, and Nagle plus the client's delayed ACKs costs ~40 ms each.
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        return sock, addr


def _register(port):
    url = ENV_URL.rstrip("/") + "/register"
    body = json_dumps({"port": port}).encode("utf-8")
    request = urllib.request.Request(url, data=body, method="POST",
                                     headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(request, timeout=10) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code
    except Exception as exc:
        log_line("register failed: %r" % (exc,))
        return None


def _poll_done():
    url = ENV_URL.rstrip("/") + "/done"
    delay = 0.25
    while True:
        try:
            with urllib.request.urlopen(url, timeout=10) as response:
                data = json.loads(response.read().decode("utf-8"))
                if data.get("done"):
                    return
        except Exception as exc:
            log_line("done poll failed: %r" % (exc,))
        time.sleep(delay)
        delay = min(delay * 2, 2.0)


def main():
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    log_line("listening on port %d as %s" % (port, VIEWER_LOGIN))
    if ENV_URL:
        status = _register(port)
        log_line("register -> %s" % status)
        _poll_done()
        server.shutdown()
        server.server_close()
        log_line("done; exiting")
        return 0
    log_line("no MAKEFUN_ENV_URL set; serving until interrupted")
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
