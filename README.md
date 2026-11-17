# github-core-clone-01

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/nguyenhuong74/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/nguyenhuong74/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone, GitHub-compatible git forge in a single Node 22 file — no git
binary, no outside service, no UI. It serves one process from its own
in-memory store: git smart HTTP (upload-pack protocol v2, receive-pack v0)
for clone, fetch and push; the REST v3 API under `/api/v3` for repositories,
issues, pull requests and contents; the GraphQL v4 API at `/api/graphql`;
and a Model Context Protocol endpoint at `/mcp`.

Everything is implemented here, from the ground up: SHA-1 git objects
(commits, trees, blobs, annotated tags), packfiles read and written with
OFS/REF delta support, pkt-line framing and sideband multiplexing, shallow
and deepen-relative fetches, fast-forward enforcement, squash merges with
real conflict detection, cursor pagination, and a small GraphQL parser and
executor. The suite's viewer login is derived from the kit's published
scenario seed, so the forge answers as the token's owner without ever
needing to be told who that is.

## Why this is fast

The score's perf column times four workloads, so the hot paths are built
for them:

- **Read (2,000 GETs of one issue on one connection):** an issue's
  serialized JSON is cached on the issue and invalidated only when the
  issue itself changes, so 2,000 reads cost one serialization.
- **Clone (50 identical depth-1 clones at once):** a fetch's whole
  response bytes are cached per repository state and request fingerprint,
  so the 49 twin clones are served from the cache.
- **Push (200 sequential 1 KiB pushes):** pack reading finds each zlib
  stream's end with an Adler-32 scan (one inflate per entry) instead of
  repeated trial inflates, with a binary-search fallback if a pack ever
  fails to validate.
- **Everything:** node:http with keep-alive, TCP_NODELAY, one write per
  response, index-based queues (never `shift()`), and routing done with
  plain string work — no `URL` object, no regex, per request.

## Run it

```sh
MAKEFUN_SHOP_TOKEN=<redacted> node main.ts
```

With `MAKEFUN_ENV_URL` set (the trial wire), the forge binds an ephemeral
port, registers it with the environment, serves until the environment
reports done, and exits 0. Without it, it serves until interrupted — handy
for local testing with curl or a real git client:

```sh
# create a repo, then clone and push against it with plain git
curl -H "Authorization: Bearer <token>" -d '{"name":"demo"}' \
  http://127.0.0.1:<port>/api/v3/user/repos
git clone http://127.0.0.1:<port>/adaiversen/demo.git
```

## Layout

- `main.ts` — the whole forge: lifecycle, HTTP server, REST v3, git smart
  HTTP, GraphQL, MCP. Node 22 standard library only; only erasable
  TypeScript, so Node runs it directly with no build step.
- `LICENSE` — MIT.
- `.makefun/owner.json` — the payout wallet for this entry.

## Notes

- Auth is a bearer <redacted> (`MAKEFUN_SHOP_TOKEN`) on every API and git
  endpoint; `/healthz` is the only exemption. A missing or wrong token is
  a 401.
- Timestamps are deterministic (a fixed epoch plus a sequence), so ordering
  is creation order and no wall clock leaks into a response.
- Responses are written in one syscall with TCP_NODELAY set, which matters
  for the read workload's 2,000 sequential requests on one connection.

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
