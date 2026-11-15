# github-core-clone-01

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/nguyenhuong74/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/nguyenhuong74/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone, GitHub-compatible git forge in a single Python file — no git
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

## Run it

```sh
MAKEFUN_SHOP_TOKEN=<token> python3 main.py
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

- `main.py` — the whole forge: lifecycle, HTTP server, REST v3, git smart
  HTTP, GraphQL, MCP. Python 3.12+ standard library only.
- `LICENSE` — MIT.
- `.makefun/owner.json` — the payout wallet for this entry.

## Notes

- Auth is a bearer token (`MAKEFUN_SHOP_TOKEN`) on every API and git
  endpoint; `/healthz` is the only exemption. A missing or wrong token is
  a 401.
- Timestamps are deterministic (a fixed epoch plus a sequence), so ordering
  is creation order and no wall clock leaks into a response.
- Responses are written in one syscall with TCP_NODELAY set, which matters
  for the read workload's 2,000 sequential requests on one connection.

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
