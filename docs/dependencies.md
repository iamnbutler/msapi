# Dependencies

The rule: small crates that do one thing, thin wrappers over building blocks,
and a total that stays countable. CI fails if the number of third-party crates
in the normal and build graph exceeds the budget in `.github/workflows/ci.yml`.

| Crate | Why | Instead of |
|---|---|---|
| `tiny_http` | A synchronous HTTP/1.1 server: a request in, a response out. Threads, not an async runtime. | axum + tokio + hyper + tower (~130 crates) |
| `rusqlite` (`bundled`) | The standard SQLite binding. Thin over the C API; bundles a known SQLite version so behaviour does not depend on the host. | sqlx (pulls in a runtime and macros) |
| `ring` | SHA-256 for token hashes, the OS random number generator, and passkey signature checks (ES256, Ed25519, RS256). Audited, no other dependencies to speak of. | sha2 + rand + getrandom stacks |
| `serde`, `serde_json` | JSON in and out, with derived, typed validation at the boundary. `arbitrary_precision` keeps numbers as their exact text, so decimals never pass through `f64`. | |
| `foldhash` | A fast, small, non-cryptographic hasher for in-memory lookup tables (class index). Already in the graph through rusqlite's hashlink. | the default SipHash |

Counted with:

```sh
cargo tree -e normal,build --prefix none --format '{p}' | sed 's/ (.*//' | sort -u | grep -v '^msapi' | wc -l
```

36 at the time of writing.

Dev-only additions need the same care but are not counted. Adding a crate
means a row in this table saying what it replaces.

## Builds

Builds go through [mbx](https://mr-boxington.jdx.dev), a shared Cargo build
cache, so a fresh lane worktree restores compiled dependencies instead of
rebuilding them. `mise.toml` sets it up for mise users; CI uses
`jdx/mr-boxington-action`.
