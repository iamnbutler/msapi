# msapi

A hand-rolled MapleStory API: one service that MapleStory tools read from and
write to. Nexon publishes almost nothing for GMS (a rankings endpoint), so
people and their agents enter what the game shows, and msapi keeps it typed,
validated, versioned and audited.

Today it holds accounts (region), characters (world, world type, class, level,
and the rest of the character screen) and the stat window, with every write
kept as a snapshot. Equipment, symbols, hyper stats and the rest are planned;
their routes exist and answer 501.

## Run it

```sh
cargo run --release -- user create "your name"   # prints a root token, once
cargo run --release -- serve --addr 127.0.0.1:8080 --db msapi.db
curl -H "Authorization: Bearer msk_…" localhost:8080/v1/me
```

`MSAPI_ADDR`, `MSAPI_DB` and `MSAPI_TRUST_PROXY=1` (take the client address
from `X-Forwarded-For`) set the defaults.

The API guide, written for agents, is [`docs/api.md`](docs/api.md) and is
served at `/v1/docs`. `GET /v1` lists every route.

## Tokens and audit

A root token belongs to a person. From it they mint short-lived tokens for
agents, each with fewer scopes, fewer accounts and an earlier expiry than the
token that minted it, to any depth up to four. Revoking a token revokes
everything below it. Every write, and every refused write, is recorded with
the token's label and the data before and after, so the owner can see what an
agent did. Sign-in with passkeys or GitHub to obtain a root token is next.

## Layout

- `crates/msapi-core`: the domain. Units, exact decimals, reference data
  (regions, worlds, classes) and formulas (displayed damage range, Combat
  Power), tested against values read from the game.
- `crates/msapi-server`: HTTP over SQLite. `routes::handle` is a plain
  function from request to response; `serve` adapts a socket to it.

## Rules the code keeps

- **Absent is not zero.** A stat nobody read is `null`, never `0`.
- **Exact numbers.** Percentages are fixed-point decimals with the game's
  precision; formulas run on exact rationals and round only where the game
  does.
- **Every quantity has a unit.** `Str + Dex` and `FinalDamage + FinalDamage`
  do not compile; final damage and ignore defense combine through `stack`.
- **Every write is audited.** The only way to commit a transaction is through
  the audit writer.
- **Few dependencies.** See [`docs/dependencies.md`](docs/dependencies.md).

## Development

Work happens in [lane](https://lane.lukeed.com) worktrees; see `AGENTS.md`.
Builds go through [mbx](https://mr-boxington.jdx.dev) for a shared build cache
(`mise.toml` sets it up).

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option. Unless you explicitly state
otherwise, any contribution intentionally submitted for inclusion in msapi, as
defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
