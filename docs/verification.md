# Verification

`msapi-core`'s formulas, the token rules and the passkey byte rules are checked by
[Verus](https://github.com/verus-lang/verus): each function carries a
specification, and the proof that the code meets it is machine-checked on every
pull request (the `verify` job in `.github/workflows/ci.yml`).

```sh
# Verus release 0.2026.10.18.7d82994, which uses Rust 1.99.1
cd crates/msapi-core
cargo verus verify --features verus
```

The specs and proofs are ghost code behind the optional `verus` feature, so a
normal build compiles exactly the code it always did, with no extra
dependencies. Proof blocks are `proof! { … }`, which compiles to nothing
without the feature.

## What is proven

Every proof also shows the function cannot panic: no overflow, no division by
zero, no out-of-bounds index.

### `ratio.rs`: exact fractions

| Function | Proven |
| --- | --- |
| `gcd` | equals Euclid's gcd |
| `Ratio::new` | the result equals `num/den`, is in lowest terms, and is `None` exactly when `den = 0` |
| `checked_mul`, `checked_div`, `checked_add` | a `Some` result is the exact product, quotient or sum, in lowest terms. `checked_mul` returns `None` only when the exact product does not fit in `u128` |
| `checked_saturating_sub` | the exact `max(0, a - b)` |
| `floor` | `q·d <= n < (q + 1)·d` |
| `round_half_up` | `2q·d <= 2n + d < 2(q + 1)·d`; the old `2 × rem` overflow is gone |
| `Ord` | the exact sign of `a·d - c·b`, with no float fallback |

`arith.rs` holds the number theory these need: the gcd divides both arguments,
every common divisor divides the gcd, and dividing by the gcd leaves coprime
numbers.

### `formula.rs`: the game's formulas

These are integer functions; `units`, `calc` and `stat` unwrap their unit
types and call them. Percentages are raw hundredths (`Pct::raw`).

| Function | Spec |
| --- | --- |
| `stat_value` | `4 × Σ primary + Σ secondary`, and `None` exactly when that exceeds `u64` |
| `scaled` (ATT × (1 + ATT%)) | `floor(base × (10000 + p) / 10000)`, and `None` exactly on overflow |
| `implied_total` (stat tooltips) | `scaled + flat`, and `None` exactly on overflow |
| `displayed_range` | the damage range formula (`upper_actual`, `lower_actual`, then the shown floors) |
| `combat_power` | `floor(N / D)` for the CP numerator and denominator, including dividing out class Final Damage |
| `bow_normalised` | `flat + floor((bow - w)(w + sf) / w)` with floor division, and `Some` whenever the result and the intermediate product fit |
| `stack_final_damage` | `Π (10000 + fdᵢ) / 10000ⁿ` |
| `stack_ignore_defense` | `Π (10000 - iedᵢ) / 10000ⁿ` |
| `defense_factor` | `max(0, 1 - pdr × (1 - ied))` with PDR clamped to [0, 500%] |

The specs are written in exact integer arithmetic, so "proven" means the code
computes these expressions exactly. Whether the expressions are the game's
formulas is a separate question, which the golden tests answer against numbers
the game displayed (for example a real character's 236,118 CP).

### `policy.rs`: token rules

| Function | Proven |
| --- | --- |
| `contains`, `minus`, `is_subset` | bit-level set semantics; `minus(a, b) = 0` exactly when `a ⊆ b` |
| `check_mint` | an `Ok` grant has a non-empty subset of the parent's scopes. Its accounts are non-empty, all owned and all reachable. It is account-limited whenever the parent is, sits within the depth limit, and expires no later than the parent and within 30 days |
| `chain_expiry` | a token works exactly when no token in its chain is revoked or expired, and then expires at the earliest expiry in the chain (or never, if none expire) |
| `next_id` | strictly greater than the last ID, and at least the time-based candidate |
| `page_size` | 50 by default, else exactly 1-200 |

### `rules.rs`: what the routes accept

| Function | Proven |
| --- | --- |
| `in_range` | `min <= v <= max` (character level 1-300, class level 0-6) |
| `length_ok` | `min <= chars <= max` (labels, notes, names, display names) |
| `ignore_defense_ok`, `cooldown_reduction_ok`, `percentage_ok`, `exp_rate_ok`, `range_ok` | the stat window's and character's hard limits, exactly as stated |
| `captured_at_ok` | `captured_at <= now + 5 min` in exact integers, with no overflow at the ends of `i64` |
| `next_batch_ok` | a log batch is applied only if it is exactly the next one |

### Every route's decisions

The handlers parse, query and store; each accept-or-refuse decision they make
goes through a proven function.

| Route | Decided by |
| --- | --- |
| every authenticated route | `chain_expiry` (is the token alive, and until when), `contains` (scope) |
| `POST /v1/tokens` | `check_mint`, `length_ok` (label) |
| `GET` lists (`limit`) | `page_size` |
| `POST`/`PATCH /v1/accounts` | `length_ok` (label, notes) |
| `POST`/`PATCH /v1/characters…` | `in_range` (levels), `exp_rate_ok`, `length_ok` |
| `PUT`/`PATCH …/stat` | `captured_at_ok`, `ignore_defense_ok`, `cooldown_reduction_ok`, `percentage_ok`, `range_ok`, and `implied_total` for tooltip warnings |
| `/v1/auth/passkey/*` | `auth_data_layout`, `cbor_head`, `presence_ok`, `counter_ok`, `length_ok` (display name) |
| new IDs (audit and history order) | `next_id` |
| restore from the log | `next_batch_ok` |
| calculators (`calc`, `units`) | the `formula.rs` and `ratio.rs` functions above |

### `webauthn.rs`: passkey bytes and rules

| Function | Proven |
| --- | --- |
| `auth_data_layout` | the flags byte and the big-endian signature counter are read from offsets 32 and 33-36; the credential ID range is in bounds, starts at 55 and has the declared length when the attested flag is set, and is empty otherwise; `None` exactly when the data is shorter than its flags announce |
| `cbor_head` | the major type, and the argument read big-endian from the 0, 1, 2, 4 or 8 bytes the initial byte declares; the content offset is in bounds; indefinite and reserved lengths are refused |
| `counter_ok` | a sign-in counter is accepted only if it grew, or if the authenticator keeps none (both 0) |
| `presence_ok` | sign-in requires the user-present flag |

## What is trusted

These parts are not proven. They are covered by tests instead.

- **I/O and parsing:** SQL queries, HTTP handling, serde, JSON merge patch,
  `Fixed` decimal parsing, base32 and base64url encoding (tested, not proven).
- **Passkey glue:** the recursive CBOR decoder built on `cbor_head`, COSE key
  selection, the client-data checks (type, challenge, origin) and the
  signature checks, which are `ring`'s. `tests/passkey.rs` drives both
  ceremonies with a software authenticator, including replayed counters,
  wrong origins, wrong sites and tampered signatures.
- **Durability:** the write log (`durable.rs`) and the Worker that stores it
  (`deploy/src/index.ts`); `tests/durable.rs` rebuilds a database from its
  log and compares it with the original.
- **Glue that feeds the proofs:** the one-line wrappers in `units`, `calc` and
  `stat` that unwrap unit types, and in `auth.rs` the mapping from account IDs
  to `AccountCheck { owned, reachable }`.
- **Hand-built constants:** `Ratio::ZERO` and `Ratio::ONE`.
- **What feeds the rules:** which fields exist and their types (serde),
  string-to-enum lookups (worlds, classes, regions), URL checks on
  `character_image`, and account ownership (a SQL query).
- **The verifier itself:** Verus, Z3, and `vstd`'s specs of the standard
  library.
