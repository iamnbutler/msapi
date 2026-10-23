# Verification

`msapi-core`'s formulas, the token rules, the passkey byte formats, and every encoding and
parser the server owns are checked by
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
| `/v1/auth/passkey/*` | `base64url::decode` (every binary field and the challenge), `Cbor::decode`, `PublicKey::from_cose`, `bytes_eq` (type, credential ID), `origin_ok`, `rp_id_hash_ok`, `es256_point`, `auth_data_layout`, `presence_ok`, `counter_ok`, `length_ok` (display name) |
| every query parameter | `percent_decode` |
| stat fields with decimals | `parse_decimal` |
| new IDs (audit and history order) | `next_id`, then `base32::encode_u128` (proven order-preserving) |
| token secrets | `base32::encode` |
| every write (the durable log) | `encode_statement`; on restore `frame_at`, `decode_batch`, `next_batch_ok` |
| calculators (`calc`, `units`) | the `formula.rs` and `ratio.rs` functions above |

### `webauthn.rs`: passkey bytes and rules

| Function | Proven |
| --- | --- |
| `auth_data_layout` | the flags byte and the big-endian signature counter are read from offsets 32 and 33-36; the credential ID range is in bounds, starts at 55 and has the declared length when the attested flag is set, and is empty otherwise; `None` exactly when the data is shorter than its flags announce |
| `cbor_head` | the major type, and the argument read big-endian from the 0, 1, 2, 4 or 8 bytes the initial byte declares; the content offset is in bounds; indefinite and reserved lengths are refused |
| `counter_ok` | a sign-in counter is accepted only if it grew, or if the authenticator keeps none (both 0) |
| `presence_ok` | sign-in requires the user-present flag |
| `Cbor::decode` | every item ends after it starts and within the buffer, and every byte and text string it returns lies inside its item. Nesting is capped at 8 and counts larger than the remaining bytes are refused, so it terminates without unbounded allocation |
| `get_int`, `get_text`, `as_bytes`, `as_int` | a value found is one of the map's entries; `get_text` compares the key's exact bytes; `as_bytes` returns exactly the item's range of the buffer; `as_int` is the exact integer |
| `origin_ok` | the client data's origin is byte-for-byte this site's and `crossOrigin` is false |
| `bytes_eq` | exact byte equality (the client data's type, the credential ID against the authenticator data) |
| `rp_id_hash_ok` | the authenticator data starts with exactly the relying-party ID hash |
| `es256_point` | the key handed to ECDSA is exactly `04 ‖ x ‖ y` |
| `PublicKey::from_cose` | ES256 and Ed25519 keys come back with exactly 32-byte coordinates |

### Encodings and parsers

| Function | Proven |
| --- | --- |
| `base64url::encode` | equals `encode_spec`, RFC 4648 §5 written group by group |
| `base64url::decode` | whatever it returns encodes back to its input (padding aside), and it returns `None` only when no byte string encodes to the input. So it is canonical: one encoding per byte string |
| `base32::encode_u128` (IDs) | each character is the Crockford digit of its five bits; `a < b` implies the encoding of `a` sorts first (`lemma_order`), so string order is ID order; distinct values encode differently |
| `base32::encode` (token secrets) | output length is `(8n + 4) / 5` and every character is Crockford |
| `decimal::parse_decimal` (`Fixed` from text) | `Ok(v)` exactly when the text is `-?D+(.D+)?` with at most `dp` fraction digits and fits `i64`, and then `v` is its exact value scaled by `10^dp`; each error (`Invalid`, `TooPrecise`, `OutOfRange`) is returned exactly in its case; a string splits into whole and fraction one way only |
| `query::percent_decode` | equals `decoded`: `+` is a space, `%XX` is that byte, anything else is itself |
| `batch::encode_statement` | appends exactly the spec encoding when every length fits a `u32`, and refuses (appending nothing) otherwise |
| `batch::decode_batch` | anything it accepts re-encodes to exactly its input, and the encoding of any statement list decodes back to that list; no read is out of bounds |
| `batch::frame_at` | a frame is a big-endian sequence number and length, then the body; it returns exactly the frame at that offset |

## What is trusted

These parts are not proven. They are covered by tests instead.

- **Outside libraries and runtimes:** SQLite (through `rusqlite`), the HTTP
  server (`tiny_http`), JSON (`serde_json`) including field types and
  string-to-enum lookups, `ring` (SHA-256 and signature checks), the OS random
  number generator, and the Cloudflare Worker and Durable Object that keep the
  log (`deploy/src/index.ts`, TypeScript).
- **Code that only moves data between those and the proofs:** SQL query
  text and account ownership (a SQL query), JSON merge patch (`serde_json`
  values), the
  rusqlite-value conversions in `durable.rs` and its iterator over frames, the
  `&` and `=` split in query strings, turning ASCII bytes into `String`s, the
  `units`, `calc` and `stat` wrappers that unwrap unit types, and in `auth.rs`
  the mapping to `AccountCheck { owned, reachable }`.
- **Hand-built constants:** `Ratio::ZERO` and `Ratio::ONE`.
- **Spec against reality:** that the specs are the game's formulas and the
  RFCs' formats is checked by golden tests and known vectors, not proofs.
- **The verifier itself:** Verus, Z3, and `vstd`'s specs of the standard
  library.

`tests/passkey.rs` drives both passkey ceremonies with a software
authenticator (replayed counters, wrong origins, wrong sites, tampered
signatures); `tests/durable.rs` rebuilds a database from its log and compares
it with the original; `deploy/e2e.ts` runs the hosted web app end to end.
