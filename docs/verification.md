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

### `units.rs` and `calc.rs`: the typed wrappers

Each wrapper unwraps its unit types and calls a formula above; the proof says
its result is that formula's spec applied to the unwrapped values, and that
each error is returned exactly in its case. `value()` is a unit's raw integer.

| Function | Proven |
| --- | --- |
| `DamagePct::factor`, `FinalDamage::factor` | the ratio `(10000 + p) / 10000` (floored at 0), in lowest terms |
| `IgnoreDefense::remaining` | `(10000 - p) / 10000` |
| `FinalDamage::stack`, `IgnoreDefense::stack` | `stack_final_damage` and `stack_ignore_defense` of the sources' raw values |
| `IgnoreDefense::defense_factor`, `CritDamage::crit_factor` | `defense_factor` of the unwrapped values (PDR clamped); `max(0, 13500 + cd) / 10000` |
| every unit's `new`, `get`, `pct`, `raw`, `plus`; `Fixed::from_raw`, `raw` | the value in is the value out; `plus` (and so `+`) saturates at the ends of `u64` or `i64` |
| `StatValue::for_class` | `Unsupported` exactly when the class's stats name HP; otherwise `stat_value` of the class's primary and secondary totals, `Overflow` exactly when that exceeds `u64` |
| `JobAttack::for_class` | magic attack exactly when the class uses it |
| `ScaledAttack::total` | `scaled` of the flat attack and its percent, `Overflow` exactly on overflow |
| `displayed_range` | `displayed_range`'s spec of the unwrapped inputs; the only error is `Overflow` |
| `bow_normalised_attack` | `bow_normalised`'s spec, and `Ok` whenever it and the intermediate product fit |
| `combat_power` | `combat_power`'s spec of the unwrapped inputs and class Final Damage list |
| `Ratio::ZERO`, `Ratio::ONE` | built by `Ratio::from_int`, so in lowest terms and equal to 0 and 1 |
| `Count::get`, `Count::of_count`, `Percent::pct` (every unit) | trait specs: the count or hundredths in is the count or hundredths out |
| `+`, `+=` on every unit | `plus`: saturating addition, matching vstd's `Add`/`AddAssign` specs |
| `breakdown_total` (generic over `Scalable`) | `implied_total`'s spec of the base, the percent's hundredths (0 if absent) and the flat value (0 if absent); `None` exactly on overflow |

### `policy.rs`: token rules

| Function | Proven |
| --- | --- |
| `contains`, `minus`, `is_subset` | bit-level set semantics; `minus(a, b) = 0` exactly when `a ⊆ b` |
| `check_mint` | an `Ok` grant has a non-empty subset of the parent's scopes. Its accounts are non-empty, all owned and all reachable. It is account-limited whenever the parent is, sits within the depth limit, and expires no later than the parent and within 30 days |
| `chain_expiry` | a token works exactly when no token in its chain is revoked or expired, and then expires at the earliest expiry in the chain (or never, if none expire) |
| `is_member`, `reaches` | byte-for-byte membership of an ID in a list; `reaches` is true for an unlimited token |
| `account_checks` | one `AccountCheck` per requested ID, with `owned` its membership in the user's accounts and `reachable` its `reaches` under the parent's limit |
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
| every authenticated route | `chain_expiry` (is the token alive, and until when), `contains` (scope), `reaches` (account limit) |
| `POST /v1/tokens` | `account_checks`, `check_mint`, `length_ok` (label) |
| `GET` lists (`limit`) | `page_size` |
| `POST`/`PATCH /v1/accounts` | `length_ok` (label, notes) |
| `POST`/`PATCH /v1/characters…` | `in_range` (levels), `exp_rate_ok`, `length_ok` |
| `PUT`/`PATCH …/stat` | `captured_at_ok`, `ignore_defense_ok`, `cooldown_reduction_ok`, `percentage_ok`, `range_ok`, and `implied_total` for tooltip warnings |
| `/v1/auth/passkey/*` | `base64url::decode` (every binary field and the challenge), `Cbor::decode`, `PublicKey::from_cose`, `bytes_eq` (type, credential ID), `origin_ok`, `rp_id_hash_ok`, `es256_point`, `auth_data_layout`, `presence_ok`, `counter_ok`, `length_ok` (display name) |
| every query parameter | `parse_query` |
| stat fields with decimals | `parse_decimal` in, `format_decimal` out (exact JSON text) |
| new IDs (audit and history order) | `next_id`, then `base32::encode_u128` (proven order-preserving) |
| token secrets | `base32::encode` |
| every write (the durable log) | `encode_statement`; on restore `frames`, `decode_batch`, `next_batch_ok` |
| calculators (`calc`, `units`) | the wrappers above, and through them `formula.rs` and `ratio.rs` |

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
| `base32::encode_u128` (IDs) | each character is `crockford()[digit]`, the literal 32-character table, of its five bits; `a < b` implies the encoding of `a` sorts first (`lemma_order`), so string order is ID order; distinct values encode differently. `lemma_u128_is_bytes`: each digit equals group `i` of the value's 16 big-endian bytes, and `encode_bytes_agree` checks that `encode(&be_bytes_u128(v))` is exactly `encode_u128(v)` |
| `base32::encode` (token secrets) | exactly `(8n + 4) / 5` characters, character `i` being `crockford()[group(bytes, i)]`: bits `5i..5i+4` of the input, most significant first, zero past the end |
| `base32::digit_char` | equals the table `crockford()` for every digit below 32 |
| `base32::be_bytes_u128` | equals `be_bytes`: byte `q` is bits `120 - 8q` to `127 - 8q` of the value (what `u128::to_be_bytes` returns) |
| `decimal::parse_decimal` (`Fixed` from text) | `Ok(v)` exactly when the text is `-?D+(.D+)?` with at most `dp` fraction digits and fits `i64`, and then `v` is its exact value scaled by `10^dp`; each error (`Invalid`, `TooPrecise`, `OutOfRange`) is returned exactly in its case; a string splits into whole and fraction one way only |
| `decimal::format_decimal` (`Fixed` and its units as text) | equals `decimal_text`: `-` if negative, the whole part's digits with no leading zeros, then `.` and exactly `dp` fraction digits when `dp > 0`; byte-identical to the old `format!` output |
| `decimal::format_then_parse` | `parse_decimal(format_decimal(v, dp), dp) == Ok(v)` for every `i64` and `dp <= 18` (`lemma_text_round_trip`) |
| `decimal::format_uint` (flat units, `Ratio` as text) | equals `digits_of`: the decimal digits of `n`, no leading zeros, whose value is `n` |
| `ascii::eq_ignore_case` | equal lengths and equal bytes after lowercasing ASCII capitals, as `str::eq_ignore_ascii_case` |
| `ascii::fold` (class names) | equals `folded`: the ASCII letters and digits in order, lowercased |
| `ascii::lowercase` (region names) | equals `lowered`: each byte lowercased if an ASCII capital; two names' `lowered` forms are equal exactly when `eq_ignore_case` holds (`lemma_same_folded_lowered`) |
| `lookup::tagged_key` (world names) | the region's tag, `0xFF`, then the lowercased name; two keys are equal exactly when the regions are and the names are equal ignoring case (`lemma_tagged`) |
| `names::{class,world,region}::find` (`class::find`, `world::find`, `Region`'s `FromStr`) | each table's keys are byte literals (`key(i)`, naming entry `owner(i)`) and are pairwise distinct (`lemma_distinct`, every pair evaluated by `all_distinct`), so for every key `i`, `find(key(i))` is `Some(owner(i))`; `Some(o)`: some key equal to the query names `o`, a position in the table; `None`: no key equals the query. Nothing is checked at run time and nothing can panic |
| `scope::scope_index` (`Scope::from_str`) | `r == index_of(name)`: the scope whose `scope_name` is exactly `name`, or `None` |
| `scope::parse_scopes` (stored token scopes) | `Ok(bits)` exactly when every ASCII-whitespace-separated token names a scope, `bits` being their union (`parse`); `Err` gives the range of a token that names none |
| `scope::format_scopes` | the names of the set scopes in order, separated by single spaces (`fmt`), and `parse(format_scopes(b)) == Some(b & 0xff)` |
| `query::percent_decode` | equals `decoded`: `+` is a space, `%XX` is that byte, anything else is itself |
| `json::merge` (every `PATCH`) | the result is `merged(result, target, patch)`, RFC 7396 §2 key by key: a `null` member's key is absent, any other member's key holds the merge of the target's value (or `null`) with it, every other key keeps the target's value, keys are unique, and a non-object patch is the result; `None` exactly when an input repeats an object key (`serde_json` values never do) |
| `query::parse_query` | equals `pairs`: the `&`-separated segments in order, empty ones skipped, each split at its first `=` (none means an empty value) and both halves `decoded` |
| `batch::encode_statement` | appends exactly the spec encoding when every length fits a `u32`, and refuses (appending nothing) otherwise |
| `batch::decode_batch` | anything it accepts re-encodes to exactly its input, and the encoding of any statement list decodes back to that list; no read is out of bounds |
| `batch::frame_at` | a frame is a big-endian sequence number and length, then the body; it returns exactly the frame at that offset |
| `batch::frames` | whatever it returns re-encodes, frame after frame, to exactly the whole buffer; whenever the buffer is a run of frames it returns exactly those frames, so a truncated or padded tail is refused rather than dropped |

### `time.rs`: timestamps (`captured_at`, `created_at`, `expires_at`)

The calendar spec counts days: `year_start(y)` is 365 a year plus one per
leap year before `y`, `month_start` is the month table (plus one after
February in a leap year), and `day_number(y, m, d)` is days since 1970-01-01.
The supported range is `0000-01-01T00:00:00.000Z` to
`9999-12-31T23:59:59.999Z` (`MIN_MS` to `MAX_MS`), the four-digit years
RFC 3339 can write.

| Function | Proven |
| --- | --- |
| `days_from_civil` | equals `day_number` for every valid date, which lies between `0000-01-01` and `9999-12-31` |
| `civil_from_days` | for every day in range, returns a valid date (month 1 to 12, day within the month, Gregorian leap years) whose `day_number` is that day; `lemma_day_number_injective` says no two valid dates share a day number, so each function undoes the other |
| `format_rfc3339` (`Display`, serde) | the output is `text(d)`, `YYYY-MM-DDTHH:MM:SS.mmmZ` written digit by digit, for a valid date and time `d` at the timestamp clamped to the range, and `parse_spec` of the output is that clamped timestamp. Out-of-range timestamps (such as `plus_millis` saturating at `i64::MAX`) format as the nearest end of the range, so the output always parses |
| `parse_rfc3339` (`FromStr`, serde) | equals `parse_spec`: `YYYY-MM-DDTHH:MM:SS[.fraction](Z\|+HH:MM\|-HH:MM)`, `T` and `Z` either case, at least one fraction digit after a `.` with digits past the third dropped, a valid date, hours at most 23 and minutes and seconds at most 59 (offsets too); the value is the instant less the offset, and `None` when that falls outside the range |
| `lemma_round_trip` | `parse_spec(text(d))` is `d`'s instant for every valid `d`, so parsing a formatted in-range timestamp gives it back |

Formatting is byte-for-byte what the previous Hinnant implementation printed
for every in-range timestamp; a test compares the two on every day in range.

## What is trusted

These parts are not proven. They are covered by tests instead.

- **Outside libraries and runtimes:** SQLite (through `rusqlite`), the HTTP
  server (`tiny_http`), JSON (`serde_json`) including field types and
  string-to-enum lookups, `ring` (SHA-256 and signature checks), the OS random
  number generator, and the Cloudflare Worker and Durable Object that keep the
  log (`deploy/src/index.ts`, TypeScript).
- **Code that only moves data between those and the proofs:** SQL query
  text and account ownership (a SQL query), converting `serde_json` values to
  and from `json::Json` around the merge patch, the rusqlite-value conversions
  in `durable.rs`, turning ASCII bytes into `String`s (including `Scope::as_str` over
  `scope::scope_name`), the byte-literal keys in `names.rs` being the folded
  IDs and names of `CLASSES`, the tagged keys and names of `WORLDS` and the
  lowercased names of `Region::ALL` (generated by `scripts/name_keys.py`; a
  test checks each table key for key), and in `auth.rs` viewing
  account-ID `String`s as their bytes (`String::as_bytes`) for
  `account_checks` and `reaches`, and `Timestamp`'s `Display`, `FromStr`
  and serde impls passing bytes to and from the proven `format_rfc3339` and
  `parse_rfc3339`. `Timestamp::now` reads the system clock.
- **Unit plumbing that is generic or a trait impl:** `StatBreakdown::implied_total`
  passing its three fields to the proven `breakdown_total` (the struct derives
  serde, so Verus does not see it), the `Sum` impls (std's `Iterator::fold`
  over the proven `+`, since Verus cannot specify a generic iterator), and the
  `From`, `Debug` and serde impls of the unit types. Their `Display`,
  `FromStr` and JSON impls only write or read the bytes of the proven
  `format_decimal`, `format_uint` and `parse_decimal`: `Fixed` crosses JSON as
  its exact decimal text (`serde_json`'s `arbitrary_precision`), never as an
  `f64`. PATCH documents are read back from their JSON text after the merge,
  so they take the same exact path as request bodies.
- **Spec against reality:** that the specs are the game's formulas and the
  RFCs' formats is checked by golden tests and known vectors, not proofs.
- **The verifier itself:** Verus, Z3, and `vstd`'s specs of the standard
  library.

`tests/passkey.rs` drives both passkey ceremonies with a software
authenticator (replayed counters, wrong origins, wrong sites, tampered
signatures); `tests/durable.rs` rebuilds a database from its log and compares
it with the original; `deploy/e2e.ts` runs the hosted web app end to end.
