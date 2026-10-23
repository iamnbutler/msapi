# Verification

`msapi-core`'s formulas and the token rules are checked by
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
| `next_id` | strictly greater than the last ID, and at least the time-based candidate |
| `page_size` | 50 by default, else exactly 1-200 |

## What is trusted

These parts are not proven. They are covered by tests instead.

- **I/O and parsing:** SQL queries, HTTP handling, serde, JSON merge patch,
  `Fixed` decimal parsing, base32 encoding (its order-preservation is tested,
  not proven).
- **Glue that feeds the proofs:** the one-line wrappers in `units`, `calc` and
  `stat` that unwrap unit types, and in `auth.rs` the mapping from account IDs
  to `AccountCheck { owned, reachable }`.
- **Hand-built constants:** `Ratio::ZERO` and `Ratio::ONE`.
- **Validation:** label lengths and `StatWindow::check`'s range rules.
- **The verifier itself:** Verus, Z3, and `vstd`'s specs of the standard
  library.
