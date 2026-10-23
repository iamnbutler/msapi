//! The checks the API's routes make on what they are sent, as plain code that
//! Verus checks.
//!
//! The routes parse JSON and run SQL; every accept-or-refuse decision they
//! make on a value is one of these functions. Percentages are raw hundredths
//! (`Pct::raw`), times are milliseconds since the Unix epoch.

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// 100% in raw hundredths.
#[cfg_attr(feature = "verus", verus_verify)]
pub const HUNDRED_PERCENT: i64 = 10_000;

/// How far in the future a stat capture may claim to be: five minutes, for
/// clock skew between a player's machine and the server.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_FUTURE_MS: i64 = 5 * 60 * 1000;

/// Whether `v` is in `min..=max`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (min <= v && v <= max)))]
#[must_use]
pub const fn in_range(v: i64, min: i64, max: i64) -> bool {
    min <= v && v <= max
}

/// Whether a text field of `chars` characters fits `min..=max`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (min <= chars && chars <= max)))]
#[must_use]
pub const fn length_ok(chars: usize, min: usize, max: usize) -> bool {
    min <= chars && chars <= max
}

/// Ignore Enemy Defense is always below 100%: each source multiplies the
/// defense left, so the total approaches 100% and never reaches it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (raw < 10_000)))]
#[must_use]
pub const fn ignore_defense_ok(raw: i64) -> bool {
    raw < HUNDRED_PERCENT
}

/// Cooldown reduction as a percentage is at most 100%.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (raw <= 10_000)))]
#[must_use]
pub const fn cooldown_reduction_ok(raw: i64) -> bool {
    raw <= HUNDRED_PERCENT
}

/// The percentages the stat window shows are never negative.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (raw >= 0)))]
#[must_use]
pub const fn percentage_ok(raw: i64) -> bool {
    raw >= 0
}

/// Experience toward the next level, in raw thousandths of a percent, is in
/// `[0, 100%)`: at 100% the character levels up.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (0 <= raw && raw < 100_000)))]
#[must_use]
pub const fn exp_rate_ok(raw: i64) -> bool {
    0 <= raw && raw < 100_000
}

/// The damage range's minimum is not above its maximum.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (min <= max)))]
#[must_use]
pub const fn range_ok(min: u64, max: u64) -> bool {
    min <= max
}

/// Whether a capture time is acceptable at `now`: no more than
/// [`MAX_FUTURE_MS`] ahead. Exact for every input, including times near the
/// ends of `i64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (captured_at as int <= now as int + MAX_FUTURE_MS as int)))]
#[must_use]
pub const fn captured_at_ok(now: i64, captured_at: i64) -> bool {
    match now.checked_add(MAX_FUTURE_MS) {
        Some(limit) => captured_at <= limit,
        // `now + MAX_FUTURE_MS` is past `i64::MAX`, so every `i64` is within it.
        None => true,
    }
}

/// Whether write batch `n` may follow batch `last` in the durable log: only
/// the very next one, so nothing is skipped or applied twice.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (n as int == last as int + 1)))]
#[must_use]
pub const fn next_batch_ok(last: u64, n: u64) -> bool {
    match last.checked_add(1) {
        Some(next) => n == next,
        None => false,
    }
}

/// Longest character name any region allows, in characters.
#[cfg_attr(feature = "verus", verus_verify)]
pub const NAME_MAX_CHARS: usize = 13;

/// Longest GMS character name, in ASCII letters and digits.
#[cfg_attr(feature = "verus", verus_verify)]
pub const GMS_NAME_MAX: usize = 12;

/// What is wrong with a character name, if anything.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NameCheck {
    /// A name.
    Ok,
    /// No characters.
    Empty,
    /// More than [`NAME_MAX_CHARS`] characters.
    TooLong,
    /// Surrounding whitespace or a control character.
    Untidy,
}

/// The verdict on a name of `chars` characters, `tidy` when it has no
/// surrounding whitespace and no control characters; the first rule broken
/// wins.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r == if chars == 0 { NameCheck::Empty }
            else if chars > NAME_MAX_CHARS { NameCheck::TooLong }
            else if !tidy { NameCheck::Untidy }
            else { NameCheck::Ok },
))]
#[must_use]
pub const fn name_check(chars: usize, tidy: bool) -> NameCheck {
    if chars == 0 {
        NameCheck::Empty
    } else if chars > NAME_MAX_CHARS {
        NameCheck::TooLong
    } else if !tidy {
        NameCheck::Untidy
    } else {
        NameCheck::Ok
    }
}

/// Whether `name` is a GMS name: at most [`GMS_NAME_MAX`] bytes, every one
/// an ASCII letter or digit.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == (name@.len() <= GMS_NAME_MAX && forall|i: int| 0 <= i < name@.len() ==> crate::ascii::is_alnum(#[trigger] name@[i])),
))]
#[must_use]
pub const fn gms_name_ok(name: &[u8]) -> bool {
    if name.len() > GMS_NAME_MAX {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= name@.len(),
            forall|j: int| 0 <= j < i ==> crate::ascii::is_alnum(#[trigger] name@[j]),
        decreases name@.len() - i
    ))]
    while i < name.len() {
        let b = name[i];
        if !((b'0' <= b && b <= b'9') || (b'A' <= b && b <= b'Z') || (b'a' <= b && b <= b'z')) {
            return false;
        }
        i += 1;
    }
    true
}

/// `v` as a `u16` when it is in `min..=max`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= min, max <= u16::MAX,
    ensures r == if min <= v && v <= max { Some(v as u16) } else { None },
))]
#[must_use]
pub const fn bounded_u16(v: i64, min: i64, max: i64) -> Option<u16> {
    if in_range(v, min, max) {
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "in range: 0 <= min <= v <= max <= u16::MAX"
        )]
        let r = v as u16;
        Some(r)
    } else {
        None
    }
}

/// `v` as a `u8` when it is in `min..=max`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= min, max <= u8::MAX,
    ensures r == if min <= v && v <= max { Some(v as u8) } else { None },
))]
#[must_use]
pub const fn bounded_u8(v: i64, min: i64, max: i64) -> Option<u8> {
    if in_range(v, min, max) {
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "in range: 0 <= min <= v <= max <= u8::MAX"
        )]
        let r = v as u8;
        Some(r)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capture_window_is_exact_at_the_edges() {
        assert!(captured_at_ok(0, MAX_FUTURE_MS));
        assert!(!captured_at_ok(0, MAX_FUTURE_MS + 1));
        assert!(captured_at_ok(i64::MAX, i64::MAX));
        assert!(captured_at_ok(i64::MIN, i64::MIN + MAX_FUTURE_MS));
        assert!(!captured_at_ok(i64::MIN, i64::MIN + MAX_FUTURE_MS + 1));
    }

    #[test]
    fn token_chains() {
        use crate::policy::{Link, chain_expiry};
        let live = |e| Link { revoked: false, expires_at: e };
        assert_eq!(chain_expiry(&[live(None)], 5), Some(None));
        assert_eq!(chain_expiry(&[live(Some(30)), live(Some(10)), live(None)], 5), Some(Some(10)));
        assert_eq!(chain_expiry(&[live(Some(30)), live(Some(5))], 5), None, "expires exactly now");
        assert_eq!(chain_expiry(&[live(None), Link { revoked: true, expires_at: None }], 5), None);
        assert!(next_batch_ok(4, 5) && !next_batch_ok(4, 4) && !next_batch_ok(u64::MAX, 0));
    }

    #[test]
    fn percentage_limits() {
        assert!(ignore_defense_ok(9_999) && !ignore_defense_ok(10_000));
        assert!(cooldown_reduction_ok(10_000) && !cooldown_reduction_ok(10_001));
        assert!(percentage_ok(0) && !percentage_ok(-1));
    }
}
