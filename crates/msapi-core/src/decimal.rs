//! Parsing a decimal string into an integer count of `10^-dp` units, checked
//! by Verus.
//!
//! [`parse_decimal`] is the whole of [`Fixed`](crate::Fixed)'s string parser.
//! Its spec says exactly which strings it accepts (`-?D+(\.D+)?` with at most
//! `dp` fraction digits) and what value each one has, so `"93.14"` is `9314`
//! hundredths because the proof says so, not because a test happened to try it.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Why a string is not a decimal of the requested precision.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecimalError {
    /// Not of the form `-?D+(\.D+)?`.
    Invalid,
    /// More fraction digits than the precision keeps.
    TooPrecise,
    /// The scaled value does not fit an `i64`.
    OutOfRange,
}

/// `2^63`, the magnitude of `i64::MIN`: the largest magnitude any result has.
#[cfg_attr(feature = "verus", verus_verify)]
const LIMIT: u128 = 0x8000_0000_0000_0000;

#[cfg(feature = "verus")]
verus! {

/// An ASCII digit.
pub open spec fn is_digit(b: u8) -> bool {
    48 <= b && b <= 57
}

/// Every byte of `s` is an ASCII digit.
pub open spec fn all_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i])
}

/// The number the digits of `s` spell, most significant first (`0` when empty).
pub open spec fn digits_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { digits_value(s.drop_last()) * 10 + (s.last() as int - 48) as nat }
}

/// `10^n`.
pub open spec fn pow10(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { pow10((n - 1) as nat) * 10 }
}

/// `1` when `s` starts with `-`, else `0`.
pub open spec fn sign_len(s: Seq<u8>) -> int {
    if s.len() > 0 && s[0] == 45u8 { 1 } else { 0 }
}

/// `s` is `-?D+(\.D+)?` with the whole digits ending at `k`: either `k` is the
/// end, or a `.` at `k` is followed by one or more digits to the end.
pub open spec fn splits_at(s: Seq<u8>, k: int) -> bool {
    &&& sign_len(s) < k <= s.len()
    &&& all_digits(s.subrange(sign_len(s), k))
    &&& (k == s.len() || (s[k] == 46u8 && k + 1 < s.len() && all_digits(s.subrange(k + 1, s.len() as int))))
}

/// The whole-number digits.
pub open spec fn whole_digits(s: Seq<u8>, k: int) -> Seq<u8> {
    s.subrange(sign_len(s), k)
}

/// The fraction digits (empty without a `.`).
pub open spec fn frac_digits(s: Seq<u8>, k: int) -> Seq<u8> {
    if k == s.len() { Seq::empty() } else { s.subrange(k + 1, s.len() as int) }
}

/// How many fraction digits there are.
pub open spec fn frac_len(s: Seq<u8>, k: int) -> nat {
    frac_digits(s, k).len()
}

/// `whole·10^dp + frac·10^(dp − frac_len)`.
pub open spec fn magnitude(s: Seq<u8>, k: int, dp: nat) -> nat {
    digits_value(whole_digits(s, k)) * pow10(dp)
        + digits_value(frac_digits(s, k)) * pow10((dp - frac_len(s, k)) as nat)
}

/// The value of the decimal `s` in units of `10^-dp`.
pub open spec fn decimal_value(s: Seq<u8>, k: int, dp: nat) -> int {
    if sign_len(s) == 1 { -magnitude(s, k, dp) } else { magnitude(s, k, dp) as int }
}

/// All the digits read as one integer: `whole·10^frac_len + frac`.
spec fn scaled_digits(s: Seq<u8>, k: int) -> nat {
    digits_value(whole_digits(s, k)) * pow10(frac_len(s, k)) + digits_value(frac_digits(s, k))
}

spec fn digits_between(s: Seq<u8>, lo: int, hi: int) -> bool {
    forall|i: int| lo <= i < hi ==> is_digit(#[trigger] s[i])
}

proof fn lemma_all_digits_range(s: Seq<u8>, lo: int, hi: int)
    requires 0 <= lo <= hi <= s.len(),
    ensures all_digits(s.subrange(lo, hi)) == digits_between(s, lo, hi),
{
    if all_digits(s.subrange(lo, hi)) {
        assert forall|i: int| lo <= i < hi implies is_digit(#[trigger] s[i]) by {
            assert(s.subrange(lo, hi)[i - lo] == s[i]);
        }
    }
    if digits_between(s, lo, hi) {
        assert forall|i: int| 0 <= i < hi - lo implies is_digit(#[trigger] s.subrange(lo, hi)[i]) by {
            assert(s.subrange(lo, hi)[i] == s[lo + i]);
        }
    }
}

/// A string splits in at most one place, so the value of a decimal is unique.
pub proof fn lemma_split_unique(s: Seq<u8>, k1: int, k2: int)
    requires splits_at(s, k1), splits_at(s, k2),
    ensures k1 == k2,
{
    let a = sign_len(s);
    lemma_all_digits_range(s, a, k1);
    lemma_all_digits_range(s, a, k2);
    if k1 < k2 {
        assert(is_digit(s[k1]));
    } else if k2 < k1 {
        assert(is_digit(s[k2]));
    }
}

/// Where the whole digits stop is the only place a split can be.
proof fn lemma_split_point(s: Seq<u8>, k: int, k2: int)
    requires
        sign_len(s) <= k <= s.len(),
        digits_between(s, sign_len(s), k),
        k == s.len() || !is_digit(s[k]),
        splits_at(s, k2),
    ensures k2 == k,
{
    lemma_all_digits_range(s, sign_len(s), k2);
    if k2 < k {
        assert(is_digit(s[k2]));
    } else if k < k2 {
        assert(is_digit(s[k]));
    }
}

proof fn lemma_pow10_pos(n: nat)
    ensures pow10(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow10_pos((n - 1) as nat);
    }
}

proof fn lemma_pow10_add(a: nat, b: nat)
    ensures pow10(a + b) == pow10(a) * pow10(b),
    decreases b,
{
    if b > 0 {
        lemma_pow10_add(a, (b - 1) as nat);
        let pa = pow10(a);
        let pb = pow10((b - 1) as nat);
        assert((a + b - 1) as nat == a + (b - 1) as nat);
        assert(pow10(a + b) == pow10(a + (b - 1) as nat) * 10);
        assert(pow10(b) == pb * 10);
        assert(pa * pb * 10 == pa * (pb * 10)) by (nonlinear_arith);
    } else {
        assert(pow10(0) == 1);
        let pa = pow10(a);
        assert(pa * 1 == pa);
    }
}

/// Splitting a digit string at `m`: `value(x) = value(x[..m])·10^(len−m) + value(x[m..])`.
proof fn lemma_digits_concat(x: Seq<u8>, m: int)
    requires 0 <= m <= x.len(),
    ensures
        digits_value(x) == digits_value(x.subrange(0, m)) * pow10((x.len() - m) as nat)
            + digits_value(x.subrange(m, x.len() as int)),
    decreases x.len(),
{
    let n = x.len() as int;
    if m == n {
        assert(x.subrange(0, m) =~= x);
        assert(x.subrange(m, n).len() == 0);
        assert(digits_value(x.subrange(m, n)) == 0);
        assert(pow10(0) == 1);
        let v = digits_value(x);
        assert(v * 1 == v);
    } else {
        let y = x.drop_last();
        lemma_digits_concat(y, m);
        assert(y.subrange(0, m) =~= x.subrange(0, m));
        assert(x.subrange(m, n).drop_last() =~= y.subrange(m, n - 1));
        assert(x.subrange(m, n).last() == x.last());
        let a = digits_value(x.subrange(0, m));
        let p = pow10((n - 1 - m) as nat);
        let b = digits_value(y.subrange(m, n - 1));
        let d = (x.last() as int - 48) as nat;
        assert(pow10((n - m) as nat) == p * 10);
        assert(digits_value(x) == digits_value(y) * 10 + d);
        assert(digits_value(x.subrange(m, n)) == b * 10 + d);
        assert((a * p + b) * 10 + d == a * (p * 10) + (b * 10 + d)) by (nonlinear_arith);
    }
}

proof fn lemma_magnitude(s: Seq<u8>, k: int, dp: nat)
    requires frac_len(s, k) <= dp,
    ensures magnitude(s, k, dp) == scaled_digits(s, k) * pow10((dp - frac_len(s, k)) as nat),
{
    let f = frac_len(s, k);
    let z = (dp - f) as nat;
    lemma_pow10_add(f, z);
    let w = digits_value(whole_digits(s, k));
    let r = digits_value(frac_digits(s, k));
    assert(w * (pow10(f) * pow10(z)) + r * pow10(z) == (w * pow10(f) + r) * pow10(z)) by (nonlinear_arith);
}

/// Any prefix of the whole digits is at most the magnitude.
proof fn lemma_whole_prefix_bound(s: Seq<u8>, k: int, dp: nat, i: int)
    requires splits_at(s, k), sign_len(s) <= i <= k,
    ensures digits_value(s.subrange(sign_len(s), i)) <= magnitude(s, k, dp),
{
    let a = sign_len(s);
    let w = whole_digits(s, k);
    assert(w.subrange(0, i - a) =~= s.subrange(a, i));
    lemma_digits_concat(w, i - a);
    let pre = digits_value(s.subrange(a, i));
    let p = pow10((w.len() - (i - a)) as nat);
    let rest = digits_value(w.subrange(i - a, w.len() as int));
    lemma_pow10_pos((w.len() - (i - a)) as nat);
    assert(pre <= pre * p + rest) by (nonlinear_arith) requires p >= 1;
    lemma_pow10_pos(dp);
    let wv = digits_value(w);
    let q = pow10(dp);
    assert(wv <= wv * q) by (nonlinear_arith) requires q >= 1;
}

/// The value of the whole digits followed by a prefix of the fraction digits
/// is at most `scaled_digits`, which is at most the magnitude.
proof fn lemma_frac_prefix_bound(s: Seq<u8>, k: int, dp: nat, j: int)
    requires splits_at(s, k), k < s.len(), frac_len(s, k) <= dp, k + 1 <= j <= s.len(),
    ensures
        digits_value(whole_digits(s, k)) * pow10((j - k - 1) as nat) + digits_value(s.subrange(k + 1, j))
            <= magnitude(s, k, dp),
{
    let f = frac_digits(s, k);
    let m = j - k - 1;
    let fl = f.len();
    assert(f.subrange(0, m) =~= s.subrange(k + 1, j));
    lemma_digits_concat(f, m);
    lemma_pow10_add(m as nat, (fl - m) as nat);
    lemma_pow10_pos((fl - m) as nat);
    let w = digits_value(whole_digits(s, k));
    let pm = pow10(m as nat);
    let pr = pow10((fl - m) as nat);
    let fp = digits_value(s.subrange(k + 1, j));
    let rest = digits_value(f.subrange(m, fl as int));
    assert(w * pm + fp <= w * (pm * pr) + (fp * pr + rest)) by (nonlinear_arith) requires pr >= 1;
    lemma_magnitude(s, k, dp);
    lemma_pow10_pos((dp - fl) as nat);
    let sd = scaled_digits(s, k);
    let pz = pow10((dp - fl) as nat);
    assert(sd <= sd * pz) by (nonlinear_arith) requires pz >= 1;
}

/// Appending zeros: `scaled_digits·10^t` is at most the magnitude while `t`
/// is at most the number of zeros the precision adds.
proof fn lemma_pad_bound(s: Seq<u8>, k: int, dp: nat, t: nat)
    requires frac_len(s, k) <= dp, t <= dp - frac_len(s, k),
    ensures scaled_digits(s, k) * pow10(t) <= magnitude(s, k, dp),
{
    let z = (dp - frac_len(s, k)) as nat;
    lemma_magnitude(s, k, dp);
    lemma_pow10_add(t, (z - t) as nat);
    lemma_pow10_pos((z - t) as nat);
    let sd = scaled_digits(s, k);
    let pt = pow10(t);
    let pr = pow10((z - t) as nat);
    assert(sd * pt <= sd * (pt * pr)) by (nonlinear_arith) requires pr >= 1;
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == is_digit(b)))]
const fn is_digit_byte(b: u8) -> bool {
    b'0' <= b && b <= b'9'
}

/// Parses `-?D+(\.D+)?` into an integer count of `10^-dp` units.
///
/// `"93.14"` at two places is `9314`; `"93.1"` is `9310`; `"-5"` is `-500`.
/// A leading `+`, an exponent, a bare `.5` or `5.` and anything with spaces
/// are [`DecimalError::Invalid`]. More than `dp` fraction digits is
/// [`DecimalError::TooPrecise`], never a rounding. A value outside `i64` is
/// [`DecimalError::OutOfRange`]. A malformed string is `Invalid` even when it
/// is also too long, and a too-precise one is `TooPrecise` even when it is
/// also too large.
///
/// Verus proves the result is exactly this: `Ok(v)` when the bytes split as
/// `-?D+(\.D+)?` (in exactly one place, by `lemma_split_unique`) with at most
/// `dp` fraction digits and `v == ±(whole·10^dp + frac·10^(dp − frac_len))`.
///
/// # Errors
///
/// As above.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Ok(v) => exists|k: int| #[trigger] splits_at(text@, k) && frac_len(text@, k) <= dp
                && v as int == decimal_value(text@, k, dp as nat),
            Err(DecimalError::Invalid) => forall|k: int| !(#[trigger] splits_at(text@, k)),
            Err(DecimalError::TooPrecise) => exists|k: int| #[trigger] splits_at(text@, k) && frac_len(text@, k) > dp,
            Err(DecimalError::OutOfRange) => exists|k: int| #[trigger] splits_at(text@, k) && frac_len(text@, k) <= dp
                && !(i64::MIN <= decimal_value(text@, k, dp as nat) && decimal_value(text@, k, dp as nat) <= i64::MAX),
        },
))]
#[allow(clippy::too_many_lines, reason = "most of the lines are ghost code that compiles away")]
pub fn parse_decimal(text: &[u8], dp: u32) -> Result<i64, DecimalError> {
    let len = text.len();
    let negative = len > 0 && text[0] == b'-';
    #[allow(clippy::bool_to_int_with_if, reason = "Verus has no spec for `usize::from(bool)`")]
    let a: usize = if negative { 1 } else { 0 };

    // Validate first, so a malformed string is `Invalid` however long it is.
    let mut k = a;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            len == text.len(),
            a == sign_len(text@),
            a <= k <= len,
            digits_between(text@, a as int, k as int),
        decreases len - k
    ))]
    while k < len && is_digit_byte(text[k]) {
        k += 1;
    }
    if k == a {
        proof! {
            assert forall|k2: int| !(#[trigger] splits_at(text@, k2)) by {
                if splits_at(text@, k2) {
                    lemma_split_point(text@, k as int, k2);
                }
            }
        }
        return Err(DecimalError::Invalid);
    }
    if k < len {
        if text[k] != b'.' || k + 1 == len {
            proof! {
                assert forall|k2: int| !(#[trigger] splits_at(text@, k2)) by {
                    if splits_at(text@, k2) {
                        lemma_split_point(text@, k as int, k2);
                    }
                }
            }
            return Err(DecimalError::Invalid);
        }
        let mut j = k + 1;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                len == text.len(),
                k < j <= len,
                digits_between(text@, k + 1, j as int),
            decreases len - j
        ))]
        while j < len && is_digit_byte(text[j]) {
            j += 1;
        }
        if j < len {
            proof! {
                assert forall|k2: int| !(#[trigger] splits_at(text@, k2)) by {
                    if splits_at(text@, k2) {
                        lemma_split_point(text@, k as int, k2);
                        lemma_all_digits_range(text@, k + 1, len as int);
                    }
                }
            }
            return Err(DecimalError::Invalid);
        }
        proof! { lemma_all_digits_range(text@, k + 1, len as int); }
    }
    proof! {
        lemma_all_digits_range(text@, a as int, k as int);
        assert(splits_at(text@, k as int));
    }

    let fraction: usize = if k < len { len - k - 1 } else { 0 };
    if fraction as u64 > dp as u64 {
        return Err(DecimalError::TooPrecise);
    }

    // Accumulate the whole digits, then the fraction digits, then the zeros
    // the precision adds. Every partial value is at most the final magnitude,
    // so passing `LIMIT` early already means the result does not fit.
    let mut acc: u128 = 0;
    let mut i = a;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            len == text.len(),
            a == sign_len(text@),
            a <= i <= k <= len,
            splits_at(text@, k as int),
            frac_len(text@, k as int) <= dp,
            digits_between(text@, a as int, k as int),
            acc == digits_value(text@.subrange(a as int, i as int)),
            acc <= LIMIT,
        decreases k - i
    ))]
    while i < k {
        proof! {
            assert(text@.subrange(a as int, i + 1).drop_last() =~= text@.subrange(a as int, i as int));
            lemma_whole_prefix_bound(text@, k as int, dp as nat, i + 1);
        }
        acc = acc * 10 + (text[i] - b'0') as u128;
        i += 1;
        if acc > LIMIT {
            return Err(DecimalError::OutOfRange);
        }
    }
    proof! {
        assert(text@.subrange(a as int, k as int) =~= whole_digits(text@, k as int));
        lemma_pow10_pos(0);
    }
    if k < len {
        let mut j = k + 1;
        proof! {
            assert(text@.subrange(k + 1, k + 1).len() == 0);
            assert(digits_value(text@.subrange(k + 1, k + 1)) == 0);
            assert(pow10(0) == 1);
            let w = digits_value(whole_digits(text@, k as int));
            assert(w * 1 == w);
        }
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                len == text.len(),
                k < j <= len,
                splits_at(text@, k as int),
                frac_len(text@, k as int) <= dp,
                digits_between(text@, k + 1, len as int),
                acc == digits_value(whole_digits(text@, k as int)) * pow10((j - k - 1) as nat)
                    + digits_value(text@.subrange(k + 1, j as int)),
                acc <= LIMIT,
            decreases len - j
        ))]
        while j < len {
            proof! {
                assert(text@.subrange(k + 1, j + 1).drop_last() =~= text@.subrange(k + 1, j as int));
                lemma_frac_prefix_bound(text@, k as int, dp as nat, j + 1);
                let w = digits_value(whole_digits(text@, k as int));
                let p = pow10((j - k - 1) as nat);
                let f = digits_value(text@.subrange(k + 1, j as int));
                assert(pow10((j + 1 - k - 1) as nat) == p * 10);
                assert((w * p + f) * 10 == w * (p * 10) + f * 10) by (nonlinear_arith);
            }
            acc = acc * 10 + (text[j] - b'0') as u128;
            j += 1;
            if acc > LIMIT {
                return Err(DecimalError::OutOfRange);
            }
        }
        proof! { assert(text@.subrange(k + 1, len as int) =~= frac_digits(text@, k as int)); }
    }
    proof! {
        if k == len {
            assert(frac_digits(text@, k as int).len() == 0);
            assert(digits_value(frac_digits(text@, k as int)) == 0);
            assert(pow10(0) == 1);
            let w = digits_value(whole_digits(text@, k as int));
            assert(w * 1 == w);
        }
        assert(acc == scaled_digits(text@, k as int));
        lemma_pow10_pos(0);
    }

    let zeros = dp as u64 - fraction as u64;
    let mut t: u64 = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            splits_at(text@, k as int),
            frac_len(text@, k as int) <= dp,
            zeros == dp - frac_len(text@, k as int),
            t <= zeros,
            acc == scaled_digits(text@, k as int) * pow10(t as nat),
            acc <= LIMIT,
        decreases zeros - t
    ))]
    while t < zeros && acc != 0 {
        proof! {
            lemma_pad_bound(text@, k as int, dp as nat, (t + 1) as nat);
            let sd = scaled_digits(text@, k as int);
            let p = pow10(t as nat);
            assert(pow10((t + 1) as nat) == p * 10);
            assert(sd * p * 10 == sd * (p * 10)) by (nonlinear_arith);
        }
        acc *= 10;
        t += 1;
        if acc > LIMIT {
            return Err(DecimalError::OutOfRange);
        }
    }
    proof! {
        lemma_magnitude(text@, k as int, dp as nat);
        lemma_pow10_pos(t as nat);
        let sd = scaled_digits(text@, k as int);
        let p = pow10(t as nat);
        let pz = pow10(zeros as nat);
        if acc == 0 {
            assert(sd == 0) by (nonlinear_arith) requires sd * p == 0, p >= 1;
            assert(sd * pz == 0) by (nonlinear_arith) requires sd == 0;
        }
        assert(acc == magnitude(text@, k as int, dp as nat));
    }

    if negative {
        if acc == LIMIT { Ok(i64::MIN) } else { Ok(-(acc as i64)) }
    } else if acc > i64::MAX as u128 {
        proof! {
            assert(decimal_value(text@, k as int, dp as nat) == acc as int);
            assert(splits_at(text@, k as int));
        }
        Err(DecimalError::OutOfRange)
    } else {
        Ok(acc as i64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scales_to_the_precision() {
        assert_eq!(parse_decimal(b"93.14", 2), Ok(9314));
        assert_eq!(parse_decimal(b"93.1", 2), Ok(9310));
        assert_eq!(parse_decimal(b"-5", 2), Ok(-500));
        assert_eq!(parse_decimal(b"-0", 2), Ok(0));
        assert_eq!(parse_decimal(b"007", 0), Ok(7));
        assert_eq!(parse_decimal(b"12.345", 3), Ok(12_345));
    }

    #[test]
    fn reaches_both_ends_of_i64() {
        assert_eq!(parse_decimal(b"9223372036854775807", 0), Ok(i64::MAX));
        assert_eq!(parse_decimal(b"-9223372036854775808", 0), Ok(i64::MIN));
        assert_eq!(parse_decimal(b"-92233720368547758.08", 2), Ok(i64::MIN));
        assert_eq!(parse_decimal(b"9223372036854775808", 0), Err(DecimalError::OutOfRange));
        assert_eq!(parse_decimal(b"1", 19), Err(DecimalError::OutOfRange));
        assert_eq!(parse_decimal(b"99999999999999999999999", 0), Err(DecimalError::OutOfRange));
    }

    #[test]
    fn zero_is_cheap_at_any_precision() {
        assert_eq!(parse_decimal(b"0.0", u32::MAX), Ok(0));
    }

    #[test]
    fn rejects_in_order_invalid_then_too_precise_then_range() {
        for bad in ["", "-", ".5", "5.", "1e3", "1.2.3", "--1", "+1", " 1", "1 ", "93.14%", "99999999999999999999x"] {
            assert_eq!(parse_decimal(bad.as_bytes(), 2), Err(DecimalError::Invalid), "{bad:?}");
        }
        assert_eq!(parse_decimal(b"93.145", 2), Err(DecimalError::TooPrecise));
        assert_eq!(parse_decimal(b"99999999999999999999.145", 2), Err(DecimalError::TooPrecise));
    }
}
