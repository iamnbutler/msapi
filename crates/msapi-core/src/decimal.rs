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
    clippy::cast_sign_loss,
    clippy::vec_init_then_push,
    reason = "plain casts and pushes are what Verus checks; each cast here is proven in range"
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

#[cfg(feature = "verus")]
verus! {

/// The decimal digits of `n`, most significant first, with no leading zeros
/// (`"0"` for zero).
pub open spec fn digits_of(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 { seq![(48 + n) as u8] } else { digits_of(n / 10).push((48 + n % 10) as u8) }
}

/// The low `w` decimal digits of `n`, zero-padded to exactly `w` characters.
pub open spec fn padded(n: nat, w: nat) -> Seq<u8>
    decreases w,
{
    if w == 0 { Seq::empty() } else { padded(n / 10, (w - 1) as nat).push((48 + n % 10) as u8) }
}

/// `|v|`.
pub open spec fn abs(v: int) -> nat {
    if v < 0 { (-v) as nat } else { v as nat }
}

/// The text of `v` units of `10^-dp`: `-` for negatives, the whole part with
/// no leading zeros, then (when `dp > 0`) `.` and exactly `dp` fraction digits.
pub open spec fn decimal_text(v: int, dp: nat) -> Seq<u8> {
    (if v < 0 { seq![45u8] } else { Seq::empty() })
        + digits_of(abs(v) / pow10(dp))
        + (if dp == 0 { Seq::empty() } else { seq![46u8] + padded(abs(v) % pow10(dp), dp) })
}

proof fn lemma_push_value(s: Seq<u8>, c: u8)
    requires is_digit(c),
    ensures digits_value(s.push(c)) == digits_value(s) * 10 + (c - 48),
{
    assert(s.push(c).drop_last() =~= s);
}

/// `digits_of(n)` is non-empty, all digits, spells `n`, and has no leading zero.
pub proof fn lemma_digits_of(n: nat)
    ensures
        digits_of(n).len() >= 1,
        all_digits(digits_of(n)),
        digits_value(digits_of(n)) == n,
        n >= 1 ==> digits_of(n)[0] != 48,
    decreases n,
{
    if n < 10 {
        let c = (48 + n) as u8;
        assert(seq![c].drop_last() =~= Seq::<u8>::empty());
        assert(seq![c].last() == c);
        assert(digits_value(Seq::<u8>::empty()) == 0);
        assert(digits_value(seq![c]) == digits_value(seq![c].drop_last()) * 10 + (c as int - 48) as nat);
    } else {
        let q = n / 10;
        let c = (48 + n % 10) as u8;
        lemma_digits_of(q);
        lemma_push_value(digits_of(q), c);
        assert(n == q * 10 + n % 10);
        let d = digits_of(q).push(c);
        assert forall|i: int| 0 <= i < d.len() implies is_digit(#[trigger] d[i]) by {
            if i < d.len() - 1 {
                assert(d[i] == digits_of(q)[i]);
            }
        }
        assert(d[0] == digits_of(q)[0]);
    }
}

/// `padded(n, w)` is `w` digits spelling `n mod 10^w`.
pub proof fn lemma_padded(n: nat, w: nat)
    ensures
        padded(n, w).len() == w,
        all_digits(padded(n, w)),
        digits_value(padded(n, w)) == n % pow10(w),
    decreases w,
{
    if w > 0 {
        let q = n / 10;
        let c = (48 + n % 10) as u8;
        let w1 = (w - 1) as nat;
        lemma_padded(q, w1);
        lemma_push_value(padded(q, w1), c);
        let d = padded(q, w1).push(c);
        assert forall|i: int| 0 <= i < d.len() implies is_digit(#[trigger] d[i]) by {
            if i < d.len() - 1 {
                assert(d[i] == padded(q, w1)[i]);
            }
        }
        lemma_pow10_pos(w1);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(n as int, 10, pow10(w1) as int);
        assert(pow10(w) == 10 * pow10(w1)) by (nonlinear_arith)
            requires pow10(w) == pow10(w1) * 10;
    }
}

/// [`decimal_text`] splits as a decimal with exactly `dp` fraction digits and
/// value `v`, so [`parse_decimal`] reads it back as `v` (see
/// `format_then_parse`).
pub proof fn lemma_text_round_trip(v: int, dp: nat)
    ensures
        splits_at(decimal_text(v, dp), text_split(v, dp)),
        frac_len(decimal_text(v, dp), text_split(v, dp)) == dp,
        decimal_value(decimal_text(v, dp), text_split(v, dp), dp) == v,
{
    let s = decimal_text(v, dp);
    let a = abs(v);
    let p = pow10(dp);
    lemma_pow10_pos(dp);
    let sg: Seq<u8> = if v < 0 { seq![45u8] } else { Seq::empty() };
    let w = digits_of(a / p);
    let t: Seq<u8> = if dp == 0 { Seq::empty() } else { seq![46u8] + padded(a % p, dp) };
    lemma_digits_of(a / p);
    lemma_padded(a % p, dp);
    assert(s == sg + w + t);
    let k = text_split(v, dp);
    assert(k == sg.len() + w.len());
    // The sign.
    if v < 0 {
        assert(s[0] == 45u8);
    } else {
        assert(s[0] == w[0]);
        assert(is_digit(w[0]));
    }
    assert(sign_len(s) == sg.len());
    assert(s.subrange(sign_len(s), k) =~= w);
    // The fraction.
    if dp == 0 {
        assert(k == s.len());
        assert(frac_digits(s, k) =~= Seq::<u8>::empty());
    } else {
        assert(s[k] == 46u8);
        assert(s.subrange(k + 1, s.len() as int) =~= padded(a % p, dp));
    }
    // The value.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, p as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(a as int, p as int);
    vstd::arithmetic::div_mod::lemma_small_mod((a % p) as nat, p);
    assert(pow10((dp - dp) as nat) == 1);
    assert(whole_digits(s, k) == w);
    if dp == 0 {
        assert(digits_value(frac_digits(s, k)) == 0);
        assert(p == 1);
        assert(a % p == 0);
    } else {
        assert(frac_digits(s, k) == padded(a % p, dp));
    }
    assert(digits_value(frac_digits(s, k)) == a % p);
    assert(frac_len(s, k) == dp);
    assert(magnitude(s, k, dp) == digits_value(w) * p + digits_value(frac_digits(s, k)) * pow10(0));
    assert(magnitude(s, k, dp) == (a / p) * p + a % p) by (nonlinear_arith)
        requires
            magnitude(s, k, dp) == digits_value(w) * p + digits_value(frac_digits(s, k)) * pow10(0),
            pow10(0) == 1,
            digits_value(w) == a / p,
            digits_value(frac_digits(s, k)) == a % p;
    assert(magnitude(s, k, dp) == a);
    if v < 0 {
        assert(decimal_value(s, k, dp) == -(a as int));
    } else {
        assert(decimal_value(s, k, dp) == a as int);
    }
}

/// Where [`decimal_text`] splits: after the sign and the whole digits.
pub open spec fn text_split(v: int, dp: nat) -> int {
    (if v < 0 { 1int } else { 0int }) + digits_of(abs(v) / pow10(dp)).len()
}

/// Formatting then parsing gives back the value, for every `i64` and every
/// precision `Fixed` allows.
fn format_then_parse(v: i64, dp: u32) -> (r: Result<i64, DecimalError>)
    requires dp <= 18,
    ensures r == Ok::<i64, DecimalError>(v),
{
    let s = format_decimal(v, dp);
    let r = parse_decimal(s.as_slice(), dp);
    proof {
        let t = decimal_text(v as int, dp as nat);
        let k0 = text_split(v as int, dp as nat);
        lemma_text_round_trip(v as int, dp as nat);
        assert(s@ == t);
        match r {
            Ok(x) => {
                let k = choose|k: int| #[trigger] splits_at(t, k) && frac_len(t, k) <= dp
                    && x as int == decimal_value(t, k, dp as nat);
                lemma_split_unique(t, k, k0);
            },
            Err(DecimalError::Invalid) => {
                assert(!splits_at(t, k0));
            },
            Err(DecimalError::TooPrecise) => {
                let k = choose|k: int| #[trigger] splits_at(t, k) && frac_len(t, k) > dp;
                lemma_split_unique(t, k, k0);
            },
            Err(DecimalError::OutOfRange) => {
                let k = choose|k: int| #[trigger] splits_at(t, k) && frac_len(t, k) <= dp
                    && !(i64::MIN <= decimal_value(t, k, dp as nat) && decimal_value(t, k, dp as nat) <= i64::MAX);
                lemma_split_unique(t, k, k0);
            },
        }
    }
    r
}

} // verus!

/// `10^dp` for the precisions `Fixed` allows.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires dp <= 18,
    ensures r as nat == pow10(dp as nat)
))]
const fn pow10_u64(dp: u32) -> u64 {
    let mut p: u64 = 1;
    let mut i: u32 = 0;
    proof! {
        reveal_with_fuel(pow10, 19);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= dp <= 18,
            p as nat == pow10(i as nat),
            pow10(18) == 1_000_000_000_000_000_000,
        decreases dp - i
    ))]
    while i < dp {
        proof! {
            lemma_pow10_add((i + 1) as nat, (18 - i - 1) as nat);
            lemma_pow10_pos((18 - i - 1) as nat);
            assert(pow10((i + 1) as nat) <= pow10(18)) by (nonlinear_arith)
                requires pow10(18) == pow10((i + 1) as nat) * pow10((18 - i - 1) as nat),
                    pow10((18 - i - 1) as nat) >= 1;
        }
        p *= 10;
        i += 1;
    }
    p
}

/// The decimal digits of `n`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r@ == digits_of(n as nat),
    decreases n
))]
fn digits(n: u128) -> Vec<u8> {
    if n < 10 {
        let mut v = Vec::new();
        v.push(b'0' + n as u8);
        proof! {
            assert(v@ =~= seq![(48 + n) as u8]);
        }
        v
    } else {
        let mut v = digits(n / 10);
        v.push(b'0' + (n % 10) as u8);
        v
    }
}

/// The decimal text of `n`: its digits, with no leading zeros.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == digits_of(n as nat)))]
#[must_use]
pub fn format_uint(n: u128) -> Vec<u8> {
    digits(n)
}

/// The low `w` decimal digits of `n`, zero-padded.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r@ == padded(n as nat, w as nat),
    decreases w
))]
fn padded_digits(n: u64, w: u32) -> Vec<u8> {
    if w == 0 {
        let v = Vec::new();
        proof! {
            assert(v@ =~= Seq::<u8>::empty());
        }
        v
    } else {
        let mut v = padded_digits(n / 10, w - 1);
        v.push(b'0' + (n % 10) as u8);
        v
    }
}

/// Appends `s` to `out`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    ensures final(out)@ == old(out)@ + s@
))]
fn push_all(out: &mut Vec<u8>, s: &[u8]) {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s@.len(),
            out@ == old(out)@ + s@.take(i as int),
        decreases s@.len() - i
    ))]
    while i < s.len() {
        proof! {
            assert(s@.take(i + 1) =~= s@.take(i as int).push(s@[i as int]));
        }
        out.push(s[i]);
        i += 1;
    }
    proof! {
        assert(s@.take(s@.len() as int) =~= s@);
    }
}

/// The text of `raw` units of `10^-dp`, e.g. `9314` at two places is `"93.14"`
/// and `-5` is `"-0.05"`.
///
/// Verus proves the output is exactly [`decimal_text`] and that
/// [`parse_decimal`] reads it back as `raw` (`lemma_text_round_trip`,
/// `format_then_parse`).
///
/// # Panics
///
/// Never: `dp <= 18` is required, and is what `Fixed`'s `10^DP` in an `i64`
/// already forces.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires dp <= 18,
    ensures r@ == decimal_text(raw as int, dp as nat)
))]
#[must_use]
pub fn format_decimal(raw: i64, dp: u32) -> Vec<u8> {
    let a: u64 = if raw < 0 { (-(raw as i128)) as u64 } else { raw as u64 };
    let p = pow10_u64(dp);
    proof! {
        lemma_pow10_pos(dp as nat);
    }
    let mut out: Vec<u8> = Vec::new();
    if raw < 0 {
        out.push(b'-');
    }
    let whole = digits((a / p) as u128);
    push_all(&mut out, whole.as_slice());
    if dp > 0 {
        out.push(b'.');
        let frac = padded_digits(a % p, dp);
        push_all(&mut out, frac.as_slice());
    }
    proof! {
        assert(a as nat == abs(raw as int));
        assert(out@ =~= decimal_text(raw as int, dp as nat));
    }
    out
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

    /// The formatting `Fixed` used before it moved here, kept to show the
    /// proven version prints exactly the same.
    fn old_format(raw: i64, dp: u32) -> String {
        let sign = if raw < 0 { "-" } else { "" };
        let abs = raw.unsigned_abs();
        let scale = 10_u64.pow(dp);
        if dp == 0 {
            format!("{sign}{abs}")
        } else {
            format!("{sign}{}.{:0width$}", abs / scale, abs % scale, width = dp as usize)
        }
    }

    #[test]
    fn formatting_matches_the_old_output_and_round_trips() {
        let mut values = vec![0, 1, -1, 9, 10, 99, 100, -5, 9314, -9314, 123_456_789, i64::MAX, i64::MIN, i64::MIN + 1];
        let mut x: i64 = 1;
        for _ in 0..18 {
            x *= 10;
            values.extend([x - 1, x, x + 1, -x, -(x - 1)]);
        }
        for dp in 0..=18 {
            for &v in &values {
                let text = format_decimal(v, dp);
                assert_eq!(String::from_utf8(text.clone()).unwrap(), old_format(v, dp), "{v} at {dp}");
                assert_eq!(parse_decimal(&text, dp), Ok(v), "{v} at {dp}");
            }
        }
    }
}
