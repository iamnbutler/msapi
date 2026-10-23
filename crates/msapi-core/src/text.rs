//! Text as the HTTP layer sees it: UTF-8 bytes. Trimming, counting
//! characters and parsing numbers, each checked by Verus against a spec.
//!
//! The specs follow the standard library: [`trim`] removes what `str::trim`
//! removes (Unicode `White_Space`), [`char_count`] is `str::chars().count()`,
//! and [`parse_u64`] / [`parse_hex`] accept what `u64::from_str` and
//! `usize::from_str_radix(_, 16)` accept. Inputs are the bytes of a `&str`,
//! so they are valid UTF-8; the tests compare each against the standard
//! library on every whitespace character and on edge cases.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::decimal::{all_digits, digits_value, is_digit};

#[cfg(feature = "verus")]
verus! {

/// The length of the Unicode `White_Space` character `s` starts with, or 0.
///
/// U+0009–U+000D and U+0020 (one byte); U+0085 and U+00A0 (two); U+1680,
/// U+2000–U+200A, U+2028, U+2029, U+202F, U+205F and U+3000 (three).
pub open spec fn ws_prefix(s: Seq<u8>) -> nat {
    if s.len() >= 1 && ((9 <= s[0] && s[0] <= 13) || s[0] == 32) {
        1
    } else if s.len() >= 2 && s[0] == 0xC2 && (s[1] == 0x85 || s[1] == 0xA0) {
        2
    } else if s.len() >= 3 && ws3(s[0], s[1], s[2]) {
        3
    } else {
        0
    }
}

/// The three-byte whitespace characters.
pub open spec fn ws3(a: u8, b: u8, c: u8) -> bool {
    (a == 0xE1 && b == 0x9A && c == 0x80)
        || (a == 0xE2 && b == 0x80 && ((0x80 <= c && c <= 0x8A) || c == 0xA8 || c == 0xA9 || c == 0xAF))
        || (a == 0xE2 && b == 0x81 && c == 0x9F)
        || (a == 0xE3 && b == 0x80 && c == 0x80)
}

/// The length of the whitespace character `s` ends with, or 0.
pub open spec fn ws_suffix(s: Seq<u8>) -> nat {
    let n = s.len() as int;
    if n >= 1 && ((9 <= s[n - 1] && s[n - 1] <= 13) || s[n - 1] == 32) {
        1
    } else if n >= 2 && s[n - 2] == 0xC2 && (s[n - 1] == 0x85 || s[n - 1] == 0xA0) {
        2
    } else if n >= 3 && ws3(s[n - 3], s[n - 2], s[n - 1]) {
        3
    } else {
        0
    }
}

/// How many bytes of whitespace `s` starts with.
pub open spec fn lead(s: Seq<u8>) -> nat
    decreases s.len(),
{
    let k = ws_prefix(s);
    if k == 0 || k > s.len() { 0 } else { k + lead(s.skip(k as int)) }
}

/// How many bytes of whitespace `s` ends with.
pub open spec fn trail(s: Seq<u8>) -> nat
    decreases s.len(),
{
    let k = ws_suffix(s);
    if k == 0 || k > s.len() { 0 } else { k + trail(s.subrange(0, s.len() - k)) }
}

/// `s` without leading and trailing whitespace: `str::trim`.
pub open spec fn trimmed(s: Seq<u8>) -> Seq<u8> {
    let t = s.skip(lead(s) as int);
    t.subrange(0, t.len() - trail(t))
}

proof fn lemma_lead_bound(s: Seq<u8>)
    ensures lead(s) <= s.len(),
    decreases s.len(),
{
    let k = ws_prefix(s);
    if k != 0 && k <= s.len() {
        lemma_lead_bound(s.skip(k as int));
    }
}

proof fn lemma_trail_bound(s: Seq<u8>)
    ensures trail(s) <= s.len(),
    decreases s.len(),
{
    let k = ws_suffix(s);
    if k != 0 && k <= s.len() {
        lemma_trail_bound(s.subrange(0, s.len() - k));
    }
}

/// Whether `b` begins a UTF-8 character (is not a continuation byte).
pub open spec fn starts_char(b: u8) -> bool {
    !(0x80 <= b && b < 0xC0)
}

/// How many characters the UTF-8 text `s` holds.
pub open spec fn chars(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { chars(s.drop_last()) + if starts_char(s.last()) { 1nat } else { 0nat } }
}

/// What `u64::from_str` accepts: an optional `+`, then one or more digits.
pub open spec fn u64_digits(s: Seq<u8>) -> Seq<u8> {
    if s.len() > 0 && s[0] == 43 { s.skip(1) } else { s }
}

/// `u64::from_str(s)`.
pub open spec fn parse_u64_spec(s: Seq<u8>) -> Option<u64> {
    let d = u64_digits(s);
    if d.len() > 0 && all_digits(d) && digits_value(d) <= u64::MAX { Some(digits_value(d) as u64) } else { None }
}

/// The value of an ASCII hex digit.
pub open spec fn hex(b: u8) -> Option<nat> {
    if 48 <= b && b <= 57 {
        Some((b - 48) as nat)
    } else if 97 <= b && b <= 102 {
        Some((b - 87) as nat)
    } else if 65 <= b && b <= 70 {
        Some((b - 55) as nat)
    } else {
        None
    }
}

/// Every byte of `s` is a hex digit.
pub open spec fn all_hex(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] hex(s[i])) is Some
}

/// The number the hex digits of `s` spell, most significant first.
pub open spec fn hex_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { hex_value(s.drop_last()) * 16 + hex(s.last()).unwrap_or(0) }
}

/// `usize::from_str_radix(s, 16)`.
pub open spec fn parse_hex_spec(s: Seq<u8>) -> Option<usize> {
    let d = u64_digits(s);
    if d.len() > 0 && all_hex(d) && hex_value(d) <= usize::MAX { Some(hex_value(d) as usize) } else { None }
}

/// A prefix's digits are worth no more than the whole's.
pub proof fn lemma_digits_prefix(s: Seq<u8>, k: int)
    requires 0 <= k <= s.len(),
    ensures digits_value(s.subrange(0, k)) <= digits_value(s),
    decreases s.len(),
{
    if k < s.len() {
        assert(s.drop_last().subrange(0, k) =~= s.subrange(0, k));
        lemma_digits_prefix(s.drop_last(), k);
    } else {
        assert(s.subrange(0, k) =~= s);
    }
}

/// A prefix's hex digits are worth no more than the whole's.
pub proof fn lemma_hex_prefix(s: Seq<u8>, k: int)
    requires 0 <= k <= s.len(),
    ensures hex_value(s.subrange(0, k)) <= hex_value(s),
    decreases s.len(),
{
    if k < s.len() {
        assert(s.drop_last().subrange(0, k) =~= s.subrange(0, k));
        lemma_hex_prefix(s.drop_last(), k);
    } else {
        assert(s.subrange(0, k) =~= s);
    }
}

/// `s` starts with `p`.
pub open spec fn has_prefix(s: Seq<u8>, p: Seq<u8>) -> bool {
    p.len() <= s.len() && s.subrange(0, p.len() as int) == p
}

} // verus!

/// The length of the whitespace character at `s[i..]`, or 0.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i <= s.len(),
    ensures r as nat == ws_prefix(s@.skip(i as int)),
))]
fn ws_at(s: &[u8], i: usize) -> usize {
    let n = s.len() - i;
    if n >= 1 && ((9 <= s[i] && s[i] <= 13) || s[i] == 32) {
        1
    } else if n >= 2 && s[i] == 0xC2 && (s[i + 1] == 0x85 || s[i + 1] == 0xA0) {
        2
    } else if n >= 3 && is_ws3(s[i], s[i + 1], s[i + 2]) {
        3
    } else {
        0
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == ws3(a, b, c)))]
const fn is_ws3(a: u8, b: u8, c: u8) -> bool {
    (a == 0xE1 && b == 0x9A && c == 0x80)
        || (a == 0xE2 && b == 0x80 && ((0x80 <= c && c <= 0x8A) || c == 0xA8 || c == 0xA9 || c == 0xAF))
        || (a == 0xE2 && b == 0x81 && c == 0x9F)
        || (a == 0xE3 && b == 0x80 && c == 0x80)
}

/// The length of the whitespace character `s[i..j]` ends with, or 0.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i <= j <= s.len(),
    ensures r as nat == ws_suffix(s@.subrange(i as int, j as int)),
))]
fn ws_before(s: &[u8], i: usize, j: usize) -> usize {
    let n = j - i;
    if n >= 1 && ((9 <= s[j - 1] && s[j - 1] <= 13) || s[j - 1] == 32) {
        1
    } else if n >= 2 && s[j - 2] == 0xC2 && (s[j - 1] == 0x85 || s[j - 1] == 0xA0) {
        2
    } else if n >= 3 && is_ws3(s[j - 3], s[j - 2], s[j - 1]) {
        3
    } else {
        0
    }
}

/// The range of `s` that [`trimmed`] keeps: `str::trim` on the bytes of a `&str`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r.0 <= r.1 <= s.len(),
        s@.subrange(r.0 as int, r.1 as int) == trimmed(s@),
))]
#[must_use]
pub fn trim(s: &[u8]) -> (usize, usize) {
    let mut i: usize = 0;
    let mut k = ws_at(s, 0);
    proof! { assert(s@.skip(0) =~= s@); }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s.len(),
            k as nat == ws_prefix(s@.skip(i as int)),
            lead(s@) == i + lead(s@.skip(i as int)),
        decreases s.len() - i
    ))]
    while k != 0 {
        proof! {
            assert(s@.skip(i as int).skip(k as int) =~= s@.skip(i + k));
        }
        i += k;
        k = ws_at(s, i);
    }
    let mut j: usize = s.len();
    proof! {
        assert(lead(s@.skip(i as int)) == 0);
        assert(s@.subrange(i as int, s.len() as int) =~= s@.skip(i as int));
    }
    let mut k = ws_before(s, i, j);
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= j <= s.len(),
            lead(s@) == i,
            k as nat == ws_suffix(s@.subrange(i as int, j as int)),
            trail(s@.skip(i as int)) == (s.len() - j) + trail(s@.subrange(i as int, j as int)),
        decreases j - i
    ))]
    while k != 0 {
        proof! {
            assert(s@.subrange(i as int, j as int).subrange(0, (j - i) - k) =~= s@.subrange(i as int, j - k));
        }
        j -= k;
        k = ws_before(s, i, j);
    }
    proof! {
        assert(trail(s@.subrange(i as int, j as int)) == 0);
        let t = s@.skip(i as int);
        assert(t.subrange(0, t.len() - trail(t)) =~= s@.subrange(i as int, j as int));
    }
    (i, j)
}

/// How many characters the UTF-8 bytes `s` hold: `str::chars().count()`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r as nat == chars(s@)))]
#[must_use]
pub fn char_count(s: &[u8]) -> usize {
    let mut n: usize = 0;
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s.len(),
            n as nat == chars(s@.subrange(0, i as int)),
            n <= i,
        decreases s.len() - i
    ))]
    while i < s.len() {
        proof! {
            assert(s@.subrange(0, i + 1).drop_last() =~= s@.subrange(0, i as int));
        }
        if !(0x80 <= s[i] && s[i] < 0xC0) {
            n += 1;
        }
        i += 1;
    }
    proof! { assert(s@.subrange(0, s.len() as int) =~= s@); }
    n
}

/// Whether `s` starts with `p`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == has_prefix(s@, p@)))]
#[must_use]
pub fn starts_with(s: &[u8], p: &[u8]) -> bool {
    if p.len() > s.len() {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            p.len() <= s.len(),
            i <= p.len(),
            forall|k: int| 0 <= k < i ==> s@[k] == p@[k],
        decreases p.len() - i
    ))]
    while i < p.len() {
        if s[i] != p[i] {
            proof! { assert(s@.subrange(0, p.len() as int)[i as int] != p@[i as int]); }
            return false;
        }
        i += 1;
    }
    proof! { assert(s@.subrange(0, p.len() as int) =~= p@); }
    true
}

/// `u64::from_str` on the bytes of a `&str`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == parse_u64_spec(s@)))]
#[must_use]
pub fn parse_u64(s: &[u8]) -> Option<u64> {
    let start: usize = if !s.is_empty() && s[0] == 43 { 1 } else { 0 };
    proof! { assert(u64_digits(s@) =~= s@.skip(start as int)); }
    if start == s.len() {
        return None;
    }
    let mut v: u64 = 0;
    let mut i: usize = start;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= i <= s.len(),
            u64_digits(s@) == s@.skip(start as int),
            all_digits(s@.subrange(start as int, i as int)),
            v as nat == digits_value(s@.subrange(start as int, i as int)),
        decreases s.len() - i
    ))]
    while i < s.len() {
        let b = s[i];
        proof! { assert(s@.subrange(start as int, i + 1).drop_last() =~= s@.subrange(start as int, i as int)); }
        if !(48 <= b && b <= 57) {
            proof! {
                assert(s@.skip(start as int)[i - start] == b);
                assert(!is_digit(s@.skip(start as int)[i - start]));
            }
            return None;
        }
        let d = (b - 48) as u64;
        if v > (u64::MAX - d) / 10 {
            proof! {
                assert(digits_value(s@.subrange(start as int, i + 1)) == v * 10 + d);
                assert(v * 10 + d > u64::MAX) by (nonlinear_arith)
                    requires v > (u64::MAX - d) / 10, d <= 9;
                let t = s@.skip(start as int);
                assert(t.subrange(0, i + 1 - start) =~= s@.subrange(start as int, i + 1));
                lemma_digits_prefix(t, i + 1 - start);
            }
            return None;
        }
        proof! {
            assert(v * 10 + d <= u64::MAX) by (nonlinear_arith)
                requires v <= (u64::MAX - d) / 10, d <= 9;
            assert(digits_value(s@.subrange(start as int, i + 1)) == v * 10 + d);
        }
        v = v * 10 + d;
        i += 1;
    }
    proof! { assert(s@.subrange(start as int, s.len() as int) =~= s@.skip(start as int)); }
    Some(v)
}

/// `usize::from_str_radix(s, 16)` on the bytes of a `&str`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == parse_hex_spec(s@)))]
#[must_use]
pub fn parse_hex(s: &[u8]) -> Option<usize> {
    let start: usize = if !s.is_empty() && s[0] == 43 { 1 } else { 0 };
    proof! { assert(u64_digits(s@) =~= s@.skip(start as int)); }
    if start == s.len() {
        return None;
    }
    let mut v: usize = 0;
    let mut i: usize = start;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= i <= s.len(),
            u64_digits(s@) == s@.skip(start as int),
            all_hex(s@.subrange(start as int, i as int)),
            v as nat == hex_value(s@.subrange(start as int, i as int)),
        decreases s.len() - i
    ))]
    while i < s.len() {
        let b = s[i];
        proof! { assert(s@.subrange(start as int, i + 1).drop_last() =~= s@.subrange(start as int, i as int)); }
        let d: usize = if 48 <= b && b <= 57 {
            (b - 48) as usize
        } else if 97 <= b && b <= 102 {
            (b - 87) as usize
        } else if 65 <= b && b <= 70 {
            (b - 55) as usize
        } else {
            proof! {
                assert(s@.skip(start as int)[i - start] == b);
                assert(hex(s@.skip(start as int)[i - start]) is None);
                assert(!all_hex(s@.skip(start as int)));
            }
            return None;
        };
        if v > (usize::MAX - d) / 16 {
            proof! {
                assert(hex_value(s@.subrange(start as int, i + 1)) == v * 16 + d);
                assert(v * 16 + d > usize::MAX) by (nonlinear_arith)
                    requires v > (usize::MAX - d) / 16, d <= 15;
                let t = s@.skip(start as int);
                assert(t.subrange(0, i + 1 - start) =~= s@.subrange(start as int, i + 1));
                lemma_hex_prefix(t, i + 1 - start);
            }
            return None;
        }
        proof! {
            assert(v * 16 + d <= usize::MAX) by (nonlinear_arith)
                requires v <= (usize::MAX - d) / 16, d <= 15;
            assert(hex_value(s@.subrange(start as int, i + 1)) == v * 16 + d);
        }
        v = v * 16 + d;
        i += 1;
    }
    proof! { assert(s@.subrange(start as int, s.len() as int) =~= s@.skip(start as int)); }
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLES: &[&str] = &[
        "", " ", "a", " a ", "\t\n a b \r\n", "\u{a0}x\u{3000}", "\u{85}\u{1680}y\u{2000}\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}",
        "\u{200b}z\u{200b}", "é", " é ", "\u{2000}\u{2000}", "\u{feff}w",
    ];

    #[test]
    fn trim_is_str_trim() {
        for c in (0..=0x10_ffff).filter_map(char::from_u32) {
            for s in [format!("{c}"), format!("{c}a{c}"), format!("{c}{c}é{c}{c}")] {
                let (a, b) = trim(s.as_bytes());
                assert_eq!(&s[a..b], s.trim(), "{:?}", c);
            }
        }
        for s in SAMPLES {
            let (a, b) = trim(s.as_bytes());
            assert_eq!(&s[a..b], s.trim());
        }
    }

    #[test]
    fn char_count_is_chars_count() {
        for s in SAMPLES {
            assert_eq!(char_count(s.as_bytes()), s.chars().count());
        }
    }

    #[test]
    fn parsers_match_std() {
        let cases = [
            "", "+", "-", "0", "+0", "-0", "007", "18446744073709551615", "18446744073709551616", "1a", " 1", "ff",
            "+FF", "fffffffffffffffff", "ffffffffffffffff", "g", "99999999999999999999",
        ];
        for s in cases {
            assert_eq!(parse_u64(s.as_bytes()), s.parse::<u64>().ok(), "{s}");
            assert_eq!(parse_hex(s.as_bytes()), usize::from_str_radix(s, 16).ok(), "{s}");
        }
    }

    #[test]
    fn prefix() {
        assert!(starts_with(b"Bearer x", b"Bearer "));
        assert!(!starts_with(b"Bear", b"Bearer "));
        assert!(starts_with(b"x", b""));
    }
}
