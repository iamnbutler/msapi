//! Lowercase Crockford base32, the text form of IDs and token secrets.
//!
//! IDs are 128-bit values whose order is creation order (`policy::next_id`),
//! and the API pages audit and stat history by comparing ID strings. So the
//! encoding must keep that order: Verus checks that a smaller value always
//! encodes to a lexicographically smaller string, and that every character is
//! in the Crockford alphabet (no `i`, `l`, `o` or `u`).

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// The alphabet, digit 0 first. [`digit_char`] computes the same mapping.
pub const ALPHABET: &[u8; 32] = b"0123456789abcdefghjkmnpqrstvwxyz";

#[cfg(feature = "verus")]
verus! {

/// The character for digit `d` (0-31).
pub open spec fn alpha(d: int) -> int {
    if d < 10 {
        48 + d
    } else if d < 18 {
        97 + (d - 10)
    } else if d < 20 {
        106 + (d - 18)
    } else if d < 22 {
        109 + (d - 20)
    } else if d < 27 {
        112 + (d - 22)
    } else {
        118 + (d - 27)
    }
}

/// Whether `c` is a lowercase Crockford character: `0-9` and `a-z` without
/// `i`, `l`, `o` and `u`.
pub open spec fn is_crockford(c: u8) -> bool {
    (48 <= c <= 57) || (97 <= c <= 122 && c != 105 && c != 108 && c != 111 && c != 117)
}

/// Digit `i` of the 26-digit encoding of `v`: 25 five-bit groups from the
/// top, then the last three bits padded with two zero bits.
pub open spec fn digit(v: u128, i: int) -> u128 {
    if i < 25 {
        (v >> ((123 - 5 * i) as u128)) & 31
    } else {
        (v & 7) << 2
    }
}

/// The encoding of `v`.
pub open spec fn encoded(v: u128) -> Seq<u8> {
    Seq::new(26, |i: int| alpha(digit(v, i) as int) as u8)
}

/// `x` sorts strictly before `y`, byte by byte.
pub open spec fn lex_lt(x: Seq<u8>, y: Seq<u8>) -> bool {
    exists|k: int|
        0 <= k < x.len() && k < y.len() && (forall|j: int| 0 <= j < k ==> x[j] == y[j]) && x[k] < y[k]
}

} // verus!

/// The character for digit `d`, which must be below 32.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires d < 32,
    ensures r as int == alpha(d as int), is_crockford(r),
))]
#[must_use]
pub const fn digit_char(d: u8) -> u8 {
    if d < 10 {
        b'0' + d
    } else if d < 18 {
        b'a' + (d - 10)
    } else if d < 20 {
        b'j' + (d - 18)
    } else if d < 22 {
        b'm' + (d - 20)
    } else if d < 27 {
        b'p' + (d - 22)
    } else {
        b'v' + (d - 27)
    }
}

/// The 26 characters of `v`, most significant bits first. Order-preserving:
/// see [`lemma_order`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@ == encoded(v),
        forall|i: int| 0 <= i < 26 ==> is_crockford(#[trigger] r@[i]),
))]
#[must_use]
pub fn encode_u128(v: u128) -> [u8; 26] {
    let mut out = [0u8; 26];
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= 25,
            out@.len() == 26,
            forall|j: int| 0 <= j < i ==> out@[j] == encoded(v)[j] && is_crockford(#[trigger] out@[j]),
        decreases 25 - i
    ))]
    while i < 25 {
        let shift = (123 - 5 * i) as u128;
        let d = (v >> shift) & 31;
        proof! {
            assert(d < 32) by (bit_vector) requires d == (v >> shift) & 31;
        }
        out[i] = digit_char(d as u8);
        i += 1;
    }
    let d = (v & 7) << 2;
    proof! {
        assert(d < 32) by (bit_vector) requires d == (v & 7) << 2;
    }
    out[25] = digit_char(d as u8);
    proof! {
        assert(out@ =~= encoded(v));
    }
    out
}

/// The base32 of `bytes`, most significant bits first, with the last
/// character padded with zero bits: `ceil(8n / 5)` characters.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires bytes@.len() * 8 + 4 <= usize::MAX,
    ensures
        r@.len() == (bytes@.len() * 8 + 4) / 5,
        forall|i: int| 0 <= i < r@.len() ==> is_crockford(#[trigger] r@[i]),
))]
#[must_use]
pub fn encode(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len() * 8 / 5 + 1);
    let (mut acc, mut bits) = (0u32, 0u32);
    let mut n: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            n <= bytes.len(),
            bytes@.len() * 8 + 4 <= usize::MAX,
            bits < 5,
            out@.len() * 5 + bits == n * 8,
            forall|j: int| 0 <= j < out@.len() ==> is_crockford(#[trigger] out@[j]),
        decreases bytes.len() - n
    ))]
    while n < bytes.len() {
        acc = (acc << 8) | bytes[n] as u32;
        bits += 8;
        n += 1;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                bits < 13,
                out@.len() * 5 + bits == n * 8,
                forall|j: int| 0 <= j < out@.len() ==> is_crockford(#[trigger] out@[j]),
            decreases bits
        ))]
        while bits >= 5 {
            bits -= 5;
            let d = (acc >> bits) & 31;
            proof! {
                assert(d < 32) by (bit_vector) requires d == (acc >> bits) & 31;
            }
            out.push(digit_char(d as u8));
        }
    }
    if bits > 0 {
        let pad = 5 - bits;
        let d = (acc << pad) & 31;
        proof! {
            assert(d < 32) by (bit_vector) requires d == (acc << pad) & 31;
        }
        out.push(digit_char(d as u8));
    }
    out
}

#[cfg(feature = "verus")]
verus! {

/// Order preservation: a smaller value encodes to a string that sorts first.
pub proof fn lemma_order(a: u128, b: u128)
    requires a < b,
    ensures lex_lt(encoded(a), encoded(b)),
{
    lemma_digits(a, b, 0);
    let k = choose|k: int|
        0 <= k < 26 && (forall|j: int| 0 <= j < k ==> digit(a, j) == digit(b, j)) && digit(a, k) < digit(b, k);
    lemma_digit_range(a, k);
    lemma_digit_range(b, k);
    assert forall|j: int| 0 <= j < k implies encoded(a)[j] == encoded(b)[j] by {
        assert(digit(a, j) == digit(b, j));
    }
    assert(encoded(a)[k] < encoded(b)[k]);
}

/// Different values have different encodings.
pub proof fn lemma_injective(a: u128, b: u128)
    requires a != b,
    ensures encoded(a) != encoded(b),
{
    if a < b {
        lemma_order(a, b);
    } else {
        lemma_order(b, a);
    }
}

proof fn lemma_digit_range(v: u128, i: int)
    requires 0 <= i < 26,
    ensures digit(v, i) < 32,
{
    if i < 25 {
        let s = (123 - 5 * i) as u128;
        assert((v >> s) & 31 < 32) by (bit_vector);
    } else {
        assert((v & 7) << 2 < 32) by (bit_vector);
    }
}

/// With digits `0..k` equal (and so the top `5k` bits), the first digit
/// that differs is smaller in `a`.
proof fn lemma_digits(a: u128, b: u128, k: int)
    requires
        a < b,
        0 <= k <= 25,
        forall|j: int| 0 <= j < k ==> digit(a, j) == digit(b, j),
        k > 0 ==> a >> ((128 - 5 * k) as u128) == b >> ((128 - 5 * k) as u128),
    ensures
        exists|k2: int|
            0 <= k2 < 26 && (forall|j: int| 0 <= j < k2 ==> digit(a, j) == digit(b, j)) && digit(a, k2) < digit(b, k2),
    decreases 26 - k,
{
    if k == 25 {
        assert(((a & 7) << 2) < ((b & 7) << 2)) by (bit_vector)
            requires a >> 3u128 == b >> 3u128, a < b;
        assert(digit(a, 25) < digit(b, 25));
    } else {
        let s = (123 - 5 * k) as u128;
        let (da, db) = (digit(a, k), digit(b, k));
        if k == 0 {
            assert((a >> 123u128) & 31 <= (b >> 123u128) & 31 && ((a >> 123u128) & 31 == (b >> 123u128) & 31 ==> a >> 123u128 == b >> 123u128)) by (bit_vector)
                requires a < b;
        } else {
            assert(3u128 <= s < 123);
            assert((a >> s) & 31 <= (b >> s) & 31 && ((a >> s) & 31 == (b >> s) & 31 ==> a >> s == b >> s)) by (bit_vector)
                requires a < b, a >> (s + 5) == b >> (s + 5), 3u128 <= s < 123;
            assert(((128 - 5 * k) as u128) == s + 5);
        }
        if da == db {
            assert(((128 - 5 * (k + 1)) as u128) == s);
            lemma_digits(a, b, k + 1);
        } else {
            assert(da < db);
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digit_char_is_the_alphabet() {
        for d in 0..32u8 {
            assert_eq!(digit_char(d), ALPHABET[d as usize]);
        }
    }

    #[test]
    fn known_vectors() {
        assert_eq!(encode(&[]), b"");
        assert_eq!(encode(&[0xff]), b"zw");
        assert_eq!(encode(&[0, 0, 0, 0, 0]), b"00000000");
        assert_eq!(&encode_u128(0), b"00000000000000000000000000");
        assert_eq!(&encode_u128(u128::MAX), b"zzzzzzzzzzzzzzzzzzzzzzzzzw");
    }

    #[test]
    fn u128_matches_bytes() {
        for v in [0, 1, 31, 32, 1 << 80, u128::MAX - 1, 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210] {
            assert_eq!(encode_u128(v).as_slice(), encode(&v.to_be_bytes()).as_slice());
        }
    }

    #[test]
    fn order_is_kept() {
        let vs = [0u128, 1, 2, 31, 32, 1 << 79, 1 << 80, (1 << 80) + 1, u128::MAX - 1, u128::MAX];
        for w in vs.windows(2) {
            assert!(encode_u128(w[0]) < encode_u128(w[1]));
        }
    }
}
