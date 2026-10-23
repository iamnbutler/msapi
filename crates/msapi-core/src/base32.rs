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
#![allow(
    clippy::manual_div_ceil,
    clippy::many_single_char_names,
    reason = "Verus has no spec for `div_ceil`; i, j, k, d, b are the digit, bit and value of the spec"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

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

/// The alphabet as a table, digit 0 first: `0-9 a-z` without `i l o u`.
pub open spec fn crockford() -> Seq<u8> {
    seq![b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f', b'g', b'h', b'j', b'k', b'm', b'n', b'p', b'q', b'r', b's', b't', b'v', b'w', b'x', b'y', b'z']
}

/// [`alpha`] is the table.
pub proof fn lemma_alpha_table(d: int)
    requires 0 <= d < 32,
    ensures alpha(d) == crockford()[d] as int,
{
    if d == 0 {
        assert(crockford()[0] == b'0');
    } else if d == 1 {
        assert(crockford()[1] == b'1');
    } else if d == 2 {
        assert(crockford()[2] == b'2');
    } else if d == 3 {
        assert(crockford()[3] == b'3');
    } else if d == 4 {
        assert(crockford()[4] == b'4');
    } else if d == 5 {
        assert(crockford()[5] == b'5');
    } else if d == 6 {
        assert(crockford()[6] == b'6');
    } else if d == 7 {
        assert(crockford()[7] == b'7');
    } else if d == 8 {
        assert(crockford()[8] == b'8');
    } else if d == 9 {
        assert(crockford()[9] == b'9');
    } else if d == 10 {
        assert(crockford()[10] == b'a');
    } else if d == 11 {
        assert(crockford()[11] == b'b');
    } else if d == 12 {
        assert(crockford()[12] == b'c');
    } else if d == 13 {
        assert(crockford()[13] == b'd');
    } else if d == 14 {
        assert(crockford()[14] == b'e');
    } else if d == 15 {
        assert(crockford()[15] == b'f');
    } else if d == 16 {
        assert(crockford()[16] == b'g');
    } else if d == 17 {
        assert(crockford()[17] == b'h');
    } else if d == 18 {
        assert(crockford()[18] == b'j');
    } else if d == 19 {
        assert(crockford()[19] == b'k');
    } else if d == 20 {
        assert(crockford()[20] == b'm');
    } else if d == 21 {
        assert(crockford()[21] == b'n');
    } else if d == 22 {
        assert(crockford()[22] == b'p');
    } else if d == 23 {
        assert(crockford()[23] == b'q');
    } else if d == 24 {
        assert(crockford()[24] == b'r');
    } else if d == 25 {
        assert(crockford()[25] == b's');
    } else if d == 26 {
        assert(crockford()[26] == b't');
    } else if d == 27 {
        assert(crockford()[27] == b'v');
    } else if d == 28 {
        assert(crockford()[28] == b'w');
    } else if d == 29 {
        assert(crockford()[29] == b'x');
    } else if d == 30 {
        assert(crockford()[30] == b'y');
    } else if d == 31 {
        assert(crockford()[31] == b'z');
    }
}

/// Bit `k` of `b`, most significant bit of `b[0]` first; 0 past the end.
pub open spec fn bit(b: Seq<u8>, k: int) -> int {
    if 0 <= k < b.len() * 8 {
        ((b[k / 8] >> ((7 - k % 8) as u8)) & 1u8) as int
    } else {
        0
    }
}

/// Five-bit group `i` of `b`, zero-padded past the end.
pub open spec fn group(b: Seq<u8>, i: int) -> int {
    16 * bit(b, 5 * i) + 8 * bit(b, 5 * i + 1) + 4 * bit(b, 5 * i + 2) + 2 * bit(b, 5 * i + 3) + bit(b, 5 * i + 4)
}

/// The first `j` bits of group `i`, as a number.
pub open spec fn partial(b: Seq<u8>, i: int, j: int) -> int
    decreases j,
{
    if j <= 0 { 0 } else { 2 * partial(b, i, j - 1) + bit(b, 5 * i + j - 1) }
}

/// The 16 big-endian bytes of `v`.
pub open spec fn be_bytes(v: u128) -> Seq<u8> {
    Seq::new(16, |q: int| ((v >> ((120 - 8 * q) as u128)) & 0xff) as u8)
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
    ensures r as int == alpha(d as int), r == crockford()[d as int], is_crockford(r),
))]
#[must_use]
pub const fn digit_char(d: u8) -> u8 {
    proof! {
        lemma_alpha_table(d as int);
    }
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
        forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]) == crockford()[group(bytes@, i)],
        forall|i: int| 0 <= i < r@.len() ==> is_crockford(#[trigger] r@[i]),
))]
#[must_use]
pub fn encode(bytes: &[u8]) -> Vec<u8> {
    let total = bytes.len() * 8;
    let len = (total + 4) / 5;
    let mut out = Vec::with_capacity(len);
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            total == bytes@.len() * 8,
            total + 4 <= usize::MAX,
            len == (total + 4) / 5,
            i <= len,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j]) == crockford()[group(bytes@, j)],
            forall|j: int| 0 <= j < i ==> is_crockford(#[trigger] out@[j]),
        decreases len - i
    ))]
    while i < len {
        let mut d: u8 = 0;
        let mut j: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                total == bytes@.len() * 8,
                total + 4 <= usize::MAX,
                i < len,
                len == (total + 4) / 5,
                j <= 5,
                out@.len() == i,
                forall|m: int| 0 <= m < i ==> (#[trigger] out@[m]) == crockford()[group(bytes@, m)],
                forall|m: int| 0 <= m < i ==> is_crockford(#[trigger] out@[m]),
                d as int == partial(bytes@, i as int, j as int),
                (d as int) < pow2(j as nat),
            decreases 5 - j
        ))]
        while j < 5 {
            let k = 5 * i + j;
            let b: u8 = if k < total {
                proof! {
                    assert(k / 8 < bytes@.len());
                }
                let sh = (7 - k % 8) as u8;
                let b = (bytes[k / 8] >> sh) & 1;
                proof! {
                    let x = bytes@[(k / 8) as int];
                    assert(b < 2) by (bit_vector) requires b == (x >> sh) & 1u8;
                }
                b
            } else {
                0
            };
            proof! {
                assert(b as int == bit(bytes@, k as int));
                assert(b < 2);
                lemma_pow2_step(j as nat);
                reveal_with_fuel(pow2, 6);
                assert(pow2(j as nat) <= 16);
            }
            d = 2 * d + b;
            j += 1;
        }
        proof! {
            lemma_pow2_step(4);
            reveal_with_fuel(pow2, 6);
            reveal_with_fuel(partial, 6);
            assert(d as int == group(bytes@, i as int));
        }
        out.push(digit_char(d));
        i += 1;
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

/// `2^n`.
pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_step(n: nat)
    ensures pow2(n + 1) == 2 * pow2(n), pow2(5) == 32,
{
    reveal_with_fuel(pow2, 6);
}

/// Bit `k` of `be_bytes(v)` is bit `127 - k` of `v`.
proof fn lemma_be_bit(v: u128, k: int)
    requires 0 <= k < 128,
    ensures bit(be_bytes(v), k) == ((v >> ((127 - k) as u128)) & 1) as int,
{
    let q = k / 8;
    let r = k % 8;
    let s1 = (120 - 8 * q) as u128;
    let s2 = (7 - r) as u128;
    let byte = ((v >> s1) & 0xff) as u8;
    assert(be_bytes(v)[q] == byte);
    assert(s1 + s2 == (127 - k) as u128);
    let x = (v >> s1) & 0xff;
    assert(x < 256) by (bit_vector) requires x == (v >> s1) & 0xff;
    assert(((x >> s2) & 1) == ((v >> (s1 + s2)) & 1)) by (bit_vector)
        requires x == (v >> s1) & 0xff, s2 < 8, s1 <= 120;
    let s2b = s2 as u8;
    assert(((byte >> s2b) & 1u8) as u128 == (x >> s2) & 1) by (bit_vector)
        requires byte == x as u8, x < 256, s2b as u128 == s2, s2 < 8;
}

/// Digit `i` of [`encoded`] is group `i` of the value's 16 big-endian
/// bytes, so `encode_u128(v)` and `encode(&v.to_be_bytes())` agree.
pub proof fn lemma_u128_is_bytes(v: u128, i: int)
    requires 0 <= i < 26,
    ensures digit(v, i) as int == group(be_bytes(v), i),
{
    assert(be_bytes(v).len() == 16);
    if i < 25 {
        let s = (123 - 5 * i) as u128;
        assert(((v >> s) & 31) == 16 * ((v >> (s + 4)) & 1) + 8 * ((v >> (s + 3)) & 1) + 4 * ((v >> (s + 2)) & 1)
            + 2 * ((v >> (s + 1)) & 1) + ((v >> s) & 1)) by (bit_vector)
            requires s <= 123;
        lemma_be_bit(v, 5 * i);
        lemma_be_bit(v, 5 * i + 1);
        lemma_be_bit(v, 5 * i + 2);
        lemma_be_bit(v, 5 * i + 3);
        lemma_be_bit(v, 5 * i + 4);
    } else {
        assert(((v & 7) << 2) == 16 * ((v >> 2u128) & 1) + 8 * ((v >> 1u128) & 1) + 4 * ((v >> 0u128) & 1)) by (bit_vector);
        lemma_be_bit(v, 125);
        lemma_be_bit(v, 126);
        lemma_be_bit(v, 127);
    }
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
        let table: Vec<u8> = (0..32).map(digit_char).collect();
        assert_eq!(table, b"0123456789abcdefghjkmnpqrstvwxyz");
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
