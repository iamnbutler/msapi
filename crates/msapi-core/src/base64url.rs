//! Base64url without padding (RFC 4648 §5), as `WebAuthn` uses it for
//! challenges, credential ids and every binary field a browser sends.
//!
//! The decoder is canonical: it accepts exactly the strings [`encode`]
//! produces, plus trailing `=` padding. Verus checks both directions:
//! whatever [`decode`] returns encodes back to its input, and it returns
//! `None` only for text no byte string encodes to.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]
#![allow(
    clippy::many_single_char_names,
    clippy::too_many_lines,
    clippy::needless_else,
    clippy::question_mark,
    reason = "w x y z / a b c are the sextets and bytes of RFC 4648; the length, empty branches and               let-else are proof blocks, which compile away"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {

/// The character for a six-bit value: `A-Z a-z 0-9 - _`.
pub open spec fn char_of(v: u8) -> u8 {
    if v < 26 {
        (65 + v) as u8
    } else if v < 52 {
        (97 + v - 26) as u8
    } else if v < 62 {
        (48 + v - 52) as u8
    } else if v == 62 {
        45u8
    } else {
        95u8
    }
}

/// The six-bit value of a character, if it is in the alphabet.
pub open spec fn value_of(c: u8) -> Option<u8> {
    if 65 <= c <= 90 {
        Some((c - 65) as u8)
    } else if 97 <= c <= 122 {
        Some((c - 97 + 26) as u8)
    } else if 48 <= c <= 57 {
        Some((c - 48 + 52) as u8)
    } else if c == 45 {
        Some(62u8)
    } else if c == 95 {
        Some(63u8)
    } else {
        None
    }
}

/// Three bytes as four characters.
pub open spec fn enc3(a: u8, b: u8, c: u8) -> Seq<u8> {
    seq![char_of(a >> 2), char_of(((a & 3) << 4) | (b >> 4)), char_of(((b & 15) << 2) | (c >> 6)), char_of(c & 63)]
}

/// The first `k` whole three-byte groups of `b`, encoded.
pub open spec fn enc_full(b: Seq<u8>, k: nat) -> Seq<u8>
    decreases k,
{
    if k == 0 || 3 * k > b.len() {
        Seq::empty()
    } else {
        let i = 3 * (k - 1) as int;
        enc_full(b, (k - 1) as nat) + enc3(b[i], b[i + 1], b[i + 2])
    }
}

/// The last one or two bytes, encoded without padding.
pub open spec fn enc_tail(b: Seq<u8>) -> Seq<u8> {
    let i = 3 * (b.len() / 3) as int;
    if b.len() % 3 == 1 {
        seq![char_of(b[i] >> 2), char_of((b[i] & 3) << 4)]
    } else if b.len() % 3 == 2 {
        seq![char_of(b[i] >> 2), char_of(((b[i] & 3) << 4) | (b[i + 1] >> 4)), char_of((b[i + 1] & 15) << 2)]
    } else {
        Seq::empty()
    }
}

/// The unpadded base64url encoding of `b`.
pub open spec fn encode_spec(b: Seq<u8>) -> Seq<u8> {
    enc_full(b, b.len() / 3) + enc_tail(b)
}

/// `t` without its trailing `=`.
pub open spec fn unpadded(t: Seq<u8>) -> Seq<u8>
    decreases t.len(),
{
    if t.len() > 0 && t.last() == 61 {
        unpadded(t.drop_last())
    } else {
        t
    }
}

proof fn lemma_char(v: u8)
    requires v < 64,
    ensures value_of(char_of(v)) == Some(v),
{
}

proof fn lemma_value(c: u8)
    requires value_of(c) is Some,
    ensures value_of(c).unwrap() < 64, char_of(value_of(c).unwrap()) == c,
{
}

proof fn lemma_sextets(a: u8, b: u8, c: u8)
    ensures
        a >> 2 < 64, ((a & 3) << 4) | (b >> 4) < 64, ((b & 15) << 2) | (c >> 6) < 64, c & 63 < 64,
        (a & 3) << 4 < 64, (b & 15) << 2 < 64, ((a & 3) << 4) & 15 == 0, ((b & 15) << 2) & 3 == 0,
{
    assert(a >> 2 < 64) by (bit_vector);
    assert(((a & 3) << 4) | (b >> 4) < 64) by (bit_vector);
    assert(((b & 15) << 2) | (c >> 6) < 64) by (bit_vector);
    assert(c & 63 < 64) by (bit_vector);
    assert((a & 3) << 4 < 64) by (bit_vector);
    assert((b & 15) << 2 < 64) by (bit_vector);
    assert(((a & 3) << 4) & 15 == 0) by (bit_vector);
    assert(((b & 15) << 2) & 3 == 0) by (bit_vector);
}

/// Every character of an encoding is in the alphabet.
proof fn lemma_enc_full_valid(b: Seq<u8>, k: nat)
    requires 3 * k <= b.len(),
    ensures
        enc_full(b, k).len() == 4 * k,
        forall|j: int| 0 <= j < 4 * k ==> value_of(#[trigger] enc_full(b, k)[j]) is Some,
    decreases k,
{
    if k > 0 {
        let i = 3 * (k - 1) as int;
        lemma_enc_full_valid(b, (k - 1) as nat);
        lemma_sextets(b[i], b[i + 1], b[i + 2]);
        lemma_char(b[i] >> 2);
        lemma_char(((b[i] & 3) << 4) | (b[i + 1] >> 4));
        lemma_char(((b[i + 1] & 15) << 2) | (b[i + 2] >> 6));
        lemma_char(b[i + 2] & 63);
        let prev = enc_full(b, (k - 1) as nat);
        let g = enc3(b[i], b[i + 1], b[i + 2]);
        assert(enc_full(b, k) == prev + g);
        assert forall|j: int| 0 <= j < 4 * k implies value_of(#[trigger] enc_full(b, k)[j]) is Some by {
            if j >= 4 * (k - 1) {
                assert(enc_full(b, k)[j] == g[j - 4 * (k - 1)]);
            } else {
                assert(enc_full(b, k)[j] == prev[j]);
            }
        }
    }
}

proof fn lemma_encode_valid(b: Seq<u8>)
    ensures
        encode_spec(b).len() == 4 * (b.len() / 3) + enc_tail(b).len(),
        encode_spec(b).len() % 4 != 1,
        forall|j: int| 0 <= j < encode_spec(b).len() ==> value_of(#[trigger] encode_spec(b)[j]) is Some,
{
    let k = b.len() / 3;
    let i = 3 * k as int;
    lemma_enc_full_valid(b, k);
    let full = enc_full(b, k);
    let tail = enc_tail(b);
    if b.len() % 3 != 0 {
        lemma_sextets(b[i], if b.len() % 3 == 2 { b[i + 1] } else { 0 }, 0);
        lemma_char(b[i] >> 2);
        lemma_char((b[i] & 3) << 4);
        if b.len() % 3 == 2 {
            lemma_sextets(b[i], b[i + 1], 0);
            lemma_char(((b[i] & 3) << 4) | (b[i + 1] >> 4));
            lemma_char((b[i + 1] & 15) << 2);
        }
    }
    assert forall|j: int| 0 <= j < encode_spec(b).len() implies value_of(#[trigger] encode_spec(b)[j]) is Some by {
        if j < 4 * k {
            assert(encode_spec(b)[j] == full[j]);
        } else {
            assert(encode_spec(b)[j] == tail[j - 4 * k]);
        }
    }
}

/// `enc_full` only looks at the first `3k` bytes.
proof fn lemma_enc_full_prefix(b1: Seq<u8>, b2: Seq<u8>, k: nat)
    requires 3 * k <= b1.len(), 3 * k <= b2.len(), b1.take(3 * k as int) == b2.take(3 * k as int),
    ensures enc_full(b1, k) == enc_full(b2, k),
    decreases k,
{
    if k > 0 {
        let i = 3 * (k - 1) as int;
        assert(b1.take(3 * (k - 1) as int) == b1.take(3 * k as int).take(3 * (k - 1) as int));
        assert(b2.take(3 * (k - 1) as int) == b2.take(3 * k as int).take(3 * (k - 1) as int));
        assert(b1[i] == b1.take(3 * k as int)[i]);
        assert(b1[i + 1] == b1.take(3 * k as int)[i + 1]);
        assert(b1[i + 2] == b1.take(3 * k as int)[i + 2]);
        lemma_enc_full_prefix(b1, b2, (k - 1) as nat);
    }
}

/// Appending bytes leaves the whole groups already there unchanged.
proof fn lemma_enc_full_extend(b: Seq<u8>, e: Seq<u8>, k: nat)
    requires 3 * k <= b.len(),
    ensures enc_full(b + e, k) == enc_full(b, k),
{
    assert((b + e).take(3 * k as int) =~= b.take(3 * k as int));
    lemma_enc_full_prefix(b + e, b, k);
}

/// A character outside the alphabet means nothing encodes to `t`.
proof fn lemma_refuse_char(t: Seq<u8>, j: int)
    requires 0 <= j < t.len(),
    ensures value_of(t[j]) is None ==> forall|b: Seq<u8>| encode_spec(b) != t,
{
    assert forall|b: Seq<u8>| value_of(t[j]) is None implies encode_spec(b) != t by {
        lemma_encode_valid(b);
    }
}

/// Nonzero leftover bits in the last character mean nothing encodes to `t`.
proof fn lemma_refuse_tail(t: Seq<u8>)
    requires
        t.len() % 4 == 2 || t.len() % 4 == 3,
        value_of(t.last()) is Some,
    ensures
        t.len() % 4 == 2 && value_of(t.last()).unwrap() & 15 != 0 ==> forall|b: Seq<u8>| encode_spec(b) != t,
        t.len() % 4 == 3 && value_of(t.last()).unwrap() & 3 != 0 ==> forall|b: Seq<u8>| encode_spec(b) != t,
{
    assert forall|b: Seq<u8>| encode_spec(b) == t implies
        (t.len() % 4 == 2 ==> value_of(t.last()).unwrap() & 15 == 0)
        && (t.len() % 4 == 3 ==> value_of(t.last()).unwrap() & 3 == 0) by {
        lemma_encode_valid(b);
        let k = b.len() / 3;
        let j = 3 * k as int;
        let full = enc_full(b, k);
        let tail = enc_tail(b);
        assert(t =~= full + tail);
        if b.len() % 3 == 1 {
            lemma_sextets(b[j], 0, 0);
            assert(t.last() == tail[1]);
            lemma_char((b[j] & 3) << 4);
        } else if b.len() % 3 == 2 {
            lemma_sextets(b[j], b[j + 1], 0);
            assert(t.last() == tail[2]);
            lemma_char((b[j + 1] & 15) << 2);
        }
    }
}

} // verus!

/// The character for a six-bit value.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => requires v < 64, ensures r == char_of(v)))]
const fn char_for(v: u8) -> u8 {
    if v < 26 {
        b'A' + v
    } else if v < 52 {
        b'a' + v - 26
    } else if v < 62 {
        b'0' + v - 52
    } else if v == 62 {
        b'-'
    } else {
        b'_'
    }
}

/// The six-bit value of a character.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == value_of(c)))]
const fn value_for(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => Some(c - b'A'),
        b'a'..=b'z' => Some(c - b'a' + 26),
        b'0'..=b'9' => Some(c - b'0' + 52),
        b'-' => Some(62),
        b'_' => Some(63),
        _ => None,
    }
}

/// Encodes `bytes` as base64url without padding.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == encode_spec(bytes@)))]
#[must_use]
pub fn encode(bytes: &[u8]) -> Vec<u8> {
    let groups = bytes.len() / 3;
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            groups == bytes@.len() / 3,
            k <= groups,
            out@ == enc_full(bytes@, k as nat),
        decreases groups - k
    ))]
    while k < groups {
        let i = 3 * k;
        let (a, b, c) = (bytes[i], bytes[i + 1], bytes[i + 2]);
        proof! {
            lemma_sextets(a, b, c);
        }
        out.push(char_for(a >> 2));
        out.push(char_for(((a & 3) << 4) | (b >> 4)));
        out.push(char_for(((b & 15) << 2) | (c >> 6)));
        out.push(char_for(c & 63));
        proof! {
            assert(out@ =~= enc_full(bytes@, k as nat) + enc3(a, b, c));
        }
        k += 1;
    }
    let i = 3 * groups;
    let rest = bytes.len() - i;
    proof! {
        assert(enc_full(bytes@, groups as nat).len() == 4 * groups) by {
            lemma_enc_full_valid(bytes@, groups as nat);
        }
    }
    if rest == 1 {
        let a = bytes[i];
        proof! {
            lemma_sextets(a, 0, 0);
        }
        out.push(char_for(a >> 2));
        out.push(char_for((a & 3) << 4));
    } else if rest == 2 {
        let (a, b) = (bytes[i], bytes[i + 1]);
        proof! {
            lemma_sextets(a, b, 0);
        }
        out.push(char_for(a >> 2));
        out.push(char_for(((a & 3) << 4) | (b >> 4)));
        out.push(char_for((b & 15) << 2));
    }
    proof! {
        assert(out@ =~= encode_spec(bytes@));
    }
    out
}

/// Decodes base64url, with or without trailing `=` padding.
///
/// `None` unless the text (padding aside) is exactly the [`encode`] of some
/// byte string: a character outside `A-Z a-z 0-9 - _`, an impossible length,
/// or nonzero leftover bits in the last character.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some(out) => encode_spec(out@) == unpadded(text@),
            None => forall|b: Seq<u8>| encode_spec(b) != unpadded(text@),
        }
))]
#[must_use]
pub fn decode(text: &[u8]) -> Option<Vec<u8>> {
    let mut n = text.len();
    proof! {
        assert(text@.take(n as int) =~= text@);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            n <= text@.len(),
            unpadded(text@.take(n as int)) == unpadded(text@),
        decreases n
    ))]
    while n > 0 && text[n - 1] == b'=' {
        proof! {
            assert(text@.take(n as int).drop_last() =~= text@.take(n - 1));
        }
        n -= 1;
    }
    proof! {
        assert(unpadded(text@.take(n as int)) == text@.take(n as int));
    }
    let groups = n / 4;
    let rest = n % 4;
    if rest == 1 {
        proof! {
            assert forall|b: Seq<u8>| encode_spec(b) != unpadded(text@) by {
                lemma_encode_valid(b);
            }
        }
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            n <= text@.len(),
            unpadded(text@) == text@.take(n as int),
            groups == n / 4,
            rest == n % 4,
            rest != 1,
            k <= groups,
            out@.len() == 3 * k,
            enc_full(out@, k as nat) == text@.take(4 * k as int),
        decreases groups - k
    ))]
    while k < groups {
        let i = 4 * k;
        let (Some(w), Some(x), Some(y), Some(z)) =
            (value_for(text[i]), value_for(text[i + 1]), value_for(text[i + 2]), value_for(text[i + 3]))
        else {
            proof! {
                lemma_refuse_char(text@.take(n as int), i as int);
                lemma_refuse_char(text@.take(n as int), i + 1);
                lemma_refuse_char(text@.take(n as int), i + 2);
                lemma_refuse_char(text@.take(n as int), i + 3);
            }
            return None;
        };
        proof! {
            lemma_value(text[i as int]);
            lemma_value(text[i + 1]);
            lemma_value(text[i + 2]);
            lemma_value(text[i + 3]);
        }
        let a = (w << 2) | (x >> 4);
        let b = ((x & 15) << 4) | (y >> 2);
        let c = ((y & 3) << 6) | z;
        proof! {
            assert(a >> 2 == w && ((a & 3) << 4) | (b >> 4) == x && ((b & 15) << 2) | (c >> 6) == y && c & 63 == z)
                by (bit_vector)
                requires w < 64, x < 64, y < 64, z < 64,
                    a == (w << 2) | (x >> 4), b == ((x & 15) << 4) | (y >> 2), c == ((y & 3) << 6) | z;
            let next = out@.push(a).push(b).push(c);
            lemma_enc_full_extend(out@, seq![a, b, c], k as nat);
            assert(next =~= out@ + seq![a, b, c]);
            assert(next[3 * k as int] == a && next[3 * k + 1] == b && next[3 * k + 2] == c);
            assert(enc_full(next, (k + 1) as nat) == enc_full(next, k as nat) + enc3(a, b, c));
            assert(enc3(a, b, c) =~= text@.subrange(4 * k as int, 4 * k + 4));
            assert(text@.take(4 * (k + 1) as int) =~= text@.take(4 * k as int) + text@.subrange(4 * k as int, 4 * k + 4));
        }
        out.push(a);
        out.push(b);
        out.push(c);
        k += 1;
    }
    let i = 4 * groups;
    proof! {
        assert(text@.take(n as int) =~= text@.take(4 * groups as int) + text@.subrange(4 * groups as int, n as int));
    }
    if rest >= 2 {
        let (Some(w), Some(x)) = (value_for(text[i]), value_for(text[i + 1])) else {
            proof! {
                lemma_refuse_char(text@.take(n as int), i as int);
                lemma_refuse_char(text@.take(n as int), i + 1);
            }
            return None;
        };
        proof! {
            lemma_value(text[i as int]);
            lemma_value(text[i + 1]);
        }
        let a = (w << 2) | (x >> 4);
        if rest == 2 {
            if x & 15 != 0 {
                proof! {
                    lemma_refuse_tail(text@.take(n as int));
                }
                return None;
            }
            proof! {
                assert(a >> 2 == w && (a & 3) << 4 == x)
                    by (bit_vector)
                    requires w < 64, x < 64, x & 15 == 0, a == (w << 2) | (x >> 4);
                lemma_enc_full_extend(out@, seq![a], groups as nat);
                assert(out@.push(a) =~= out@ + seq![a]);
                assert(enc_tail(out@.push(a)) =~= text@.subrange(4 * groups as int, n as int));
            }
            out.push(a);
        } else {
            let Some(y) = value_for(text[i + 2]) else {
                proof! {
                    lemma_refuse_char(text@.take(n as int), i + 2);
                }
                return None;
            };
            proof! {
                lemma_value(text[i + 2]);
            }
            if y & 3 != 0 {
                proof! {
                    lemma_refuse_tail(text@.take(n as int));
                }
                return None;
            }
            let b = ((x & 15) << 4) | (y >> 2);
            proof! {
                assert(a >> 2 == w && ((a & 3) << 4) | (b >> 4) == x && (b & 15) << 2 == y)
                    by (bit_vector)
                    requires w < 64, x < 64, y < 64, y & 3 == 0,
                        a == (w << 2) | (x >> 4), b == ((x & 15) << 4) | (y >> 2);
                lemma_enc_full_extend(out@, seq![a, b], groups as nat);
                assert(out@.push(a).push(b) =~= out@ + seq![a, b]);
                assert(enc_tail(out@.push(a).push(b)) =~= text@.subrange(4 * groups as int, n as int));
            }
            out.push(a);
            out.push(b);
        }
    } else {
        proof! {
            assert(enc_tail(out@) =~= text@.subrange(4 * groups as int, n as int));
        }
    }
    proof! {
        assert(out@.len() / 3 == groups);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips() {
        for len in 0..40u8 {
            let bytes: Vec<u8> = (0..len).map(|i| i.wrapping_mul(37).wrapping_add(250)).collect();
            assert_eq!(decode(&encode(&bytes)), Some(bytes));
        }
    }

    #[test]
    fn known_vectors() {
        assert_eq!(encode(b"hello?>"), b"aGVsbG8_Pg");
        assert_eq!(decode(b"aGVsbG8_Pg=="), Some(b"hello?>".to_vec()));
        assert_eq!(encode(&[0xfb, 0xff]), b"-_8");
    }

    #[test]
    fn refuses_what_nothing_encodes_to() {
        assert_eq!(decode(b"a"), None);
        assert_eq!(decode(b"a+b/"), None);
        // "AB" would leave the bits 0001 over; only "AA" encodes [0].
        assert_eq!(decode(b"AB"), None);
        assert_eq!(decode(b"AA"), Some(vec![0]));
    }
}
