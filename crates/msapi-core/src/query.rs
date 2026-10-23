//! Query-string percent decoding (`application/x-www-form-urlencoded`).
//!
//! Verus checks [`percent_decode`] against [`decoded`], a one-step-at-a-time
//! definition: `+` is a space, `%` and two hex digits is that byte, and every
//! other byte (including a `%` without two hex digits after it) is itself.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {

/// The value of an ASCII hex digit.
pub open spec fn hex_value(c: u8) -> Option<u8> {
    if 48 <= c <= 57 {
        Some((c - 48) as u8)
    } else if 97 <= c <= 102 {
        Some((c - 97 + 10) as u8)
    } else if 65 <= c <= 70 {
        Some((c - 65 + 10) as u8)
    } else {
        None
    }
}

/// Whether `s` starts with `%` and two hex digits.
pub open spec fn escape_at(s: Seq<u8>) -> bool {
    s.len() >= 3 && s[0] == 37 && hex_value(s[1]) is Some && hex_value(s[2]) is Some
}

/// The percent-decoding of `s`.
pub open spec fn decoded(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 43 {
        seq![32u8] + decoded(s.skip(1))
    } else if escape_at(s) {
        seq![(hex_value(s[1]).unwrap() * 16 + hex_value(s[2]).unwrap()) as u8] + decoded(s.skip(3))
    } else {
        seq![s[0]] + decoded(s.skip(1))
    }
}

} // verus!

/// The value of an ASCII hex digit.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == hex_value(b)))]
const fn hex(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// Percent-decodes `s`: `+` becomes a space and `%XX` the byte `XX`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == decoded(s@)))]
#[must_use]
pub fn percent_decode(s: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof! {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s@.len(),
            out@ + decoded(s@.subrange(i as int, s@.len() as int)) == decoded(s@),
        decreases s@.len() - i
    ))]
    while i < s.len() {
        let c = s[i];
        let step: usize;
        let byte: u8;
        if c == b'+' {
            byte = b' ';
            step = 1;
        } else if c == b'%' && s.len() - i >= 3 {
            if let (Some(hi), Some(lo)) = (hex(s[i + 1]), hex(s[i + 2])) {
                proof! {
                    assert(escape_at(s@.subrange(i as int, s@.len() as int)));
                }
                byte = hi * 16 + lo;
                step = 3;
            } else {
                proof! {
                    assert(!escape_at(s@.subrange(i as int, s@.len() as int)));
                }
                byte = c;
                step = 1;
            }
        } else {
            proof! {
                assert(!escape_at(s@.subrange(i as int, s@.len() as int)));
            }
            byte = c;
            step = 1;
        }
        proof! {
            assert(s@.subrange(i as int, s@.len() as int).skip(step as int) =~= s@.subrange(i + step, s@.len() as int));
            assert(decoded(s@.subrange(i as int, s@.len() as int)) == seq![byte] + decoded(s@.subrange(i as int, s@.len() as int).skip(step as int)));
            assert(out@.push(byte) + decoded(s@.subrange(i as int, s@.len() as int).skip(step as int)) =~= out@ + decoded(s@.subrange(i as int, s@.len() as int)));
        }
        out.push(byte);
        i += step;
    }
    proof! {
        assert(s@.subrange(i as int, s@.len() as int) =~= Seq::<u8>::empty());
        assert(out@ + decoded(Seq::<u8>::empty()) =~= out@);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes() {
        assert_eq!(percent_decode(b"a+b%2Fc%2fd"), b"a b/c/d");
        assert_eq!(percent_decode(b"100%"), b"100%");
        assert_eq!(percent_decode(b"%zz%4"), b"%zz%4");
        assert_eq!(percent_decode(b"%E2%9C%93"), "✓".as_bytes());
    }
}
