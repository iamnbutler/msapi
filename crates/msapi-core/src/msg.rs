//! Building text in proven code: bytes and numbers appended to a `String`
//! with the exact characters stated, so a message's content is part of the
//! spec of the function that words it.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_unwrap_or_default,
    clippy::manual_map,
    clippy::single_match,
    clippy::collapsible_if,
    clippy::manual_unwrap_or,
    clippy::single_match_else,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening, `Option` combinators or `if let` chains"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(feature = "verus")]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, length_of_first_scalar, pop_first_scalar, valid_utf8,
};

#[cfg(feature = "verus")]
use crate::decimal::{decimal_text, digits_of};
use crate::decimal::{format_decimal, format_uint};

#[cfg(feature = "verus")]
verus! {

/// Each byte as the character with that code point (ASCII text stays as is).
pub open spec fn chars(b: Seq<u8>) -> Seq<char> {
    b.map_values(|c: u8| c as char)
}

/// The characters `n` prints as: its decimal digits.
pub open spec fn uint_chars(n: nat) -> Seq<char> {
    chars(digits_of(n))
}

/// In UTF-8, the byte after an ASCII byte starts a character, so a `str`
/// may be cut there.
pub proof fn lemma_boundary_after_ascii(bytes: Seq<u8>, i: int)
    requires
        valid_utf8(bytes),
        0 <= i < bytes.len(),
        bytes[i] < 0x80,
    ensures
        is_char_boundary(bytes, i + 1),
    decreases bytes.len(),
{
    let l = length_of_first_scalar(bytes);
    assert(1 <= l <= bytes.len());
    if i < l {
        assert(i == 0 && l == 1);
        reveal_with_fuel(is_char_boundary, 2);
    } else {
        let rest = pop_first_scalar(bytes);
        assert(rest.len() == bytes.len() - l);
        assert(rest[i - l] == bytes[i]);
        lemma_boundary_after_ascii(rest, i - l);
        reveal_with_fuel(is_char_boundary, 2);
    }
}

/// The characters `v` prints as: `-` for negatives, then the digits of `|v|`.
pub open spec fn int_chars(v: int) -> Seq<char> {
    chars(decimal_text(v, 0))
}

} // verus!

/// `b`, one character per byte.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == chars(b@)))]
#[must_use]
pub fn text(b: &[u8]) -> String {
    let mut out = String::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= b@.len(),
            out@ == chars(b@.subrange(0, i as int)),
        decreases b@.len() - i
    ))]
    while i < b.len() {
        proof! {
            assert(chars(b@.subrange(0, i as int + 1)) =~= chars(b@.subrange(0, i as int)).push(b@[i as int] as char));
        }
        out.push(b[i] as char);
        i += 1;
    }
    proof! { assert(b@.subrange(0, b@.len() as int) =~= b@); }
    out
}

/// Appends `b`, one character per byte.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(ensures final(s)@ == old(s)@ + chars(b@)))]
pub fn push_bytes(s: &mut String, b: &[u8]) {
    let t = text(b);
    s.push_str(t.as_str());
}

/// Appends the decimal digits of `n`, as `{}` prints it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(ensures final(s)@ == old(s)@ + uint_chars(n as nat)))]
pub fn push_uint(s: &mut String, n: u128) {
    let d = format_uint(n);
    push_bytes(s, d.as_slice());
}

/// Appends `v` as `{}` prints it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(ensures final(s)@ == old(s)@ + int_chars(v as int)))]
pub fn push_int(s: &mut String, v: i64) {
    let d = format_decimal(v, 0);
    push_bytes(s, d.as_slice());
}

/// `s[start..end]`, with its bytes stated (vstd specifies `str::split_at`,
/// not range indexing).
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires
        start <= end <= s.spec_bytes().len(),
        is_char_boundary(s.spec_bytes(), start as int),
        is_char_boundary(s.spec_bytes(), end as int),
    ensures
        r.spec_bytes() == s.spec_bytes().subrange(start as int, end as int),
))]
#[must_use]
pub fn cut(s: &str, start: usize, end: usize) -> &str {
    let head = s.split_at(end).0;
    proof! {
        encode_utf8_valid_utf8(s@);
        encode_utf8_valid_utf8(head@);
        is_char_boundary_start_end_of_seq(head.spec_bytes());
        if start < end {
            is_char_boundary_iff_not_is_continuation_byte(s.spec_bytes(), start as int);
            is_char_boundary_iff_not_is_continuation_byte(head.spec_bytes(), start as int);
        }
    }
    let r = head.split_at(start).1;
    proof! {
        assert(r.spec_bytes() =~= s.spec_bytes().subrange(start as int, end as int));
    }
    r
}

/// `a` followed by `b`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == a@ + b@))]
#[must_use]
pub fn concat(a: &str, b: &str) -> String {
    let mut s = String::new();
    s.push_str(a);
    s.push_str(b);
    proof! { assert(Seq::<char>::empty() + a@ + b@ =~= a@ + b@); }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_std_formatting() {
        for n in [0u128, 7, 10, 12345, u128::MAX] {
            let mut s = String::new();
            push_uint(&mut s, n);
            assert_eq!(s, n.to_string());
        }
        for v in [0i64, 5, -5, i64::MIN, i64::MAX] {
            let mut s = String::new();
            push_int(&mut s, v);
            assert_eq!(s, v.to_string());
        }
        assert_eq!(text(b"a:b"), "a:b");
        assert_eq!(cut("héllo wörld", 7, 13), "wörld");
    }
}
