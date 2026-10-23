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
    }
}
