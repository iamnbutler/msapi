//! ASCII case folding for name lookups: regions, worlds and classes.
//!
//! Verus checks [`eq_ignore_case`] against [`same_folded`] and [`fold`]
//! against [`folded`]. Both work on bytes; a non-ASCII byte is never a letter
//! or digit, so they agree with the `char`-level std functions they replace.

#![allow(
    clippy::cast_possible_truncation,
    clippy::manual_range_contains,
    reason = "plain casts and comparisons are what Verus checks; each cast here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {

/// `c` lowercased if it is an ASCII capital, else `c`.
pub open spec fn lower(c: u8) -> u8 {
    if 65 <= c <= 90 { (c + 32) as u8 } else { c }
}

/// Whether `c` is an ASCII letter or digit.
pub open spec fn is_alnum(c: u8) -> bool {
    (48 <= c <= 57) || (65 <= c <= 90) || (97 <= c <= 122)
}

/// `a` and `b` are equal ignoring ASCII case.
pub open spec fn same_folded(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> lower(#[trigger] a[i]) == lower(b[i])
}

/// The ASCII letters and digits of `s`, lowercased.
pub open spec fn folded(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if is_alnum(s.last()) {
        folded(s.drop_last()).push(lower(s.last()))
    } else {
        folded(s.drop_last())
    }
}

/// `s` with its ASCII capitals lowercased.
pub open spec fn lowered(s: Seq<u8>) -> Seq<u8> {
    s.map_values(|c: u8| lower(c))
}

/// Equal ignoring ASCII case is equal after lowering.
pub proof fn lemma_same_folded_lowered(a: Seq<u8>, b: Seq<u8>)
    ensures same_folded(a, b) == (lowered(a) == lowered(b)),
{
    if same_folded(a, b) {
        assert(lowered(a) =~= lowered(b));
    }
    assert(lowered(a).len() == a.len() && lowered(b).len() == b.len());
    if lowered(a) == lowered(b) {
        assert forall|i: int| 0 <= i < a.len() implies lower(#[trigger] a[i]) == lower(b[i]) by {
            assert(lowered(a)[i] == lowered(b)[i]);
        }
    }
}

} // verus!

/// `s` with its ASCII capitals lowercased: `str::to_ascii_lowercase` on bytes.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == lowered(s@)))]
#[must_use]
pub fn lowercase(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s@.len(),
            out@ == lowered(s@.subrange(0, i as int)),
        decreases s@.len() - i
    ))]
    while i < s.len() {
        proof! {
            assert(lowered(s@.subrange(0, i + 1)) =~= lowered(s@.subrange(0, i as int)).push(lower(s@[i as int])));
        }
        out.push(to_lower(s[i]));
        i += 1;
    }
    proof! {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    out
}

/// `c` lowercased if it is an ASCII capital.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == lower(c)))]
const fn to_lower(c: u8) -> u8 {
    if c >= b'A' && c <= b'Z' { c + 32 } else { c }
}

/// Whether `a` and `b` are equal ignoring ASCII case: `str::eq_ignore_ascii_case`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == same_folded(a@, b@)))]
#[must_use]
pub fn eq_ignore_case(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> lower(#[trigger] a@[j]) == lower(b@[j]),
        decreases a@.len() - i
    ))]
    while i < a.len() {
        if to_lower(a[i]) != to_lower(b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// The ASCII letters and digits of `s`, lowercased: `"Night Walker"`,
/// `"night-walker"` and `"nightwalker"` all fold to `"nightwalker"`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == folded(s@)))]
#[must_use]
pub fn fold(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s@.len(),
            out@ == folded(s@.subrange(0, i as int)),
        decreases s@.len() - i
    ))]
    while i < s.len() {
        let c = s[i];
        proof! {
            let t = s@.subrange(0, i as int + 1);
            assert(t.drop_last() =~= s@.subrange(0, i as int));
            assert(t.last() == c);
        }
        if (c >= b'0' && c <= b'9') || (c >= b'A' && c <= b'Z') || (c >= b'a' && c <= b'z') {
            out.push(to_lower(c));
        }
        i += 1;
    }
    proof! {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_std() {
        let words =
            ["", "gms", "GMS", "gMs", "msea", "Kronos", "KRONOS", "kron0s", "Night Walker", "é", "É", "ß", "[]", "@`{"];
        for a in words {
            for b in words {
                assert_eq!(eq_ignore_case(a.as_bytes(), b.as_bytes()), a.eq_ignore_ascii_case(b), "{a} {b}");
            }
            let old: String = a.chars().filter(char::is_ascii_alphanumeric).map(|ch| ch.to_ascii_lowercase()).collect();
            assert_eq!(fold(a.as_bytes()), old.into_bytes(), "{a}");
        }
        for c in 0..=255u8 {
            assert_eq!(to_lower(c), c.to_ascii_lowercase());
            assert_eq!(fold(&[c]), if c.is_ascii_alphanumeric() { vec![c.to_ascii_lowercase()] } else { vec![] });
        }
    }
}
