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

/// Where `x` first occurs in `q[i..e]`, or `e` if it does not.
pub open spec fn find(q: Seq<u8>, i: int, e: int, x: u8) -> int
    decreases e - i,
{
    if i >= e {
        e
    } else if q[i] == x {
        i
    } else {
        find(q, i + 1, e, x)
    }
}

proof fn lemma_find_bounds(q: Seq<u8>, i: int, e: int, x: u8)
    requires i <= e,
    ensures i <= find(q, i, e, x) <= e,
    decreases e - i,
{
    if i < e && q[i] != x {
        lemma_find_bounds(q, i + 1, e, x);
    }
}

/// The parameter whose text starts at `i`: the decoded text before the first
/// `=` of its `&`-segment, and the decoded text after it (empty if none).
pub open spec fn pair_at(q: Seq<u8>, i: int) -> (Seq<u8>, Seq<u8>) {
    let e = find(q, i, q.len() as int, 38);
    let m = find(q, i, e, 61);
    (decoded(q.subrange(i, m)), if m < e { decoded(q.subrange(m + 1, e)) } else { Seq::empty() })
}

/// The parameters of `q` from byte `i` on, skipping empty segments.
pub open spec fn pairs(q: Seq<u8>, i: int) -> Seq<(Seq<u8>, Seq<u8>)>
    decreases q.len() - i,
{
    if i < 0 || i >= q.len() {
        Seq::empty()
    } else {
        let e = find(q, i, q.len() as int, 38);
        let rest = if e < q.len() && e >= i { pairs(q, e + 1) } else { Seq::empty() };
        if e <= i { rest } else { seq![pair_at(q, i)] + rest }
    }
}

/// Decoded pairs as sequences.
pub open spec fn pairs_view(ps: Seq<Pair>) -> Seq<(Seq<u8>, Seq<u8>)> {
    ps.map_values(|p: Pair| (p.name@, p.value@))
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

/// Percent-decodes `s[from..to]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires from <= to <= s@.len(),
    ensures r@ == decoded(s@.subrange(from as int, to as int))
))]
fn decode_range(s: &[u8], from: usize, to: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = from;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            from <= i <= to,
            to <= s@.len(),
            out@ + decoded(s@.subrange(i as int, to as int)) == decoded(s@.subrange(from as int, to as int)),
        decreases to - i
    ))]
    while i < to {
        let c = s[i];
        let step: usize;
        let byte: u8;
        if c == b'+' {
            byte = b' ';
            step = 1;
        } else if c == b'%' && to - i >= 3 {
            if let (Some(hi), Some(lo)) = (hex(s[i + 1]), hex(s[i + 2])) {
                proof! {
                    assert(escape_at(s@.subrange(i as int, to as int)));
                }
                byte = hi * 16 + lo;
                step = 3;
            } else {
                proof! {
                    assert(!escape_at(s@.subrange(i as int, to as int)));
                }
                byte = c;
                step = 1;
            }
        } else {
            proof! {
                assert(!escape_at(s@.subrange(i as int, to as int)));
            }
            byte = c;
            step = 1;
        }
        proof! {
            assert(s@.subrange(i as int, to as int).skip(step as int) =~= s@.subrange(i + step, to as int));
            assert(decoded(s@.subrange(i as int, to as int)) == seq![byte] + decoded(s@.subrange(i as int, to as int).skip(step as int)));
            assert(out@.push(byte) + decoded(s@.subrange(i as int, to as int).skip(step as int)) =~= out@ + decoded(s@.subrange(i as int, to as int)));
        }
        out.push(byte);
        i += step;
    }
    proof! {
        assert(s@.subrange(i as int, to as int) =~= Seq::<u8>::empty());
        assert(out@ + decoded(Seq::<u8>::empty()) =~= out@);
    }
    out
}

/// Percent-decodes `s`: `+` becomes a space and `%XX` the byte `XX`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == decoded(s@)))]
#[must_use]
pub fn percent_decode(s: &[u8]) -> Vec<u8> {
    proof! {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    decode_range(s, 0, s.len())
}

/// One query parameter: its decoded name and value.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub struct Pair {
    /// The decoded name.
    pub name: Vec<u8>,
    /// The decoded value; empty when the parameter has no `=`.
    pub value: Vec<u8>,
}

/// Where `x` first occurs in `q[i..e]`, or `e`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i <= e <= q@.len(),
    ensures r as int == find(q@, i as int, e as int, x)
))]
#[allow(clippy::many_single_char_names, reason = "named to match the `find` spec")]
fn find_byte(q: &[u8], i: usize, e: usize, x: u8) -> usize {
    let mut j = i;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= j <= e,
            e <= q@.len(),
            find(q@, j as int, e as int, x) == find(q@, i as int, e as int, x),
        decreases e - j
    ))]
    while j < e && q[j] != x {
        j += 1;
    }
    j
}

/// Splits a query string at `&`, skips empty parameters, splits each at its
/// first `=` (no `=` means an empty value) and percent-decodes both halves.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures pairs_view(r@) == pairs(q@, 0)))]
#[must_use]
#[allow(clippy::needless_else, reason = "the `else` holds a proof block, which compiles away")]
pub fn parse_query(q: &[u8]) -> Vec<Pair> {
    let mut out: Vec<Pair> = Vec::new();
    let mut i: usize = 0;
    proof! {
        assert(pairs_view(out@) + pairs(q@, 0) =~= pairs(q@, 0));
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= q@.len(),
            pairs_view(out@) + pairs(q@, i as int) == pairs(q@, 0),
        decreases q@.len() - i
    ))]
    while i < q.len() {
        let e = find_byte(q, i, q.len(), b'&');
        let next = if e < q.len() { e + 1 } else { q.len() };
        proof! {
            lemma_find_bounds(q@, i as int, q@.len() as int, 38);
            assert(pairs(q@, next as int) == if e < q@.len() { pairs(q@, e + 1) } else { Seq::empty() });
        }
        if e > i {
            let m = find_byte(q, i, e, b'=');
            proof! {
                lemma_find_bounds(q@, i as int, e as int, 61);
            }
            let name = decode_range(q, i, m);
            let value = if m < e { decode_range(q, m + 1, e) } else { Vec::new() };
            proof! {
                assert(value@ == pair_at(q@, i as int).1);
                let p = Pair { name, value };
                assert(pairs_view(out@.push(p)) =~= pairs_view(out@).push((name@, value@)));
                assert(pairs_view(out@.push(p)) + pairs(q@, next as int) =~= pairs_view(out@) + pairs(q@, i as int));
            }
            out.push(Pair { name, value });
        } else {
            proof! {
                assert(pairs(q@, i as int) == pairs(q@, next as int));
            }
        }
        i = next;
    }
    proof! {
        assert(pairs_view(out@) + Seq::empty() =~= pairs_view(out@));
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

    #[test]
    fn splits() {
        let pair = |n: &str, v: &str| Pair { name: n.into(), value: v.into() };
        assert_eq!(
            parse_query(b"a=1&&b=x%3Dy=z&c&=v&"),
            vec![pair("a", "1"), pair("b", "x=y=z"), pair("c", ""), pair("", "v")]
        );
        assert_eq!(parse_query(b""), vec![]);
    }
}
