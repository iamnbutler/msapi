//! Token scope names: parsing a stored scope list and formatting one.
//!
//! A scope set is a bitset (scope `k` is bit `k`; see [`crate::policy`]). On
//! the wire and in the database it is the names of its scopes, separated by
//! spaces. Verus checks that [`parse_scopes`] accepts a text exactly when every
//! whitespace-separated token names a scope, and that [`format_scopes`] writes
//! text that parses back to the same set.
//!
//! Whitespace here is ASCII whitespace (space, tab, LF, VT, FF, CR). The
//! server only parses lists that [`format_scopes`] wrote, which use spaces.

#![allow(clippy::manual_range_contains, reason = "plain comparisons are what Verus checks")]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::policy::bit_set;

/// How many scopes there are.
#[cfg_attr(feature = "verus", verus_verify)]
pub const COUNT: u16 = 8;

#[cfg(feature = "verus")]
verus! {

/// The name of scope `k`, for `k < 8`.
pub open spec fn name(k: u16) -> Seq<u8> {
    match k {
        0 => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],  // accounts:read
        1 => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8],  // accounts:write
        2 => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],  // characters:read
        3 => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8],  // characters:write
        4 => seq![100u8, 101u8, 108u8, 101u8, 116u8, 101u8],  // delete
        5 => seq![116u8, 111u8, 107u8, 101u8, 110u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],  // tokens:read
        6 => seq![116u8, 111u8, 107u8, 101u8, 110u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8],  // tokens:write
        _ => seq![97u8, 117u8, 100u8, 105u8, 116u8, 58u8, 114u8, 101u8, 97u8, 100u8],  // audit:read
    }
}

/// The scope `s` names, if any.
pub open spec fn index_of(s: Seq<u8>) -> Option<u16> {
    if s == name(0) { Some(0u16) } else if s == name(1) { Some(1u16) } else if s == name(2) { Some(2u16) } else if s == name(3) { Some(3u16) } else if s == name(4) { Some(4u16) } else if s == name(5) { Some(5u16) } else if s == name(6) { Some(6u16) } else if s == name(7) { Some(7u16) } else { None }
}

/// ASCII whitespace, as `u8::is_ascii_whitespace` plus vertical tab.
pub open spec fn is_ws(c: u8) -> bool {
    c == 32 || (9 <= c && c <= 13)
}

/// `s` has no whitespace.
pub open spec fn no_ws(s: Seq<u8>) -> bool
    decreases s.len(),
{
    s.len() == 0 || (!is_ws(s.last()) && no_ws(s.drop_last()))
}

/// Ends the token `cur`: adds its scope to `acc`, or fails if it names none.
pub open spec fn flush(acc: Option<u16>, cur: Seq<u8>) -> Option<u16> {
    if cur.len() == 0 {
        acc
    } else {
        match (acc, index_of(cur)) {
            (Some(a), Some(k)) => Some(a | (1u16 << k)),
            _ => None,
        }
    }
}

/// Reads one byte: whitespace ends the current token, anything else extends it.
pub open spec fn step(st: (Option<u16>, Seq<u8>), c: u8) -> (Option<u16>, Seq<u8>) {
    if is_ws(c) { (flush(st.0, st.1), Seq::empty()) } else { (st.0, st.1.push(c)) }
}

/// The scopes so far (`None` once a token named no scope) and the token in progress.
pub open spec fn state(t: Seq<u8>) -> (Option<u16>, Seq<u8>)
    decreases t.len(),
{
    if t.len() == 0 { (Some(0u16), Seq::empty()) } else { step(state(t.drop_last()), t.last()) }
}

/// The set `t` lists: `Some` exactly when every token names a scope.
pub open spec fn parse(t: Seq<u8>) -> Option<u16> {
    flush(state(t).0, state(t).1)
}

/// The names of the scopes below `k` in `bits`, in order, separated by spaces.
pub open spec fn fmt(bits: u16, k: u16) -> Seq<u8>
    decreases k,
{
    if k == 0 {
        Seq::empty()
    } else {
        let p = fmt(bits, (k - 1) as u16);
        if bit_set(bits, (k - 1) as u16) {
            if p.len() == 0 { name((k - 1) as u16) } else { p.push(32u8) + name((k - 1) as u16) }
        } else {
            p
        }
    }
}

/// The scopes below `k` in `bits`.
pub open spec fn low(bits: u16, k: u16) -> u16 {
    bits & !(0xffffu16 << k)
}

/// Each name names its own scope and has no whitespace.
pub proof fn lemma_names(k: u16)
    requires k < 8,
    ensures index_of(name(k)) == Some(k), no_ws(name(k)), name(k).len() > 0,
{
    assert(index_of(name(0)) == Some(0u16) && no_ws(name(0))) by (compute);
    assert(index_of(name(1)) == Some(1u16) && no_ws(name(1))) by (compute);
    assert(index_of(name(2)) == Some(2u16) && no_ws(name(2))) by (compute);
    assert(index_of(name(3)) == Some(3u16) && no_ws(name(3))) by (compute);
    assert(index_of(name(4)) == Some(4u16) && no_ws(name(4))) by (compute);
    assert(index_of(name(5)) == Some(5u16) && no_ws(name(5))) by (compute);
    assert(index_of(name(6)) == Some(6u16) && no_ws(name(6))) by (compute);
    assert(index_of(name(7)) == Some(7u16) && no_ws(name(7))) by (compute);
}

/// A word without whitespace only extends the token in progress.
proof fn lemma_word(s: Seq<u8>, w: Seq<u8>)
    requires no_ws(w),
    ensures state(s + w) == (state(s).0, state(s).1 + w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(s + w =~= s);
        assert(state(s).1 + w =~= state(s).1);
    } else {
        lemma_word(s, w.drop_last());
        assert((s + w).drop_last() =~= s + w.drop_last());
        assert((state(s).1 + w.drop_last()).push(w.last()) =~= state(s).1 + w);
    }
}

/// Once a token has named no scope, the whole text fails.
proof fn lemma_stuck(t: Seq<u8>, n: int)
    requires 0 <= n <= t.len(), state(t.subrange(0, n)).0 is None,
    ensures parse(t) is None,
    decreases t.len() - n,
{
    if n == t.len() {
        assert(t.subrange(0, n) =~= t);
    } else {
        assert(t.subrange(0, n + 1).drop_last() =~= t.subrange(0, n));
        lemma_stuck(t, n + 1);
    }
}

/// How the scopes below `k + 1` follow from those below `k`.
proof fn lemma_low(bits: u16, k: u16)
    requires k < 8,
    ensures
        low(bits, 0) == 0,
        low(bits, 8) == bits & 0xff,
        low(bits, (k + 1) as u16) == if bit_set(bits, k) { low(bits, k) | (1u16 << k) } else { low(bits, k) },
{
    assert(bits & !(0xffffu16 << 0u16) == 0u16 && bits & !(0xffffu16 << 8u16) == bits & 0xff) by (bit_vector);
    assert(bits & !(0xffffu16 << add(k, 1u16)) == if (bits >> k) & 1u16 == 1u16 {
        (bits & !(0xffffu16 << k)) | (1u16 << k)
    } else {
        bits & !(0xffffu16 << k)
    }) by (bit_vector)
        requires k < 8;
}

} // verus!

/// The name of scope `k`, e.g. `b"characters:write"` for 3.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => requires k < 8, ensures r@ == name(k)))]
#[must_use]
pub fn scope_name(k: u16) -> &'static [u8] {
    let r: &'static [u8] = match k {
        0 => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],
        1 => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8],
        2 => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],
        3 => {
            &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8]
        }
        4 => &[100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        5 => &[116u8, 111u8, 107u8, 101u8, 110u8, 115u8, 58u8, 114u8, 101u8, 97u8, 100u8],
        6 => &[116u8, 111u8, 107u8, 101u8, 110u8, 115u8, 58u8, 119u8, 114u8, 105u8, 116u8, 101u8],
        _ => &[97u8, 117u8, 100u8, 105u8, 116u8, 58u8, 114u8, 101u8, 97u8, 100u8],
    };
    proof! {
        assert(r@ =~= name(k));
    }
    r
}

/// Whether `t[start..end]` is `w`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires start <= end <= t@.len(),
    ensures r == (t@.subrange(start as int, end as int) == w@),
))]
fn matches_at(t: &[u8], start: usize, end: usize, w: &[u8]) -> bool {
    if end - start != w.len() {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= end <= t@.len(),
            end - start == w@.len(),
            i <= w@.len(),
            forall|j: int| 0 <= j < i ==> t@[start + j] == w@[j],
        decreases w@.len() - i
    ))]
    while i < w.len() {
        if t[start + i] != w[i] {
            proof! {
                assert(t@.subrange(start as int, end as int)[i as int] != w@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof! {
        assert(t@.subrange(start as int, end as int) =~= w@);
    }
    true
}

/// The scope `t[start..end]` names, if any.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires start <= end <= t@.len(),
    ensures r == index_of(t@.subrange(start as int, end as int)),
))]
fn scope_at(t: &[u8], start: usize, end: usize) -> Option<u16> {
    let mut k: u16 = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            k <= 8,
            start <= end <= t@.len(),
            forall|j: u16| j < k ==> t@.subrange(start as int, end as int) != #[trigger] name(j),
        decreases 8 - k
    ))]
    while k < COUNT {
        if matches_at(t, start, end, scope_name(k)) {
            return Some(k);
        }
        k += 1;
    }
    None
}

/// The scope `name` names, if any.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == index_of(name@)))]
#[must_use]
pub fn scope_index(name: &[u8]) -> Option<u16> {
    proof! {
        assert(name@.subrange(0, name@.len() as int) =~= name@);
    }
    scope_at(name, 0, name.len())
}

/// The scope set `text` lists, or the byte range of the first token that names
/// no scope. Tokens are separated by runs of ASCII whitespace.
///
/// # Errors
///
/// `Err((start, end))` when `text[start..end]` is a token that names no scope.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Ok(bits) ==> parse(text@) == Some(bits),
        r matches Err((start, end)) ==> parse(text@) is None && start < end <= text@.len()
            && index_of(text@.subrange(start as int, end as int)) is None
            && (start == 0 || is_ws(text@[start - 1]))
            && (end == text@.len() || is_ws(text@[end as int])),
))]
pub fn parse_scopes(text: &[u8]) -> Result<u16, (usize, usize)> {
    let mut acc: u16 = 0;
    let mut start: usize = 0;
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= i <= text@.len(),
            state(text@.subrange(0, i as int)) == (Some(acc), text@.subrange(start as int, i as int)),
            start == 0 || is_ws(text@[start - 1]),
        decreases text@.len() - i
    ))]
    while i < text.len() {
        proof! {
            assert(text@.subrange(0, i + 1).drop_last() =~= text@.subrange(0, i as int));
        }
        let c = text[i];
        proof! {
            assert(text@.subrange(start as int, i + 1) =~= text@.subrange(start as int, i as int).push(c));
        }
        if c == b' ' || (c >= 9 && c <= 13) {
            if start < i {
                match scope_at(text, start, i) {
                    Some(k) => acc |= 1 << k,
                    None => {
                        proof! {
                            lemma_stuck(text@, i + 1);
                        }
                        return Err((start, i));
                    }
                }
            }
            start = i + 1;
            proof! {
                assert(text@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
            }
        }
        i += 1;
    }
    proof! {
        assert(text@.subrange(0, text@.len() as int) =~= text@);
    }
    if start < i {
        match scope_at(text, start, i) {
            Some(k) => acc |= 1 << k,
            None => return Err((start, i)),
        }
    }
    Ok(acc)
}

/// The names of the scopes in `bits`, in order, separated by single spaces.
/// Bits above the last scope are ignored.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@ == fmt(bits, 8),
        parse(r@) == Some(bits & 0xff),
))]
#[must_use]
pub fn format_scopes(bits: u16) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut k: u16 = 0;
    proof! {
        lemma_low(bits, 0);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            k <= 8,
            out@ == fmt(bits, k),
            out@.len() == 0 ==> low(bits, k) == 0,
            out@.len() > 0 ==> state(out@).1.len() > 0 && flush(state(out@).0, state(out@).1) == Some(low(bits, k)),
        decreases 8 - k
    ))]
    while k < COUNT {
        proof! {
            lemma_low(bits, k);
            lemma_names(k);
        }
        if (bits >> k) & 1 == 1 {
            if !out.is_empty() {
                proof! {
                    assert(out@.push(32u8).drop_last() =~= out@);
                }
                out.push(b' ');
            }
            proof! {
                lemma_word(out@, name(k));
                assert(state(out@).1 + name(k) =~= name(k));
            }
            push_all(&mut out, scope_name(k));
        }
        k += 1;
    }
    proof! {
        lemma_low(bits, 0);
    }
    out
}

/// Appends `w` to `out`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(ensures final(out)@ == old(out)@ + w@))]
fn push_all(out: &mut Vec<u8>, w: &[u8]) {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= w@.len(),
            out@ == old(out)@ + w@.subrange(0, i as int),
        decreases w@.len() - i
    ))]
    while i < w.len() {
        proof! {
            assert(w@.subrange(0, i + 1) =~= w@.subrange(0, i as int).push(w@[i as int]));
        }
        out.push(w[i]);
        i += 1;
    }
    proof! {
        assert(w@.subrange(0, w@.len() as int) =~= w@);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_formats() {
        assert_eq!(parse_scopes(b"characters:read  characters:write\n"), Ok(0b1100));
        assert_eq!(parse_scopes(b""), Ok(0));
        assert_eq!(parse_scopes(b"delete characters:admin tokens:read"), Err((7, 23)));
        assert_eq!(format_scopes(0b1100), b"characters:read characters:write");
        assert_eq!(format_scopes(0xffff), format_scopes(0xff));
        for bits in 0..=0xff {
            assert_eq!(parse_scopes(&format_scopes(bits)), Ok(bits));
        }
    }
}
