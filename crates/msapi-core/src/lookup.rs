//! What name lookups share: the key of a world's name ([`tagged_key`]), and
//! the check that a table's keys are pairwise distinct.
//!
//! The tables themselves, and the search over each, are in [`crate::names`].
//! A table's distinctness is checked by evaluating [`all_distinct`] on its
//! literal keys; [`lemma_all_distinct`] turns that into the statement every
//! search relies on: no two positions hold equal keys.

#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::ascii::lowercase;
#[cfg(feature = "verus")]
use crate::ascii::{lemma_same_folded_lowered, lowered, same_folded};

#[cfg(feature = "verus")]
verus! {

/// `f(i)` differs from each of `f(0)` to `f(j - 1)`.
pub open spec fn differs_from_all(f: spec_fn(int) -> Seq<u8>, i: int, j: int) -> bool
    decreases j,
{
    if j <= 0 { true } else { f(i) != f(j - 1) && differs_from_all(f, i, j - 1) }
}

/// `f(0)` to `f(n - 1)` are pairwise distinct. Written as a recursion so
/// `by (compute_only)` can evaluate it on a literal table.
pub open spec fn all_distinct(f: spec_fn(int) -> Seq<u8>, n: int) -> bool
    decreases n,
{
    if n <= 0 { true } else { differs_from_all(f, n - 1, n - 1) && all_distinct(f, n - 1) }
}

/// `f(0)` to `f(n - 1)` are all below `m`.
pub open spec fn all_below(f: spec_fn(int) -> usize, n: int, m: usize) -> bool
    decreases n,
{
    if n <= 0 { true } else { f(n - 1) < m && all_below(f, n - 1, m) }
}

proof fn lemma_differs_from_all(f: spec_fn(int) -> Seq<u8>, i: int, j: int)
    requires differs_from_all(f, i, j),
    ensures forall|k: int| 0 <= k < j ==> f(i) != #[trigger] f(k),
    decreases j,
{
    if j > 0 {
        lemma_differs_from_all(f, i, j - 1);
    }
}

/// What [`all_distinct`] means: no two of the first `n` positions hold equal keys.
pub proof fn lemma_all_distinct(f: spec_fn(int) -> Seq<u8>, n: int)
    requires all_distinct(f, n),
    ensures forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> #[trigger] f(i) != #[trigger] f(j),
    decreases n,
{
    if n > 0 {
        lemma_all_distinct(f, n - 1);
        lemma_differs_from_all(f, n - 1, n - 1);
    }
}

/// What [`all_below`] means.
pub proof fn lemma_all_below(f: spec_fn(int) -> usize, n: int, m: usize)
    requires all_below(f, n, m),
    ensures forall|i: int| 0 <= i < n ==> #[trigger] f(i) < m,
    decreases n,
{
    if n > 0 {
        lemma_all_below(f, n - 1, m);
    }
}

/// The key of `name` within group `tag`.
pub open spec fn tagged(tag: u8, name: Seq<u8>) -> Seq<u8> {
    seq![tag, 0xffu8] + lowered(name)
}

/// Two tagged keys are equal exactly when the tags are and the names are
/// equal ignoring ASCII case.
pub proof fn lemma_tagged(t1: u8, n1: Seq<u8>, t2: u8, n2: Seq<u8>)
    ensures (tagged(t1, n1) == tagged(t2, n2)) == (t1 == t2 && same_folded(n1, n2)),
{
    lemma_same_folded_lowered(n1, n2);
    if tagged(t1, n1) == tagged(t2, n2) {
        assert(tagged(t1, n1)[0] == t1 && tagged(t2, n2)[0] == t2);
        assert(lowered(n1) =~= tagged(t1, n1).subrange(2, tagged(t1, n1).len() as int));
        assert(lowered(n2) =~= tagged(t2, n2).subrange(2, tagged(t2, n2).len() as int));
    }
}

} // verus!

/// The key of `name` within group `tag` (a world's region): the tag, a byte
/// no UTF-8 text contains, then the name lowercased.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == tagged(tag, name@)))]
#[must_use]
pub fn tagged_key(tag: u8, name: &[u8]) -> Vec<u8> {
    let lower = lowercase(name);
    let mut out = Vec::new();
    out.push(tag);
    out.push(0xff);
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= lower@.len(),
            lower@ == lowered(name@),
            out@ == seq![tag, 0xffu8] + lower@.subrange(0, i as int),
        decreases lower@.len() - i
    ))]
    while i < lower.len() {
        proof! {
            assert(lower@.subrange(0, i + 1) =~= lower@.subrange(0, i as int).push(lower@[i as int]));
            assert(seq![tag, 0xffu8] + lower@.subrange(0, i + 1) =~= (seq![tag, 0xffu8] + lower@.subrange(0, i as int)).push(lower@[i as int]));
        }
        out.push(lower[i]);
        i += 1;
    }
    proof! {
        assert(lower@.subrange(0, lower@.len() as int) =~= lower@);
    }
    out
}
