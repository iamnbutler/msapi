//! Name lookup over a table: the search behind [`crate::class::find`],
//! [`crate::world::find`] and `Region`'s `FromStr`.
//!
//! An [`Index`] maps keys (already folded or lowercased bytes) to the
//! position of a table entry. [`Index::build`] refuses a table where one key
//! would name two different entries, and Verus checks that [`Index::get`]
//! then returns the one entry a key names, or `None` exactly when no key
//! matches.

#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::ascii::lowercase;
#[cfg(feature = "verus")]
use crate::ascii::{lemma_same_folded_lowered, lowered, same_folded};
use crate::webauthn::bytes_eq;

/// Keys and the table position each one names.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug)]
pub struct Index {
    keys: Vec<Vec<u8>>,
    owners: Vec<usize>,
}

#[cfg(feature = "verus")]
verus! {

/// Equal keys always name the same entry.
pub open spec fn consistent(keys: Seq<Vec<u8>>, owners: Seq<usize>) -> bool {
    &&& keys.len() == owners.len()
    &&& forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && #[trigger] keys[i]@ == #[trigger] keys[j]@
        ==> owners[i] == owners[j]
}

/// Some key equal to `q` names `o`.
pub open spec fn names(keys: Seq<Vec<u8>>, owners: Seq<usize>, q: Seq<u8>, o: usize) -> bool {
    exists|i: int| 0 <= i < keys.len() && i < owners.len() && #[trigger] keys[i]@ == q && owners[i] == o
}

impl Index {
    /// The keys.
    pub closed spec fn key_seq(&self) -> Seq<Vec<u8>> {
        self.keys@
    }

    /// The entry positions, one per key.
    pub closed spec fn owner_seq(&self) -> Seq<usize> {
        self.owners@
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

#[cfg_attr(feature = "verus", verus_verify)]
impl Index {
    /// An index of `keys`, where `keys[i]` names entry `owners[i]`. `None`
    /// when the lengths differ or one key names two different entries.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Some(ix) => ix.key_seq() == keys@ && ix.owner_seq() == owners@ && consistent(keys@, owners@),
                None => !consistent(keys@, owners@),
            }
    ))]
    #[must_use]
    pub fn build(keys: Vec<Vec<u8>>, owners: Vec<usize>) -> Option<Self> {
        if keys.len() != owners.len() {
            return None;
        }
        let n = keys.len();
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                n == keys@.len(),
                n == owners@.len(),
                i <= n,
                forall|a: int, b: int| 0 <= a < i && 0 <= b < n && #[trigger] keys@[a]@ == #[trigger] keys@[b]@
                    ==> owners@[a] == owners@[b],
            decreases n - i
        ))]
        while i < n {
            let mut j: usize = 0;
            #[cfg_attr(feature = "verus", verus_spec(
                invariant
                    n == keys@.len(),
                    n == owners@.len(),
                    i < n,
                    j <= n,
                    forall|a: int, b: int| 0 <= a < i && 0 <= b < n && #[trigger] keys@[a]@ == #[trigger] keys@[b]@
                        ==> owners@[a] == owners@[b],
                    forall|b: int| 0 <= b < j && keys@[i as int]@ == #[trigger] keys@[b]@ ==> owners@[i as int] == owners@[b],
                decreases n - j
            ))]
            while j < n {
                if bytes_eq(&keys[i], &keys[j]) && owners[i] != owners[j] {
                    return None;
                }
                j += 1;
            }
            proof! {
                assert forall|a: int, b: int| 0 <= a < i + 1 && 0 <= b < n && #[trigger] keys@[a]@ == #[trigger] keys@[b]@
                    implies owners@[a] == owners@[b] by {
                    if a == i as int {
                        assert(keys@[i as int]@ == keys@[b]@);
                    }
                }
            }
            i += 1;
        }
        Some(Self { keys, owners })
    }

    /// The entry key `q` names, if any.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Some(o) => names(self.key_seq(), self.owner_seq(), q@, o)
                    && (consistent(self.key_seq(), self.owner_seq()) ==>
                        forall|o2: usize| names(self.key_seq(), self.owner_seq(), q@, o2) ==> o2 == o),
                None => forall|i: int| 0 <= i < self.key_seq().len() && i < self.owner_seq().len()
                    ==> #[trigger] self.key_seq()[i]@ != q@,
            }
    ))]
    #[must_use]
    pub fn get(&self, q: &[u8]) -> Option<usize> {
        let n = if self.keys.len() < self.owners.len() { self.keys.len() } else { self.owners.len() };
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                n <= self.keys@.len(),
                n <= self.owners@.len(),
                n == self.keys@.len() || n == self.owners@.len(),
                i <= n,
                forall|j: int| 0 <= j < i ==> #[trigger] self.keys@[j]@ != q@,
            decreases n - i
        ))]
        while i < n {
            if bytes_eq(&self.keys[i], q) {
                {
                    let o = self.owners[i];
                    proof! {
                        assert(self.keys@[i as int]@ == q@);
                        assert(names(self.keys@, self.owners@, q@, o));
                        assert forall|o2: usize| consistent(self.keys@, self.owners@) && names(self.keys@, self.owners@, q@, o2)
                            implies o2 == o by {
                            let k = choose|k: int| 0 <= k < self.keys@.len() && k < self.owners@.len()
                                && #[trigger] self.keys@[k]@ == q@ && self.owners@[k] == o2;
                            assert(self.keys@[i as int]@ == self.keys@[k]@);
                        }
                    }
                    return Some(o);
                }
            }
            i += 1;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_and_refuses() {
        let ix = Index::build(vec![b"a".to_vec(), b"b".to_vec(), b"a".to_vec()], vec![0, 1, 0]).unwrap();
        assert_eq!(ix.get(b"a"), Some(0));
        assert_eq!(ix.get(b"b"), Some(1));
        assert_eq!(ix.get(b"c"), None);
        assert!(Index::build(vec![b"a".to_vec(), b"a".to_vec()], vec![0, 1]).is_none(), "one key, two entries");
        assert!(Index::build(vec![b"a".to_vec()], vec![]).is_none());
    }
}
