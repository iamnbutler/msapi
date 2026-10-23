//! JSON Merge Patch (RFC 7396) over a small JSON model.
//!
//! The server converts `serde_json` values to [`Json`] and back; the merge
//! itself is here, checked by Verus against [`merged`], which states the RFC's
//! rule key by key: a `null` member removes its key, any other member's key
//! becomes the merge of the target's value (or `null`) with it, every other
//! key keeps the target's value, and a patch that is not an object replaces
//! the target. Objects are compared as maps, so member order is not part of
//! the result's meaning (the server's maps are sorted anyway).

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]
#![allow(
    clippy::many_single_char_names,
    clippy::len_zero,
    reason = "k, v, i, j and b name keys, values and indices as the RFC does; vstd has no spec for `Vec::is_empty`"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::webauthn::bytes_eq;

/// A JSON value. Numbers and strings are kept as their bytes: the merge
/// never looks inside them.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug)]
pub enum Json {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// A number, as its JSON text.
    Number(Vec<u8>),
    /// A string's UTF-8 bytes.
    Str(Vec<u8>),
    /// An array.
    Array(Vec<Json>),
    /// An object: member `i` has key `keys[i]` and value `values[i]`.
    Object(Vec<Vec<u8>>, Vec<Json>),
}

#[cfg(feature = "verus")]
verus! {

/// No key appears twice.
pub open spec fn unique(keys: Seq<Vec<u8>>) -> bool {
    forall|i: int, j: int| #![trigger keys[i], keys[j]] 0 <= i < j < keys.len() ==> keys[i]@ != keys[j]@
}

/// Some member has key `k`.
pub open spec fn has_key(keys: Seq<Vec<u8>>, k: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k
}

/// The value under key `k`.
pub open spec fn lookup(keys: Seq<Vec<u8>>, values: Seq<Json>, k: Seq<u8>) -> Option<Json> {
    if has_key(keys, k) {
        Some(values[choose|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k])
    } else {
        None
    }
}

/// The target's value under key `k`, or `null`: a target that is not an
/// object counts as `{}`.
pub open spec fn target_value(keys: Seq<Vec<u8>>, values: Seq<Json>, k: Seq<u8>) -> Json {
    match lookup(keys, values, k) {
        Some(v) => v,
        None => Json::Null,
    }
}

/// Well-formed: every object has as many keys as values, and no repeated key.
pub open spec fn wf(j: Json) -> bool
    decreases j,
{
    match j {
        Json::Array(v) => forall|i: int| 0 <= i < v.len() ==> wf(#[trigger] v@[i]),
        Json::Object(k, v) => k.len() == v.len() && unique(k@) && forall|i: int| 0 <= i < v.len() ==> wf(#[trigger] v@[i]),
        _ => true,
    }
}

/// The object part of a target: its keys and values, or none.
pub open spec fn keys_of(t: Json) -> Seq<Vec<u8>> {
    match t {
        Json::Object(k, _) => k@,
        _ => Seq::empty(),
    }
}

/// See [`keys_of`].
pub open spec fn values_of(t: Json) -> Seq<Json> {
    match t {
        Json::Object(_, v) => v@,
        _ => Seq::empty(),
    }
}

/// `r` is the result of merging patch `p` into target `t` (RFC 7396 §2).
pub open spec fn merged(r: Json, t: Json, p: Json) -> bool
    decreases p,
{
    match p {
        Json::Object(pk, pv) => match r {
            Json::Object(rk, rv) => {
                &&& rk.len() == rv.len()
                &&& unique(rk@)
                &&& forall|i: int| 0 <= i < pv.len() && 0 <= i < pk.len() ==> {
                    let k = pk@[i]@;
                    if #[trigger] pv@[i] is Null {
                        !has_key(rk@, k)
                    } else {
                        has_key(rk@, k) && merged(lookup(rk@, rv@, k).unwrap(), target_value(keys_of(t), values_of(t), k), pv@[i])
                    }
                }
                &&& forall|k: Seq<u8>| !has_key(pk@, k) ==> #[trigger] lookup(rk@, rv@, k) == lookup(keys_of(t), values_of(t), k)
            },
            _ => false,
        },
        _ => r == p,
    }
}

/// With unique keys, the member at `i` is what [`lookup`] finds.
proof fn lemma_lookup_at(keys: Seq<Vec<u8>>, values: Seq<Json>, i: int)
    requires unique(keys), 0 <= i < keys.len(), keys.len() == values.len(),
    ensures has_key(keys, keys[i]@), lookup(keys, values, keys[i]@) == Some(values[i]),
{
    let k = keys[i]@;
    assert(has_key(keys, k));
    let j = choose|j: int| 0 <= j < keys.len() && (#[trigger] keys[j])@ == k;
    if j != i {
        if j < i {
            assert(keys[j]@ != keys[i]@);
        } else {
            assert(keys[i]@ != keys[j]@);
        }
    }
}

/// A key found by [`lookup`] is at some index holding that value.
proof fn lemma_lookup_some(keys: Seq<Vec<u8>>, values: Seq<Json>, k: Seq<u8>)
    requires unique(keys), keys.len() == values.len(), has_key(keys, k),
    ensures exists|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k && lookup(keys, values, k) == Some(values[i]),
{
    let i = choose|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k;
    lemma_lookup_at(keys, values, i);
}

/// Removing member `j` removes its key and keeps every other lookup.
proof fn lemma_remove(keys: Seq<Vec<u8>>, values: Seq<Json>, j: int)
    requires unique(keys), keys.len() == values.len(), 0 <= j < keys.len(),
    ensures
        unique(keys.remove(j)),
        !has_key(keys.remove(j), keys[j]@),
        forall|k: Seq<u8>| k != keys[j]@ ==> #[trigger] lookup(keys.remove(j), values.remove(j), k) == lookup(keys, values, k),
{
    let nk = keys.remove(j);
    let nv = values.remove(j);
    assert forall|a: int, b: int| #![trigger nk[a], nk[b]] 0 <= a < b < nk.len() implies nk[a]@ != nk[b]@ by {
        let a0 = if a < j { a } else { a + 1 };
        let b0 = if b < j { b } else { b + 1 };
        assert(nk[a] == keys[a0] && nk[b] == keys[b0]);
        assert(keys[a0]@ != keys[b0]@);
    }
    if has_key(nk, keys[j]@) {
        let a = choose|a: int| 0 <= a < nk.len() && (#[trigger] nk[a])@ == keys[j]@;
        let a0 = if a < j { a } else { a + 1 };
        assert(nk[a] == keys[a0]);
        if a0 < j {
            assert(keys[a0]@ != keys[j]@);
        } else {
            assert(keys[j]@ != keys[a0]@);
        }
    }
    assert forall|k: Seq<u8>| k != keys[j]@ implies #[trigger] lookup(nk, nv, k) == lookup(keys, values, k) by {
        if has_key(keys, k) {
            lemma_lookup_some(keys, values, k);
            let i = choose|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k && lookup(keys, values, k) == Some(values[i]);
            assert(i != j);
            let a = if i < j { i } else { i - 1 };
            assert(nk[a] == keys[i] && nv[a] == values[i]);
            lemma_lookup_at(nk, nv, a);
        } else {
            if has_key(nk, k) {
                let a = choose|a: int| 0 <= a < nk.len() && (#[trigger] nk[a])@ == k;
                let a0 = if a < j { a } else { a + 1 };
                assert(nk[a] == keys[a0]);
                assert(has_key(keys, k));
            }
        }
    }
}

/// Appending a member with a new key adds it and keeps every other lookup.
proof fn lemma_push(keys: Seq<Vec<u8>>, values: Seq<Json>, key: Vec<u8>, value: Json)
    requires unique(keys), keys.len() == values.len(), !has_key(keys, key@),
    ensures
        unique(keys.push(key)),
        has_key(keys.push(key), key@),
        lookup(keys.push(key), values.push(value), key@) == Some(value),
        forall|k: Seq<u8>| k != key@ ==> #[trigger] lookup(keys.push(key), values.push(value), k) == lookup(keys, values, k),
{
    let nk = keys.push(key);
    let nv = values.push(value);
    assert forall|a: int, b: int| #![trigger nk[a], nk[b]] 0 <= a < b < nk.len() implies nk[a]@ != nk[b]@ by {
        if b == keys.len() {
            assert(nk[a] == keys[a]);
        } else {
            assert(nk[a] == keys[a] && nk[b] == keys[b]);
        }
    }
    lemma_lookup_at(nk, nv, keys.len() as int);
    assert(nk[keys.len() as int] == key);
    assert forall|k: Seq<u8>| k != key@ implies #[trigger] lookup(nk, nv, k) == lookup(keys, values, k) by {
        if has_key(keys, k) {
            lemma_lookup_some(keys, values, k);
            let i = choose|i: int| 0 <= i < keys.len() && (#[trigger] keys[i])@ == k && lookup(keys, values, k) == Some(values[i]);
            assert(nk[i] == keys[i] && nv[i] == values[i]);
            lemma_lookup_at(nk, nv, i);
        } else if has_key(nk, k) {
            let a = choose|a: int| 0 <= a < nk.len() && (#[trigger] nk[a])@ == k;
            assert(a < keys.len());
            assert(nk[a] == keys[a]);
        }
    }
}

/// A value in a well-formed object is well-formed.
proof fn lemma_wf_lookup(keys: Seq<Vec<u8>>, values: Seq<Json>, k: Seq<u8>)
    requires
        unique(keys), keys.len() == values.len(),
        forall|i: int| 0 <= i < values.len() ==> wf(#[trigger] values[i]),
    ensures wf(target_value(keys, values, k)),
{
    if has_key(keys, k) {
        lemma_lookup_some(keys, values, k);
    }
}

/// The keys from `n` on are the key at `n` and the keys after it.
proof fn lemma_keys_from(keys: Seq<Vec<u8>>, n: int)
    requires 0 <= n < keys.len(),
    ensures
        forall|k: Seq<u8>| #[trigger] has_key(keys.subrange(n, keys.len() as int), k)
            == (keys[n]@ == k || has_key(keys.subrange(n + 1, keys.len() as int), k)),
{
    let a = keys.subrange(n, keys.len() as int);
    let b = keys.subrange(n + 1, keys.len() as int);
    assert forall|k: Seq<u8>| #[trigger] has_key(a, k) == (keys[n]@ == k || has_key(b, k)) by {
        if has_key(a, k) {
            let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i])@ == k;
            if i > 0 {
                assert(a[i] == b[i - 1]);
            }
        }
        if keys[n]@ == k {
            assert(a[0] == keys[n]);
        }
        if has_key(b, k) {
            let i = choose|i: int| 0 <= i < b.len() && (#[trigger] b[i])@ == k;
            assert(a[i + 1] == b[i]);
        }
    }
}

/// The items of an array.
pub open spec fn items_of(j: Json) -> Seq<Json> {
    match j {
        Json::Array(v) => v@,
        _ => Seq::empty(),
    }
}

/// Unfolds [`wf`] one level.
proof fn lemma_wf_unfold(j: Json)
    ensures
        j is Array ==> (wf(j) <==> forall|i: int| 0 <= i < items_of(j).len() ==> wf(#[trigger] items_of(j)[i])),
        j is Object ==> (wf(j) <==> (keys_of(j).len() == values_of(j).len() && unique(keys_of(j))
            && forall|i: int| 0 <= i < values_of(j).len() ==> wf(#[trigger] values_of(j)[i]))),
{
    match j {
        Json::Array(v) => {
            assert(items_of(j) == v@);
        },
        Json::Object(k, v) => {
            assert(keys_of(j) == k@ && values_of(j) == v@);
        },
        _ => {},
    }
}

/// Unfolds [`wf`] on an object's members.
proof fn lemma_wf_object(j: Json)
    requires wf(j), j is Object,
    ensures
        keys_of(j).len() == values_of(j).len(),
        unique(keys_of(j)),
        forall|i: int| 0 <= i < values_of(j).len() ==> wf(#[trigger] values_of(j)[i]),
{
    if let Json::Object(k, v) = j {
        assert forall|i: int| 0 <= i < values_of(j).len() implies wf(#[trigger] values_of(j)[i]) by {
            assert(values_of(j)[i] == v@[i]);
        }
    }
}

} // verus!

/// Whether `j` is `null`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (*j is Null)))]
const fn is_null(j: &Json) -> bool {
    matches!(j, Json::Null)
}

/// Where key `k` is among `keys`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(i) ==> i < keys@.len() && keys@[i as int]@ == k@,
        r is None ==> !has_key(keys@, k@),
))]
fn find_key(keys: &[Vec<u8>], k: &[u8]) -> Option<usize> {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= keys@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] keys@[j])@ != k@,
        decreases keys@.len() - i
    ))]
    while i < keys.len() {
        if bytes_eq(keys[i].as_slice(), k) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Whether `j` is [`wf`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == wf(*j), decreases *j))]
fn check_wf(j: &Json) -> bool {
    proof! {
        lemma_wf_unfold(*j);
    }
    match j {
        Json::Array(v) => {
            let mut i: usize = 0;
            #[cfg_attr(feature = "verus", verus_spec(
                invariant
                    *j == Json::Array(*v),
                    items_of(*j) == v@,
                    i <= v@.len(),
                    forall|a: int| 0 <= a < i ==> wf(#[trigger] v@[a]),
                decreases v@.len() - i
            ))]
            while i < v.len() {
                if !check_wf(&v[i]) {
                    return false;
                }
                i += 1;
            }
            true
        }
        Json::Object(k, v) => {
            if k.len() != v.len() {
                return false;
            }
            let mut i: usize = 0;
            #[cfg_attr(feature = "verus", verus_spec(
                invariant
                    *j == Json::Object(*k, *v),
                    keys_of(*j) == k@,
                    values_of(*j) == v@,
                    k@.len() == v@.len(),
                    i <= v@.len(),
                    forall|a: int, b: int| #![trigger k@[a], k@[b]] 0 <= a < b < i ==> k@[a]@ != k@[b]@,
                    forall|a: int| 0 <= a < i ==> wf(#[trigger] v@[a]),
                decreases v@.len() - i
            ))]
            while i < v.len() {
                if !check_wf(&v[i]) {
                    return false;
                }
                let mut b: usize = 0;
                #[cfg_attr(feature = "verus", verus_spec(
                    invariant
                        *j == Json::Object(*k, *v),
                        keys_of(*j) == k@,
                        k@.len() == v@.len(),
                        i < v@.len(),
                        b <= i,
                        forall|a: int| 0 <= a < b ==> (#[trigger] k@[a])@ != k@[i as int]@,
                    decreases i - b
                ))]
                while b < i {
                    if bytes_eq(k[b].as_slice(), k[i].as_slice()) {
                        proof! {
                            assert(k@[b as int]@ == k@[i as int]@);
                            assert(!unique(k@));
                            lemma_wf_unfold(*j);
                        }
                        return false;
                    }
                    b += 1;
                }
                i += 1;
            }
            true
        }
        _ => true,
    }
}

/// Merges `patch` into `target`. `None` only when either is not [`wf`] (an
/// object with a repeated key), which `serde_json` values never are.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(x) ==> merged(x, target, patch),
        r is None <==> !(wf(target) && wf(patch)),
))]
#[must_use]
pub fn merge(target: Json, patch: Json) -> Option<Json> {
    if check_wf(&target) && check_wf(&patch) { Some(merge_patch(target, patch)) } else { None }
}

/// [`merge`] on well-formed values.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires wf(target), wf(patch),
    ensures merged(r, target, patch),
    decreases patch
))]
fn merge_patch(target: Json, patch: Json) -> Json {
    match patch {
        Json::Object(mut pk, mut pv) => {
            let (mut tk, mut tv) = match target {
                Json::Object(k, v) => (k, v),
                _ => (Vec::new(), Vec::new()),
            };
            proof! {
                lemma_wf_object(patch);
                if target is Object {
                    lemma_wf_object(target);
                }
                assert(tk@ == keys_of(target) && tv@ == values_of(target));
                assert(pk@ == keys_of(patch) && pv@ == values_of(patch));
            }
            merge_members(&mut tk, &mut tv, &mut pk, &mut pv);
            Json::Object(tk, tv)
        }
        _ => patch,
    }
}

/// Applies the members `pk`/`pv` of an object patch to the members `tk`/`tv`
/// of the target, emptying the patch.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    requires
        old(tk)@.len() == old(tv)@.len(),
        unique(old(tk)@),
        forall|i: int| 0 <= i < old(tv)@.len() ==> wf(#[trigger] old(tv)@[i]),
        old(pk)@.len() == old(pv)@.len(),
        unique(old(pk)@),
        forall|i: int| 0 <= i < old(pv)@.len() ==> wf(#[trigger] old(pv)@[i]),
    ensures
        final(tk)@.len() == final(tv)@.len(),
        unique(final(tk)@),
        forall|i: int| 0 <= i < old(pv)@.len() ==> {
            let k = old(pk)@[i]@;
            if #[trigger] old(pv)@[i] is Null {
                !has_key(final(tk)@, k)
            } else {
                has_key(final(tk)@, k) && merged(lookup(final(tk)@, final(tv)@, k).unwrap(), target_value(old(tk)@, old(tv)@, k), old(pv)@[i])
            }
        },
        forall|k: Seq<u8>| !has_key(old(pk)@, k) ==> #[trigger] lookup(final(tk)@, final(tv)@, k) == lookup(old(tk)@, old(tv)@, k),
    decreases *old(pv)
))]
fn merge_members(tk: &mut Vec<Vec<u8>>, tv: &mut Vec<Json>, pk: &mut Vec<Vec<u8>>, pv: &mut Vec<Json>) {
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            pk@.len() == pv@.len(),
            pk@ == old(pk)@.take(pk@.len() as int),
            pv@ == old(pv)@.take(pv@.len() as int),
            pv@.len() <= old(pv)@.len(),
            old(pk)@.len() == old(pv)@.len(),
            unique(old(pk)@),
            forall|i: int| 0 <= i < old(pv)@.len() ==> wf(#[trigger] old(pv)@[i]),
            old(tk)@.len() == old(tv)@.len(),
            unique(old(tk)@),
            forall|i: int| 0 <= i < old(tv)@.len() ==> wf(#[trigger] old(tv)@[i]),
            tk@.len() == tv@.len(),
            unique(tk@),
            forall|i: int| pv@.len() <= i < old(pv)@.len() ==> {
                let k = old(pk)@[i]@;
                if #[trigger] old(pv)@[i] is Null {
                    !has_key(tk@, k)
                } else {
                    has_key(tk@, k) && merged(lookup(tk@, tv@, k).unwrap(), target_value(old(tk)@, old(tv)@, k), old(pv)@[i])
                }
            },
            forall|k: Seq<u8>| !has_key(old(pk)@.subrange(pk@.len() as int, old(pk)@.len() as int), k)
                ==> #[trigger] lookup(tk@, tv@, k) == lookup(old(tk)@, old(tv)@, k),
        decreases pv@.len()
    ))]
    while pv.len() > 0 {
        let (Some(value), Some(key)) = (pv.pop(), pk.pop()) else {
            proof! {
                assert(false);
            }
            return;
        };
        proof! {
            assert(key == old(pk)@[pv.len() as int] && value == old(pv)@[pv.len() as int]);
            lemma_keys_from(old(pk)@, pv.len() as int);
            assert(old(pk)@.subrange(pv.len() as int, old(pk)@.len() as int) =~= seq![key] + old(pk)@.subrange(pv.len() + 1, old(pk)@.len() as int));
            // The key is not among the members already applied.
            assert forall|i: int| pv.len() < i < old(pk)@.len() implies (#[trigger] old(pk)@[i])@ != key@ by {
                assert(old(pk)@[pv.len() as int]@ != old(pk)@[i]@);
            }
            // So the target's members still hold their original value for it.
            if !has_key(old(pk)@.subrange(pv.len() + 1, old(pk)@.len() as int), key@) {
                assert(lookup(tk@, tv@, key@) == lookup(old(tk)@, old(tv)@, key@));
            } else {
                let i = choose|i: int| 0 <= i < old(pk)@.len() - (pv.len() + 1)
                    && (#[trigger] old(pk)@.subrange(pv.len() + 1, old(pk)@.len() as int)[i])@ == key@;
                assert(old(pk)@.subrange(pv.len() + 1, old(pk)@.len() as int)[i] == old(pk)@[pv.len() + 1 + i]);
            }
        }
        let found = find_key(tk.as_slice(), key.as_slice());
        if is_null(&value) {
            if let Some(j) = found {
                proof! {
                    lemma_remove(tk@, tv@, j as int);
                }
                tk.remove(j);
                tv.remove(j);
            }
        } else {
            let current = if let Some(j) = found {
                proof! {
                    lemma_lookup_at(tk@, tv@, j as int);
                    lemma_remove(tk@, tv@, j as int);
                }
                tk.remove(j);
                tv.remove(j)
            } else {
                Json::Null
            };
            proof! {
                assert(current == target_value(old(tk)@, old(tv)@, key@));
                lemma_wf_lookup(old(tk)@, old(tv)@, key@);
            }
            let result = merge_patch(current, value);
            proof! {
                lemma_push(tk@, tv@, key, result);
            }
            tk.push(key);
            tv.push(result);
        }
    }
    proof! {
        assert(pv@.len() == 0);
        assert(old(pk)@.subrange(0, old(pk)@.len() as int) =~= old(pk)@);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(text: &str) -> Json {
        Json::Str(text.as_bytes().to_vec())
    }

    fn obj(members: Vec<(&str, Json)>) -> Json {
        let (keys, values) = members.into_iter().map(|(k, v)| (k.as_bytes().to_vec(), v)).unzip();
        Json::Object(keys, values)
    }

    #[test]
    fn refuses_repeated_keys() {
        assert!(merge(obj(vec![("a", Json::Null), ("a", Json::Null)]), Json::Null).is_none());
        assert!(merge(Json::Null, obj(vec![("a", Json::Null), ("a", Json::Null)])).is_none());
    }

    #[test]
    fn merges_members() {
        let target = obj(vec![("a", s("b")), ("c", obj(vec![("d", s("e"))]))]);
        let patch = obj(vec![("a", Json::Null), ("c", obj(vec![("f", s("g"))]))]);
        let Some(Json::Object(keys, values)) = merge(target, patch) else { panic!("not an object") };
        assert_eq!(keys, vec![b"c".to_vec()]);
        let Json::Object(inner, _) = &values[0] else { panic!("not an object") };
        assert_eq!(inner, &vec![b"d".to_vec(), b"f".to_vec()]);
    }
}
