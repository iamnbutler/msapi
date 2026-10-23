#!/usr/bin/env python3
"""Writes crates/msapi-core/src/names.rs: the lookup keys of the class,
world and region tables as byte literals, so Verus can see them.

Run from the repository root after editing a table:

    python3 scripts/name_keys.py && cargo fmt --all

`names::tests` checks the output against the tables, so a stale file fails
`cargo test`.
"""

import re
from pathlib import Path

SRC = Path("crates/msapi-core/src")
REGIONS = ["gms", "kms", "msea", "tms", "jms"]  # `Region::ALL` order; tag = position


def fold(s):
    return [ord(c.lower()) for c in s if c.isascii() and c.isalnum()]


def lower(s):
    return [b + 32 if 65 <= b <= 90 else b for b in s.encode()]


def classes():
    text = (SRC / "class.rs").read_text()
    return re.findall(r'row\(\s*"([^"]+)",\s*"([^"]+)"', text)


def worlds():
    text = (SRC / "world.rs").read_text()
    return re.findall(r'key: "([^"]+)",\s*name: "([^"]+)",\s*region: Region::(\w+)', text)


def entries(rows):
    """(key bytes, owner, comment) for each row's keys, dropping a key that
    repeats one of the same row."""
    out = []
    for owner, keys in enumerate(rows):
        seen = []
        for key, text in keys:
            if key not in seen:
                seen.append(key)
                out.append((key, owner, text))
    return out


def lit(key, mac):
    return f"{mac}[{', '.join(f'{b}u8' for b in key)}]"


def table(name, doc, owners, items):
    n = len(items)
    spec_keys = "\n".join(
        f"            {i} => {lit(k, 'seq!')},  // {t}" for i, (k, _, t) in enumerate(items[:-1])
    ) + f"\n            _ => {lit(items[-1][0], 'seq!')},  // {items[-1][2]}"
    spec_owners = "\n".join(
        f"            {i} => {o}," for i, (_, o, _) in enumerate(items[:-1])
    ) + f"\n            _ => {items[-1][1]},"
    exec_arms = "\n".join(
        f"            {i} => (&{lit(k, '')}, {o}),  // {t}" for i, (k, o, t) in enumerate(items[:-1])
    ) + f"\n            _ => (&{lit(items[-1][0], '')}, {items[-1][1]}),  // {items[-1][2]}"
    return f'''
/// {doc}
pub mod {name} {{
    #[cfg(feature = "verus")]
    use vstd::prelude::*;

    use crate::webauthn::bytes_eq;
    #[cfg(feature = "verus")]
    use crate::lookup::{{all_below, all_distinct, lemma_all_below, lemma_all_distinct}};

    /// How many keys there are.
    #[cfg_attr(feature = "verus", verus_verify)]
    pub const LEN: usize = {n};

    /// How many entries the keys name; every owner is below this.
    #[cfg_attr(feature = "verus", verus_verify)]
    pub const OWNERS: usize = {owners};

    #[cfg(feature = "verus")]
    verus! {{

    /// Key `i`, for `i < LEN`.
    pub open spec fn key(i: usize) -> Seq<u8> {{
        match i {{
{spec_keys}
        }}
    }}

    /// The entry key `i` names.
    pub open spec fn owner(i: usize) -> usize {{
        match i {{
{spec_owners}
        }}
    }}

    /// No two keys are equal, checked by evaluating every pair.
    pub proof fn lemma_distinct()
        ensures
            forall|i: usize, j: usize| i < LEN && j < LEN && i != j ==> #[trigger] key(i) != #[trigger] key(j),
            forall|i: usize| i < LEN ==> #[trigger] owner(i) < OWNERS,
    {{
        assert(all_distinct(|k: int| key(k as usize), LEN as int)) by (compute_only);
        lemma_all_distinct(|k: int| key(k as usize), LEN as int);
        assert(all_below(|k: int| owner(k as usize), LEN as int, OWNERS)) by (compute_only);
        lemma_all_below(|k: int| owner(k as usize), LEN as int, OWNERS);
        assert forall|i: usize, j: usize| i < LEN && j < LEN && i != j implies #[trigger] key(i) != #[trigger] key(j) by {{
            assert((|k: int| key(k as usize))(i as int) == key(i));
            assert((|k: int| key(k as usize))(j as int) == key(j));
        }}
        assert forall|i: usize| i < LEN implies #[trigger] owner(i) < OWNERS by {{
            assert((|k: int| owner(k as usize))(i as int) == owner(i));
        }}
    }}

    }} // verus!

    /// Key `i` and the entry it names.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires i < LEN,
        ensures r.0@ == key(i), r.1 == owner(i),
    ))]
    #[must_use]
    #[rustfmt::skip]
    pub fn entry(i: usize) -> (&'static [u8], usize) {{
        let r: (&'static [u8], usize) = match i {{
{exec_arms}
        }};
        proof! {{ assert(r.0@ =~= key(i)); }}
        r
    }}

    /// The entry key `q` names, if any. Since no two keys are equal, a key
    /// always finds its own entry.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {{
                Some(o) => o < OWNERS && exists|i: usize| i < LEN && #[trigger] key(i) == q@ && owner(i) == o,
                None => forall|i: usize| i < LEN ==> #[trigger] key(i) != q@,
            }},
            forall|i: usize| i < LEN && #[trigger] key(i) == q@ ==> r == Some(owner(i)),
    ))]
    #[must_use]
    pub fn find(q: &[u8]) -> Option<usize> {{
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                i <= LEN,
                forall|j: usize| j < i ==> #[trigger] key(j) != q@,
            decreases LEN - i
        ))]
        while i < LEN {{
            let (k, o) = entry(i);
            if bytes_eq(k, q) {{
                proof! {{
                    lemma_distinct();
                    assert(key(i) == q@);
                }}
                return Some(o);
            }}
            i += 1;
        }}
        None
    }}
}}
'''


TESTS = """
#[cfg(test)]
mod tests {
    use crate::ascii::{fold, lowercase};
    use crate::class::CLASSES;
    use crate::lookup::tagged_key;
    use crate::region::Region;
    use crate::world::WORLDS;

    /// Each row's keys in order, dropping one that repeats a key of the same row.
    fn expected(rows: impl Iterator<Item = Vec<Vec<u8>>>) -> Vec<(Vec<u8>, usize)> {
        let mut out = Vec::new();
        for (owner, keys) in rows.enumerate() {
            let mut seen: Vec<Vec<u8>> = Vec::new();
            for key in keys {
                if !seen.contains(&key) {
                    seen.push(key.clone());
                    out.push((key, owner));
                }
            }
        }
        out
    }

    fn actual(len: usize, entry: fn(usize) -> (&'static [u8], usize)) -> Vec<(Vec<u8>, usize)> {
        (0..len).map(entry).map(|(k, o)| (k.to_vec(), o)).collect()
    }

    #[test]
    fn class_keys_are_the_folded_ids_and_names() {
        let rows = CLASSES.iter().map(|c| vec![fold(c.id.as_bytes()), fold(c.name.as_bytes())]);
        assert_eq!(actual(super::class::LEN, super::class::entry), expected(rows), "run scripts/name_keys.py");
        assert_eq!(super::class::OWNERS, CLASSES.len());
    }

    #[test]
    fn world_keys_are_the_tagged_keys_and_names() {
        let rows = WORLDS.iter().map(|w| {
            vec![tagged_key(w.region as u8, w.key.as_bytes()), tagged_key(w.region as u8, w.name.as_bytes())]
        });
        assert_eq!(actual(super::world::LEN, super::world::entry), expected(rows), "run scripts/name_keys.py");
        assert_eq!(super::world::OWNERS, WORLDS.len());
    }

    #[test]
    fn region_keys_are_the_lowercased_names() {
        for (i, r) in Region::ALL.iter().enumerate() {
            assert_eq!(*r as usize, i, "a region's tag is its position in Region::ALL");
        }
        let rows = Region::ALL.iter().map(|r| vec![lowercase(r.as_str().as_bytes())]);
        assert_eq!(actual(super::region::LEN, super::region::entry), expected(rows), "run scripts/name_keys.py");
        assert_eq!(super::region::OWNERS, Region::ALL.len());
    }
}
"""


def main():
    cls = classes()
    wds = worlds()
    tags = {r.lower(): i for i, r in enumerate(REGIONS)}
    class_items = entries([[(fold(i), i), (fold(n), n)] for i, n in cls])
    world_items = entries(
        [
            [([tags[r.lower()], 255] + lower(k), f"{r.lower()} {k}"), ([tags[r.lower()], 255] + lower(n), f"{r.lower()} {n}")]
            for k, n, r in wds
        ]
    )
    region_items = entries([[(lower(r), r)] for r in REGIONS])
    out = f'''//! The lookup keys of the class, world and region tables, as byte literals
//! Verus can read. Generated by `scripts/name_keys.py` from `class.rs`,
//! `world.rs` and `region.rs`; do not edit by hand.
//!
//! Each table's keys are pairwise distinct (`lemma_distinct`, checked by
//! evaluation), so its `find` returns the entry a key names and never a
//! different one. The tests check that these keys are exactly the folded or
//! tagged names of the tables they come from.
{table("class", "Each class's folded ID and folded name (a name folding to its ID once) → position in `CLASSES`.", len(cls), class_items)}{table("world", "Each world's tagged key and tagged name → position in `WORLDS`.", len(wds), world_items)}{table("region", "Each region's lowercased wire name → position in `Region::ALL`.", len(REGIONS), region_items)}'''
    (SRC / "names.rs").write_text(out + TESTS)


main()
