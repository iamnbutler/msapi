#!/usr/bin/env python3
"""Writes crates/msapi-core/src/names.rs: the names of the class, world and
region tables as byte literals Verus can read, with a proof that names of
different entries never share a lookup key.

Run from the repository root after editing a table:

    python3 scripts/name_keys.py && cargo fmt --all

`class.rs`, `world.rs` and `region.rs` each check at compile time that their
table's names are byte for byte the texts here, so a stale file fails the
build.
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


def lit(key, mac):
    return f"{mac}[{', '.join(f'{b}u8' for b in key)}]"


def arms(values, fmt, note=lambda v: None):
    """Match arms for `values`, the last one as the catch-all."""

    def arm(pat, v):
        n = note(v)
        return f"            {pat} => {fmt(v)}," + (f"  // {n}" if n is not None else "")

    lines = [arm(i, v) for i, v in enumerate(values[:-1])]
    lines.append(arm("_", values[-1]))
    return "\n".join(lines)


def table(name, doc, group, texts, keys, spec_key, exec_key, exec_use, spec_use, tags=None):
    n = len(texts)
    raw_arms = arms(texts, lambda t: lit(t.encode(), "seq!"), lambda t: t)
    lit_arms = arms(keys, lambda k: lit(k, "seq!"))
    text_arms = arms(texts, lambda t: f"&{lit(t.encode(), '')}", lambda t: t)
    tag_spec = tag_exec = ""
    if tags is not None:
        tag_spec = f'''
    /// The tag of entry `o`: its region's position in `Region::ALL`.
    pub open spec fn tag_of(o: usize) -> u8 {{
        match o {{
{arms(tags, str)}
        }}
    }}
'''
        tag_exec = f'''
    /// The tag of entry `o`.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == tag_of(o)))]
    #[must_use]
    pub const fn tag(o: usize) -> u8 {{
        match o {{
{arms(tags, str)}
        }}
    }}
'''
    return f'''
/// {doc}
pub mod {name} {{
    #[cfg(feature = "verus")]
    use vstd::prelude::*;

    #[cfg(feature = "verus")]
    use {spec_use};
    use {exec_use};
    #[cfg(feature = "verus")]
    use crate::lookup::{{all_distinct, lemma_all_distinct}};
    use crate::webauthn::bytes_eq;

    /// How many texts there are.
    #[cfg_attr(feature = "verus", verus_verify)]
    pub const LEN: usize = {n};

    /// How many texts name each entry: text `i` names entry `i / GROUP`.
    #[cfg_attr(feature = "verus", verus_verify)]
    pub const GROUP: usize = {group};

    #[cfg(feature = "verus")]
    verus! {{

    /// Text `i`, for `i < LEN`.
    pub open spec fn raw(i: usize) -> Seq<u8> {{
        match i {{
{raw_arms}
        }}
    }}
{tag_spec}
    /// The lookup key of text `i`.
    pub open spec fn key(i: usize) -> Seq<u8> {{
        {spec_key}
    }}

    /// `key(i)`, written out by the generator.
    spec fn lit(i: usize) -> Seq<u8> {{
        match i {{
{lit_arms}
        }}
    }}

    /// `key` and `lit` agree below `n`.
    spec fn lits_match(n: int) -> bool
        decreases n,
    {{
        if n <= 0 {{ true }} else {{ key((n - 1) as usize) == lit((n - 1) as usize) && lits_match(n - 1) }}
    }}

    proof fn lemma_lits_match(n: int)
        requires lits_match(n),
        ensures forall|i: usize| (i as int) < n ==> #[trigger] key(i) == lit(i),
        decreases n,
    {{
        if n > 0 {{
            lemma_lits_match(n - 1);
        }}
    }}

    /// Texts of different entries have different keys, checked by
    /// evaluating every key and every pair.
    pub proof fn lemma_distinct()
        ensures
            forall|i: usize, j: usize| i < LEN && j < LEN && i / GROUP != j / GROUP ==> #[trigger] key(i) != #[trigger] key(j),
    {{
        assert(lits_match(LEN as int)) by (compute_only);
        lemma_lits_match(LEN as int);
        assert(all_distinct(|k: int| lit(k as usize), GROUP as int, LEN as int)) by (compute_only);
        lemma_all_distinct(|k: int| lit(k as usize), GROUP as int, LEN as int);
        assert forall|i: usize, j: usize| i < LEN && j < LEN && i / GROUP != j / GROUP implies #[trigger] key(i) != #[trigger] key(j) by {{
            assert((|k: int| lit(k as usize))(i as int) == lit(i));
            assert((|k: int| lit(k as usize))(j as int) == lit(j));
        }}
    }}

    }} // verus!

    /// Text `i`.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires i < LEN,
        ensures r@ == raw(i),
    ))]
    #[must_use]
    #[rustfmt::skip]
    pub const fn text(i: usize) -> &'static [u8] {{
        let r: &'static [u8] = match i {{
{text_arms}
        }};
        proof! {{ assert(r@ =~= raw(i)); }}
        r
    }}
{tag_exec}
    /// The entry one of whose texts has key `q`, if any. Texts of different
    /// entries never share a key, so this is the only such entry.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {{
                Some(o) => o < LEN / GROUP && exists|i: usize| i < LEN && #[trigger] key(i) == q@ && i / GROUP == o,
                None => forall|i: usize| i < LEN ==> #[trigger] key(i) != q@,
            }},
            forall|i: usize| i < LEN && #[trigger] key(i) == q@ ==> r == Some(i / GROUP),
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
            let k = {exec_key};
            if bytes_eq(&k, q) {{
                proof! {{
                    lemma_distinct();
                    assert(key(i) == q@);
                }}
                return Some(i / GROUP);
            }}
            i += 1;
        }}
        None
    }}
}}
'''


HEADER = '''//! The names of the class, world and region tables as byte literals Verus
//! can read. Generated by `scripts/name_keys.py` from `class.rs`, `world.rs`
//! and `region.rs`; do not edit by hand. Each of those files checks at
//! compile time that its table's names are exactly these texts.
//!
//! In each table, texts of different entries have different lookup keys
//! (`lemma_distinct`, checked by evaluation), so its `find` returns the entry
//! a key names and never a different one.
#![allow(
    clippy::too_many_lines,
    clippy::match_same_arms,
    reason = "generated tables: one match arm per text or entry"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Whether `a` and `b` are the same bytes; usable in constants.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (a@ == b@)))]
#[must_use]
pub const fn same(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    ))]
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof! { assert(a@ =~= b@); }
    true
}
'''


def main():
    cls = classes()
    wds = worlds()
    tags = [REGIONS.index(r.lower()) for _, _, r in wds]
    class_texts = [t for row in cls for t in row]
    world_texts = [t for k, n, _ in wds for t in (k, n)]
    out = HEADER
    out += table(
        "class",
        "Each class's ID and name, in `CLASSES` order; keys are folded.",
        2,
        class_texts,
        [fold(t) for t in class_texts],
        "folded(raw(i))",
        "fold(text(i))",
        "crate::ascii::fold",
        "crate::ascii::folded",
    )
    out += table(
        "world",
        "Each world's key and name, in `WORLDS` order; keys are tagged with the world's region.",
        2,
        world_texts,
        [[tags[i // 2], 255] + lower(t) for i, t in enumerate(world_texts)],
        "tagged(tag_of(i / GROUP), raw(i))",
        "tagged_key(tag(i / GROUP), text(i))",
        "crate::lookup::tagged_key",
        "crate::lookup::tagged",
        tags,
    )
    out += table(
        "region",
        "Each region's wire name, in `Region::ALL` order; keys are lowercased.",
        1,
        REGIONS,
        [lower(t) for t in REGIONS],
        "lowered(raw(i))",
        "lowercase(text(i))",
        "crate::ascii::lowercase",
        "crate::ascii::lowered",
    )
    (SRC / "names.rs").write_text(out)


main()
