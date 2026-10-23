//! Reading the HTTP/1.1 responses of the changeset log: where the head ends,
//! the status code, whether the body is chunked, and the chunked body's
//! data. Verus checks each against a spec written step by step.
//!
//! The specs are those of the code this replaced, which used the standard
//! library: the head must be UTF-8 (`str::from_utf8`), the status is the
//! second space-separated field parsed as a `u16`, the body is chunked when a
//! header line starts with `transfer-encoding:` in any case and contains
//! `chunked`, and each chunk size is the text before any `;`, trimmed and
//! parsed with `usize::from_str_radix(_, 16)`.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]
#![allow(
    clippy::manual_range_contains,
    clippy::many_single_char_names,
    reason = "Verus has no spec for `RangeInclusive::contains`; s, i, v, lo, hi name the spec's terms"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::query::find;
use crate::text::{parse_hex_in, parse_u64_in, trim_in};
#[cfg(feature = "verus")]
use crate::text::{parse_hex_spec, parse_u64_spec, trimmed};

#[cfg(feature = "verus")]
verus! {

/// Whether `b` is a UTF-8 continuation byte in `lo..=hi`.
pub open spec fn cont(b: u8, lo: u8, hi: u8) -> bool {
    lo <= b && b <= hi
}

/// The length of the well-formed UTF-8 character `s` starts with, or 0
/// (Unicode Table 3-7).
pub open spec fn utf8_char(s: Seq<u8>) -> nat {
    let n = s.len();
    if n == 0 {
        0
    } else if s[0] <= 0x7F {
        1
    } else if 0xC2 <= s[0] <= 0xDF {
        if n >= 2 && cont(s[1], 0x80, 0xBF) { 2 } else { 0 }
    } else if s[0] == 0xE0 {
        if n >= 3 && cont(s[1], 0xA0, 0xBF) && cont(s[2], 0x80, 0xBF) { 3 } else { 0 }
    } else if (0xE1 <= s[0] <= 0xEC) || s[0] == 0xEE || s[0] == 0xEF {
        if n >= 3 && cont(s[1], 0x80, 0xBF) && cont(s[2], 0x80, 0xBF) { 3 } else { 0 }
    } else if s[0] == 0xED {
        if n >= 3 && cont(s[1], 0x80, 0x9F) && cont(s[2], 0x80, 0xBF) { 3 } else { 0 }
    } else if s[0] == 0xF0 {
        if n >= 4 && cont(s[1], 0x90, 0xBF) && cont(s[2], 0x80, 0xBF) && cont(s[3], 0x80, 0xBF) { 4 } else { 0 }
    } else if 0xF1 <= s[0] <= 0xF3 {
        if n >= 4 && cont(s[1], 0x80, 0xBF) && cont(s[2], 0x80, 0xBF) && cont(s[3], 0x80, 0xBF) { 4 } else { 0 }
    } else if s[0] == 0xF4 {
        if n >= 4 && cont(s[1], 0x80, 0x8F) && cont(s[2], 0x80, 0xBF) && cont(s[3], 0x80, 0xBF) { 4 } else { 0 }
    } else {
        0
    }
}

/// `s` is well-formed UTF-8: `str::from_utf8(s).is_ok()`.
pub open spec fn utf8(s: Seq<u8>) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let k = utf8_char(s);
        k > 0 && k <= s.len() && utf8(s.skip(k as int))
    }
}

/// Where `\r\n\r\n` first starts in `s`, if anywhere.
pub open spec fn head_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if i + 4 > s.len() {
        None
    } else if s[i] == 13 && s[i + 1] == 10 && s[i + 2] == 13 && s[i + 3] == 10 {
        Some(i)
    } else {
        head_end(s, i + 1)
    }
}

/// Where `\r\n` first starts in `s[i..]`, if anywhere.
pub open spec fn line_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if i + 2 > s.len() {
        None
    } else if s[i] == 13 && s[i + 1] == 10 {
        Some(i)
    } else {
        line_end(s, i + 1)
    }
}

/// The status code in the head `h[..e]`: the second space-separated field.
pub open spec fn status_spec(h: Seq<u8>, e: int) -> Option<u16> {
    let a = find(h, 0, e, 32);
    if a >= e {
        None
    } else {
        let b = find(h, a + 1, e, 32);
        match parse_u64_spec(h.subrange(a + 1, b)) {
            Some(n) => if n <= 65535 { Some(n as u16) } else { None },
            None => None,
        }
    }
}

/// `b` lowercased if it is an ASCII capital.
pub open spec fn lower(b: u8) -> u8 {
    if 65 <= b <= 90 { (b + 32) as u8 } else { b }
}

/// `transfer-encoding:`.
pub open spec fn te() -> Seq<u8> {
    seq![116u8, 114u8, 97u8, 110u8, 115u8, 102u8, 101u8, 114u8, 45u8, 101u8, 110u8, 99u8, 111u8, 100u8, 105u8, 110u8, 103u8, 58u8]
}

/// `chunked`.
pub open spec fn chunked_word() -> Seq<u8> {
    seq![99u8, 104u8, 117u8, 110u8, 107u8, 101u8, 100u8]
}

/// The line `h[lo..hi]` starts with `transfer-encoding:` in any case.
pub open spec fn te_line(h: Seq<u8>, lo: int, hi: int) -> bool {
    hi - lo >= 18 && forall|k: int| 0 <= k < 18 ==> lower(#[trigger] h[lo + k]) == te()[k]
}

/// `chunked` occurs in `h[lo..hi]`.
pub open spec fn has_chunked(h: Seq<u8>, lo: int, hi: int) -> bool {
    exists|k: int| lo <= k && k + 7 <= hi && #[trigger] h.subrange(k, k + 7) == chunked_word()
}

/// Some `\n`-separated line of the head `h[..e]` from position `i` on
/// announces a chunked body.
pub open spec fn chunked_from(h: Seq<u8>, i: int, e: int) -> bool
    decreases e - i,
{
    if i < 0 || i > e {
        false
    } else {
        let f = find(h, i, e, 10);
        (te_line(h, i, f) && has_chunked(h, i, f)) || (i <= f < e && chunked_from(h, f + 1, e))
    }
}

/// A response's parts: `(status, body start, chunked)`.
pub open spec fn response_spec(r: Seq<u8>) -> Option<(u16, int, bool)> {
    match head_end(r, 0) {
        None => None,
        Some(e) => {
            if !utf8(r.subrange(0, e)) {
                None
            } else {
                match status_spec(r, e) {
                    None => None,
                    Some(s) => Some((s, e + 4, chunked_from(r, 0, e))),
                }
            }
        },
    }
}

/// The chunk size the size line `l[lo..hi]` gives: the text before any `;`,
/// trimmed, in hex.
pub open spec fn size_spec(l: Seq<u8>, lo: int, hi: int) -> Option<usize> {
    if !utf8(l.subrange(lo, hi)) {
        None
    } else {
        parse_hex_spec(trimmed(l.subrange(lo, find(l, lo, hi, 59))))
    }
}

/// The data of the chunked body that starts at `at` in `d`: each chunk is a
/// size line, `\r\n`, that many bytes and two more; a size of 0 ends it.
pub open spec fn dechunk_at(d: Seq<u8>, at: int) -> Option<Seq<u8>>
    decreases d.len() - at,
{
    if at < 0 || at > d.len() {
        None
    } else {
        match line_end(d, at) {
            None => None,
            Some(e) => if e < at || e + 2 > d.len() {
                None
            } else {
                match size_spec(d, at, e) {
                    None => None,
                    Some(n) => {
                        let b = e + 2;
                        if n == 0 {
                            Some(Seq::empty())
                        } else if d.len() - b < n + 2 {
                            None
                        } else {
                            match dechunk_at(d, b + n + 2) {
                                Some(t) => Some(d.subrange(b, b + n) + t),
                                None => None,
                            }
                        }
                    },
                }
            },
        }
    }
}

/// The data of a chunked body.
pub open spec fn dechunk_spec(d: Seq<u8>) -> Option<Seq<u8>> {
    dechunk_at(d, 0)
}

proof fn lemma_head_end(s: Seq<u8>, i: int)
    requires 0 <= i,
    ensures head_end(s, i) matches Some(e) ==> i <= e && e + 4 <= s.len(),
    decreases s.len() - i,
{
    if i + 4 <= s.len() && !(s[i] == 13 && s[i + 1] == 10 && s[i + 2] == 13 && s[i + 3] == 10) {
        lemma_head_end(s, i + 1);
    }
}

proof fn lemma_line_end(s: Seq<u8>, i: int)
    requires 0 <= i,
    ensures line_end(s, i) matches Some(e) ==> i <= e && e + 2 <= s.len(),
    decreases s.len() - i,
{
    if i + 2 <= s.len() && !(s[i] == 13 && s[i + 1] == 10) {
        lemma_line_end(s, i + 1);
    }
}

proof fn lemma_find(q: Seq<u8>, i: int, e: int, x: u8)
    requires i <= e,
    ensures i <= find(q, i, e, x) <= e,
    decreases e - i,
{
    if i < e && q[i] != x {
        lemma_find(q, i + 1, e, x);
    }
}

} // verus!

/// Whether `s[j]` is in `lo..=hi`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires j < s.len(),
    ensures r == cont(s@[j as int], lo, hi),
))]
fn cont_at(s: &[u8], j: usize, lo: u8, hi: u8) -> bool {
    lo <= s[j] && s[j] <= hi
}

/// The length of the well-formed UTF-8 character at `s[i..hi]`, or 0.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i <= hi <= s.len(),
    ensures r as nat == utf8_char(s@.subrange(i as int, hi as int)),
))]
fn char_at(s: &[u8], i: usize, hi: usize) -> usize {
    let n = hi - i;
    if n == 0 {
        return 0;
    }
    let b = s[i];
    if b <= 0x7F {
        1
    } else if 0xC2 <= b && b <= 0xDF {
        if n >= 2 && cont_at(s, i + 1, 0x80, 0xBF) { 2 } else { 0 }
    } else if b == 0xE0 {
        if n >= 3 && cont_at(s, i + 1, 0xA0, 0xBF) && cont_at(s, i + 2, 0x80, 0xBF) { 3 } else { 0 }
    } else if (0xE1 <= b && b <= 0xEC) || b == 0xEE || b == 0xEF {
        if n >= 3 && cont_at(s, i + 1, 0x80, 0xBF) && cont_at(s, i + 2, 0x80, 0xBF) { 3 } else { 0 }
    } else if b == 0xED {
        if n >= 3 && cont_at(s, i + 1, 0x80, 0x9F) && cont_at(s, i + 2, 0x80, 0xBF) { 3 } else { 0 }
    } else if b == 0xF0 {
        if n >= 4 && cont_at(s, i + 1, 0x90, 0xBF) && cont_at(s, i + 2, 0x80, 0xBF) && cont_at(s, i + 3, 0x80, 0xBF) {
            4
        } else {
            0
        }
    } else if 0xF1 <= b && b <= 0xF3 {
        if n >= 4 && cont_at(s, i + 1, 0x80, 0xBF) && cont_at(s, i + 2, 0x80, 0xBF) && cont_at(s, i + 3, 0x80, 0xBF) {
            4
        } else {
            0
        }
    } else if b == 0xF4 {
        if n >= 4 && cont_at(s, i + 1, 0x80, 0x8F) && cont_at(s, i + 2, 0x80, 0xBF) && cont_at(s, i + 3, 0x80, 0xBF) {
            4
        } else {
            0
        }
    } else {
        0
    }
}
/// Whether `s[lo..hi]` is well-formed UTF-8: `str::from_utf8(..).is_ok()`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires lo <= hi <= s.len(),
    ensures r == utf8(s@.subrange(lo as int, hi as int)),
))]
#[must_use]
pub fn is_utf8(s: &[u8], lo: usize, hi: usize) -> bool {
    let mut i = lo;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            lo <= i <= hi <= s.len(),
            utf8(s@.subrange(lo as int, hi as int)) == utf8(s@.subrange(i as int, hi as int)),
        decreases hi - i
    ))]
    while i < hi {
        let k = char_at(s, i, hi);
        if k == 0 {
            return false;
        }
        proof! {
            assert(s@.subrange(i as int, hi as int).skip(k as int) =~= s@.subrange(i + k, hi as int));
        }
        i += k;
    }
    true
}

/// Where `\r\n\r\n` first starts in `s`, if anywhere.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == match head_end(s@, 0) { Some(e) => Some(e as usize), None => None::<usize> }))]
fn find_head_end(s: &[u8]) -> Option<usize> {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant head_end(s@, 0) == head_end(s@, i as int),
        decreases s.len() - i
    ))]
    while i <= s.len() && s.len() - i >= 4 {
        if s[i] == 13 && s[i + 1] == 10 && s[i + 2] == 13 && s[i + 3] == 10 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Where `x` first occurs in `s[i..e]`, or `e`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i <= e <= s.len(),
    ensures r as int == find(s@, i as int, e as int, x),
))]
fn find_byte(s: &[u8], i: usize, e: usize, x: u8) -> usize {
    let mut j = i;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= j <= e <= s.len(),
            find(s@, i as int, e as int, x) == find(s@, j as int, e as int, x),
        decreases e - j
    ))]
    while j < e && s[j] != x {
        j += 1;
    }
    j
}

/// Where `\r\n` first starts in `s[from..]`, if anywhere.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == match line_end(s@, from as int) { Some(e) => Some(e as usize), None => None::<usize> },
))]
fn find_line_end(s: &[u8], from: usize) -> Option<usize> {
    let mut i: usize = from;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant line_end(s@, from as int) == line_end(s@, i as int),
        decreases s.len() - i
    ))]
    while i <= s.len() && s.len() - i >= 2 {
        if s[i] == 13 && s[i + 1] == 10 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// The status code in the head `h[..e]`: the second space-separated field.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires e <= h.len(),
    ensures r == status_spec(h@, e as int),
))]
fn status(h: &[u8], e: usize) -> Option<u16> {
    let a = find_byte(h, 0, e, 32);
    if a >= e {
        return None;
    }
    let b = find_byte(h, a + 1, e, 32);
    proof! { lemma_find(h@, a + 1, e as int, 32); }
    match parse_u64_in(h, a + 1, b) {
        Some(n) => {
            if n <= 65535 {
                Some(n as u16)
            } else {
                None
            }
        }
        None => None,
    }
}

/// Whether the line `h[lo..hi]` starts with `transfer-encoding:` in any case.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires lo <= hi <= h.len(),
    ensures r == te_line(h@, lo as int, hi as int),
))]
fn is_te_line(h: &[u8], lo: usize, hi: usize) -> bool {
    let want: [u8; 18] = [116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103, 58];
    proof! { assert(want@ =~= te()); }
    if hi - lo < 18 {
        return false;
    }
    let mut k: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            k <= 18, lo + 18 <= hi <= h.len(), want@ == te(),
            forall|j: int| 0 <= j < k ==> lower(#[trigger] h@[lo + j]) == te()[j],
        decreases 18 - k
    ))]
    while k < 18 {
        let b = h[lo + k];
        let lb = if 65 <= b && b <= 90 { b + 32 } else { b };
        if lb != want[k] {
            return false;
        }
        k += 1;
    }
    true
}

/// Whether `chunked` occurs in `h[lo..hi]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires lo <= hi <= h.len(),
    ensures r == has_chunked(h@, lo as int, hi as int),
))]
fn contains_chunked(h: &[u8], lo: usize, hi: usize) -> bool {
    let want: [u8; 7] = [99, 104, 117, 110, 107, 101, 100];
    proof! { assert(want@ =~= chunked_word()); }
    let mut k: usize = lo;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            lo <= k <= hi <= h.len(), want@ == chunked_word(),
            forall|j: int| lo <= j < k && j + 7 <= hi ==> #[trigger] h@.subrange(j, j + 7) != chunked_word(),
        decreases hi - k
    ))]
    while hi - k >= 7 {
        let mut m: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                m <= 7, k + 7 <= hi <= h.len(), want@ == chunked_word(),
                forall|j: int| 0 <= j < m ==> h@[k + j] == want@[j],
            decreases 7 - m
        ))]
        while m < 7 && h[k + m] == want[m] {
            m += 1;
        }
        if m == 7 {
            proof! { assert(h@.subrange(k as int, k + 7) =~= chunked_word()); }
            return true;
        }
        proof! { assert(h@.subrange(k as int, k + 7)[m as int] != chunked_word()[m as int]); }
        k += 1;
    }
    false
}

/// Whether some `\n`-separated line of the head `h[..e]` announces a chunked
/// body.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires e <= h.len(),
    ensures r == chunked_from(h@, 0, e as int),
))]
fn is_chunked(h: &[u8], e: usize) -> bool {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= e <= h.len(),
            chunked_from(h@, 0, e as int) == chunked_from(h@, i as int, e as int),
        decreases e - i
    ))]
    loop {
        let f = find_byte(h, i, e, 10);
        proof! { lemma_find(h@, i as int, e as int, 10); }
        if is_te_line(h, i, f) && contains_chunked(h, i, f) {
            return true;
        }
        if f >= e {
            return false;
        }
        i = f + 1;
    }
}

/// A response's parts: `(status, where the body starts, chunked)`; `None`
/// when the head does not end, is not UTF-8 or has no status.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some((s, b, c)) => response_spec(resp@) == Some((s, b as int, c)) && b <= resp.len(),
            None => response_spec(resp@) is None,
        },
))]
#[must_use]
pub fn response(resp: &[u8]) -> Option<(u16, usize, bool)> {
    proof! { lemma_head_end(resp@, 0); }
    let e = find_head_end(resp)?;
    if !is_utf8(resp, 0, e) {
        return None;
    }
    let s = status(resp, e)?;
    Some((s, e + 4, is_chunked(resp, e)))
}

/// Whether a status is a success (2xx).
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (200 <= status && status < 300)))]
#[must_use]
pub const fn success(status: u16) -> bool {
    200 <= status && status < 300
}

/// The chunk size the size line `l[lo..hi]` gives.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires lo <= hi <= l.len(),
    ensures r == size_spec(l@, lo as int, hi as int),
))]
fn size(l: &[u8], lo: usize, hi: usize) -> Option<usize> {
    if !is_utf8(l, lo, hi) {
        return None;
    }
    let semi = find_byte(l, lo, hi, 59);
    proof! { lemma_find(l@, lo as int, hi as int, 59); }
    let (a, b) = trim_in(l, lo, semi);
    parse_hex_in(l, a, b)
}

/// The data of a chunked body: [`dechunk_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some(v) => dechunk_spec(d@) == Some(v@),
            None => dechunk_spec(d@) is None,
        },
))]
#[must_use]
pub fn dechunk(d: &[u8]) -> Option<Vec<u8>> {
    let mut out: Vec<u8> = Vec::new();
    let mut at: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            at <= d.len(),
            dechunk_spec(d@) == match dechunk_at(d@, at as int) {
                Some(t) => Some(out@ + t),
                None => None::<Seq<u8>>,
            },
        decreases d.len() - at
    ))]
    loop {
        proof! { lemma_line_end(d@, at as int); }
        let e = find_line_end(d, at)?;
        let n = size(d, at, e)?;
        let body = e + 2;
        if n == 0 {
            proof! { assert(out@ + Seq::<u8>::empty() =~= out@); }
            return Some(out);
        }
        if d.len() - body < n || d.len() - body - n < 2 {
            return None;
        }
        let next = body + n + 2;
        #[allow(unused_variables, reason = "the proof names it")]
        let start = out.len();
        proof! {
            assert(out@.subrange(0, start as int) =~= out@);
            assert(out@.subrange(start as int, out@.len() as int) =~= d@.subrange(body as int, body as int));
        }
        let mut k: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                k <= n, next == body + n + 2, next <= d.len(), at < body,
                out@.len() == start + k,
                dechunk_spec(d@) == match dechunk_at(d@, at as int) {
                    Some(t) => Some(out@.subrange(0, start as int) + t),
                    None => None::<Seq<u8>>,
                },
                dechunk_at(d@, at as int) == match dechunk_at(d@, next as int) {
                    Some(t) => Some(d@.subrange(body as int, body + n) + t),
                    None => None::<Seq<u8>>,
                },
                out@.subrange(start as int, out@.len() as int) == d@.subrange(body as int, body + k),
            decreases n - k
        ))]
        while k < n {
            proof! {
                let o = out@;
                assert(o.push(d@[body + k]).subrange(0, start as int) =~= o.subrange(0, start as int));
                assert(o.push(d@[body + k]).subrange(start as int, o.len() as int + 1)
                    =~= o.subrange(start as int, o.len() as int).push(d@[body + k]));
                assert(d@.subrange(body as int, body + k + 1) =~= d@.subrange(body as int, body + k).push(d@[body + k]));
            }
            out.push(d[body + k]);
            k += 1;
        }
        proof! {
            let p = out@.subrange(0, start as int);
            let c = d@.subrange(body as int, body + n);
            assert(out@ =~= p + c);
            match dechunk_at(d@, next as int) {
                Some(t) => { assert(p + (c + t) =~= (p + c) + t); },
                None => {},
            }
        }
        at = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn old_dechunk(mut data: &[u8]) -> Option<Vec<u8>> {
        let mut out = Vec::new();
        loop {
            let line_end = data.windows(2).position(|w| w == b"\r\n")?;
            let size_text = std::str::from_utf8(&data[..line_end]).ok()?;
            let size = usize::from_str_radix(size_text.split(';').next().unwrap_or("").trim(), 16).ok()?;
            data = &data[line_end + 2..];
            if size == 0 {
                return Some(out);
            }
            out.extend_from_slice(data.get(..size)?);
            data = data.get(size + 2..)?;
        }
    }

    fn old_response(response: &[u8]) -> Option<(u16, usize, bool)> {
        let split = response.windows(4).position(|w| w == b"\r\n\r\n")?;
        let head = std::str::from_utf8(&response[..split]).ok()?;
        let status: u16 = head.split(' ').nth(1).and_then(|s| s.parse().ok())?;
        let chunked =
            head.lines().any(|l| l.to_ascii_lowercase().starts_with("transfer-encoding:") && l.contains("chunked"));
        Some((status, split + 4, chunked))
    }

    #[test]
    fn utf8_is_std() {
        for a in 0..=255u8 {
            assert_eq!(is_utf8(&[a], 0, 1), std::str::from_utf8(&[a]).is_ok());
            for b in 0..=255u8 {
                let s = [a, b];
                assert_eq!(is_utf8(&s, 0, 2), std::str::from_utf8(&s).is_ok(), "{s:?}");
                for c in [0x00, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xff] {
                    let s = [a, b, c];
                    assert_eq!(is_utf8(&s, 0, 3), std::str::from_utf8(&s).is_ok(), "{s:?}");
                    for d in [0x00, 0x80, 0xbf, 0xc0] {
                        let s = [a, b, c, d];
                        assert_eq!(is_utf8(&s, 0, 4), std::str::from_utf8(&s).is_ok(), "{s:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn matches_the_code_it_replaced() {
        let bodies: &[&[u8]] = &[
            b"5\r\nhello\r\n0\r\n\r\n",
            b"5;ext=1\r\nhello\r\n6\r\n world\r\n0\r\n\r\n",
            b" 5 \r\nhello\r\n0\r\n",
            b"+a\r\n0123456789xx0\r\n",
            b"5\r\nhel",
            b"5\r\nhelloX",
            b"zz\r\n",
            b"5;\xff\r\nhello\r\n0\r\n",
            b"\xc2\xa05\r\nhello\r\n0\r\n",
            b"",
            b"0",
            b"ffffffffffffffffff\r\n",
        ];
        for b in bodies {
            assert_eq!(dechunk(b), old_dechunk(b), "{:?}", String::from_utf8_lossy(b));
        }
        let responses: &[&[u8]] = &[
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nbody",
            b"HTTP/1.1 204 No Content\r\n\r\n",
            b"HTTP/1.1 500\r\nx: y\r\n\r\n",
            b"HTTP/1.1 +200 OK\r\n\r\n",
            b"HTTP/1.1 70000 OK\r\n\r\n",
            b"HTTP/1.1\r\n\r\n",
            b"HTTP/1.1 200 OK\r\nTRANSFER-ENCODING: gzip, chunked\r\n\r\n",
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: CHUNKED\r\n\r\n",
            b"HTTP/1.1 200 OK\r\nX-Transfer-Encoding: chunked\r\n\r\n",
            b"HTTP/1.1 200 OK\r\n\xff\r\n\r\n",
            b"no end",
        ];
        for r in responses {
            assert_eq!(response(r), old_response(r), "{:?}", String::from_utf8_lossy(r));
        }
        assert!(success(200) && success(299) && !success(300) && !success(199));
    }
}
