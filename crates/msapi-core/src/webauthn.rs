//! The byte formats and rules of passkey (`WebAuthn`) sign-in, with no crypto
//! and no I/O.
//!
//! A passkey ceremony hands the server three binary things: CBOR (the
//! attestation object and the public key), the authenticator data, and a
//! signature. The server keeps the hashing and signature checks (`ring`); this
//! module decides where each field is and whether its values are acceptable.
//! The offset arithmetic and the acceptance rules are checked by Verus.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]
#![allow(
    clippy::cast_possible_wrap,
    clippy::collapsible_if,
    reason = "the u64 to i64 casts are guarded by `<= i64::MAX`; Verus does not take let chains"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Authenticator data flag: the user was present (touched the key).
#[cfg_attr(feature = "verus", verus_verify)]
pub const USER_PRESENT: u8 = 0x01;
/// Authenticator data flag: the user was verified (PIN, biometrics).
#[cfg_attr(feature = "verus", verus_verify)]
pub const USER_VERIFIED: u8 = 0x04;
/// Authenticator data flag: attested credential data follows the counter.
#[cfg_attr(feature = "verus", verus_verify)]
pub const ATTESTED: u8 = 0x40;
/// Authenticator data flag: extensions follow.
#[cfg_attr(feature = "verus", verus_verify)]
pub const EXTENSIONS: u8 = 0x80;

/// Where the fields of authenticator data are.
///
/// ```text
/// rpIdHash 32 | flags 1 | signCount 4 (BE) | [ aaguid 16 | idLen 2 (BE) | id | COSE key | ... ]
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthDataLayout {
    /// The flags byte.
    pub flags: u8,
    /// The signature counter.
    pub sign_count: u32,
    /// The credential ID is `data[id_start..id_end]`; empty without [`ATTESTED`].
    pub id_start: usize,
    /// End of the credential ID.
    pub id_end: usize,
}

#[cfg(feature = "verus")]
verus! {

/// Big-endian value of `data[at..at + n]`.
pub open spec fn be(data: Seq<u8>, at: int, n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { be(data, at, (n - 1) as nat) * 256 + data[at + n - 1] as nat }
}

} // verus!

/// Locates the fields of authenticator data. `None` if it is too short for
/// what its flags announce.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r.is_none() <==> (data@.len() < 37 || (data@[32] & ATTESTED != 0 && (data@.len() < 55
            || data@.len() < 55 + (data@[53] as int) * 256 + data@[54] as int))),
        r matches Some(l) ==> {
            &&& l.flags == data@[32]
            &&& l.sign_count as nat == be(data@, 33, 4)
            &&& l.id_start <= l.id_end <= data@.len()
            &&& (l.flags & ATTESTED == 0 ==> l.id_start == 37 && l.id_end == 37)
            &&& (l.flags & ATTESTED != 0 ==> l.id_start == 55
                    && l.id_end == 55 + (data@[53] as int) * 256 + data@[54] as int)
        },
))]
#[must_use]
pub fn auth_data_layout(data: &[u8]) -> Option<AuthDataLayout> {
    if data.len() < 37 {
        return None;
    }
    let flags = data[32];
    let sign_count = (((data[33] as u32 * 256 + data[34] as u32) * 256 + data[35] as u32) * 256) + data[36] as u32;
    proof! {
        reveal_with_fuel(be, 5);
    }
    if flags & ATTESTED == 0 {
        return Some(AuthDataLayout { flags, sign_count, id_start: 37, id_end: 37 });
    }
    if data.len() < 55 {
        return None;
    }
    let id_len = data[53] as usize * 256 + data[54] as usize;
    if data.len() - 55 < id_len {
        return None;
    }
    Some(AuthDataLayout { flags, sign_count, id_start: 55, id_end: 55 + id_len })
}

/// Whether a sign-in's signature counter is acceptable after `stored`.
///
/// Authenticators that keep no counter (most synced passkeys) always send 0.
/// Otherwise the counter must grow; a counter that does not is the sign of a
/// cloned authenticator, and the sign-in is refused.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == ((stored == 0 && received == 0) || received > stored)
))]
#[must_use]
pub const fn counter_ok(stored: u32, received: u32) -> bool {
    (stored == 0 && received == 0) || received > stored
}

/// Whether the flags allow a sign-in: the user must have been present.
/// Verification (PIN or biometrics) is requested but not required, so a
/// security key without a PIN still works.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (flags & USER_PRESENT != 0)))]
#[must_use]
pub const fn presence_ok(flags: u8) -> bool {
    flags & USER_PRESENT != 0
}

/// Whether the flags say the authenticator data carries a credential, as a
/// registration's must.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (flags & ATTESTED != 0)))]
#[must_use]
pub const fn attested(flags: u8) -> bool {
    flags & ATTESTED != 0
}

/// The head of a CBOR item at `data[at..]`: its major type (0-7), its
/// argument, and where its content starts. `None` for indefinite lengths,
/// reserved encodings, or a head that runs past the end.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some((major, arg, next)) ==> {
            &&& at < data@.len()
            &&& major == data@[at as int] >> 5
            &&& at < next <= data@.len()
            &&& (data@[at as int] & 31 < 24 ==> arg == (data@[at as int] & 31) as u64 && next == at + 1)
            &&& (data@[at as int] & 31 == 24 ==> arg as nat == be(data@, at + 1, 1) && next == at + 2)
            &&& (data@[at as int] & 31 == 25 ==> arg as nat == be(data@, at + 1, 2) && next == at + 3)
            &&& (data@[at as int] & 31 == 26 ==> arg as nat == be(data@, at + 1, 4) && next == at + 5)
            &&& (data@[at as int] & 31 == 27 ==> arg as nat == be(data@, at + 1, 8) && next == at + 9)
            &&& data@[at as int] & 31 < 28
        },
))]
#[must_use]
pub fn cbor_head(data: &[u8], at: usize) -> Option<(u8, u64, usize)> {
    if at >= data.len() {
        return None;
    }
    let initial = data[at];
    let major = initial >> 5;
    let info = initial & 31;
    if info < 24 {
        return Some((major, info as u64, at + 1));
    }
    if info >= 28 {
        return None;
    }
    let n: usize = if info == 24 {
        1
    } else if info == 25 {
        2
    } else if info == 26 {
        4
    } else {
        8
    };
    if data.len() - at - 1 < n {
        return None;
    }
    let mut arg: u64 = 0;
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= n,
            n <= 8,
            at + 1 + n <= data.len(),
            arg as nat == be(data@, at + 1, i as nat),
            (arg as nat) < pow256(i as nat),
        decreases n - i
    ))]
    while i < n {
        proof! {
            lemma_pow256_step(i as nat);
            assert((arg as nat) * 256 + (data@[at + 1 + i] as nat) < pow256(i as nat + 1)) by (nonlinear_arith)
                requires (arg as nat) < pow256(i as nat), pow256(i as nat + 1) == pow256(i as nat) * 256,
                    (data@[at + 1 + i] as nat) < 256;
            lemma_pow256_bound((i + 1) as nat);
        }
        arg = arg * 256 + data[at + 1 + i] as u64;
        i += 1;
    }
    Some((major, arg, at + 1 + n))
}

#[cfg(feature = "verus")]
verus! {

/// `256^n`.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { pow256((n - 1) as nat) * 256 }
}

proof fn lemma_pow256_step(n: nat)
    ensures pow256(n + 1) == pow256(n) * 256,
{
}

/// `256^n ≤ 2^64` up to eight bytes, so an eight-byte argument fits a `u64`.
proof fn lemma_pow256_bound(n: nat)
    requires n <= 8,
    ensures pow256(n) <= 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(pow256, 9);
}

} // verus!

/// A decoded CBOR item: the subset `WebAuthn` uses (no floats, tags or
/// indefinite lengths).
///
/// Strings are ranges into the decoded buffer rather than borrows of it, so
/// the decoder's bounds can be stated and proven; read them with
/// [`Cbor::as_bytes`]. Text is not checked for UTF-8: the server only ever
/// compares text keys against ASCII names.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug)]
pub enum Cbor {
    /// A non-negative integer.
    Uint(u64),
    /// A negative integer, `-1 - n`.
    Neg(u64),
    /// A byte string at `data[start..end]`.
    Bytes(usize, usize),
    /// A text string at `data[start..end]`.
    Text(usize, usize),
    /// An array.
    Array(Vec<Cbor>),
    /// A map in encoded order: keys at even positions, each followed by its
    /// value.
    Map(Vec<Cbor>),
    /// `true` or `false`.
    Bool(bool),
    /// `null` or `undefined`.
    Null,
}

/// Deepest nesting accepted; COSE keys and attestation objects need three.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_DEPTH: u32 = 8;

#[cfg(feature = "verus")]
verus! {

/// Every string range in `c` lies within `lo..hi`.
pub open spec fn within(c: Cbor, lo: int, hi: int) -> bool
    decreases c,
{
    match c {
        Cbor::Bytes(s, e) => lo <= s <= e <= hi,
        Cbor::Text(s, e) => lo <= s <= e <= hi,
        Cbor::Array(v) => forall|i: int| 0 <= i < v.len() ==> within(#[trigger] v@[i], lo, hi),
        Cbor::Map(v) => forall|i: int| 0 <= i < v.len() ==> within(#[trigger] v@[i], lo, hi),
        _ => true,
    }
}

/// `v` is the value of one of the entries of map `c`.
pub open spec fn entry_value(c: Cbor, v: Cbor) -> bool {
    match c {
        Cbor::Map(m) => exists|i: int| 0 <= i < m.len() && #[trigger] m@[i] == v,
        _ => false,
    }
}

/// A map's entries lie where the map does.
proof fn lemma_map_entry(m: Vec<Cbor>, i: int, lo: int, hi: int)
    requires within(Cbor::Map(m), lo, hi), 0 <= i < m.len(),
    ensures within(m@[i], lo, hi),
{
    // Verus unfolds `within` on a constructed map only once it is matched apart.
    if let Cbor::Map(v) = Cbor::Map(m) {
        assert(v == m);
        assert(within(v@[i], lo, hi));
    }
}

/// Each entry of a map is one of its entries.
proof fn lemma_map_value(m: Vec<Cbor>, i: int)
    requires 0 <= i < m.len(),
    ensures entry_value(Cbor::Map(m), m@[i]),
{
    if let Cbor::Map(v) = Cbor::Map(m) {
        assert(v == m);
        assert(v@[i] == m@[i]);
    }
}

/// A value found in a map lies where the map does.
proof fn lemma_within_value(c: Cbor, v: Cbor, lo: int, hi: int)
    requires within(c, lo, hi), entry_value(c, v),
    ensures within(v, lo, hi),
{
    if let Cbor::Map(m) = c {
        let i = choose|i: int| 0 <= i < m.len() && #[trigger] m@[i] == v;
        assert(within(m@[i], lo, hi));
    }
}

proof fn lemma_within_widen(c: Cbor, lo: int, hi: int, lo2: int, hi2: int)
    requires within(c, lo, hi), lo2 <= lo, hi <= hi2,
    ensures within(c, lo2, hi2),
    decreases c,
{
    match c {
        Cbor::Array(v) => {
            assert forall|i: int| 0 <= i < v.len() implies within(#[trigger] v@[i], lo2, hi2) by {
                lemma_within_widen(v@[i], lo, hi, lo2, hi2);
            }
        },
        Cbor::Map(v) => {
            assert forall|i: int| 0 <= i < v.len() implies within(#[trigger] v@[i], lo2, hi2) by {
                lemma_within_widen(v@[i], lo, hi, lo2, hi2);
            }
        },
        _ => {},
    }
}

} // verus!

/// A copy of `data[start..end]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires start <= end <= data@.len(),
    ensures r@ == data@.subrange(start as int, end as int)
))]
fn copy_range(data: &[u8], start: usize, end: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = start;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= i <= end <= data@.len(),
            out@ == data@.subrange(start as int, i as int),
        decreases end - i
    ))]
    while i < end {
        proof! {
            assert(data@.subrange(start as int, i + 1) =~= data@.subrange(start as int, i as int).push(data@[i as int]));
        }
        out.push(data[i]);
        i += 1;
    }
    out
}

/// Whether `data[start..end]` equals `key`, without copying it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires start <= end <= data@.len(),
    ensures r == (data@.subrange(start as int, end as int) == key@)
))]
fn range_eq(data: &[u8], start: usize, end: usize, key: &[u8]) -> bool {
    if end - start != key.len() {
        proof! {
            assert(data@.subrange(start as int, end as int).len() != key@.len());
        }
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= end <= data@.len(),
            end - start == key@.len(),
            i <= key@.len(),
            forall|j: int| 0 <= j < i ==> data@[start + j] == key@[j],
        decreases key@.len() - i
    ))]
    while i < key.len() {
        if data[start + i] != key[i] {
            proof! {
                assert(data@.subrange(start as int, end as int)[i as int] != key@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof! {
        assert(data@.subrange(start as int, end as int) =~= key@);
    }
    true
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Cbor {
    /// Decodes one item at the start of `data`. Returns it and where it ends.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some((item, end)) ==> 0 < end <= data@.len() && within(item, 0, end as int)
    ))]
    #[must_use]
    pub fn decode(data: &[u8]) -> Option<(Self, usize)> {
        decode_at(data, 0, 0)
    }

    /// The value under integer key `key` of a map.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(v) ==> entry_value(*self, *v)
    ))]
    #[must_use]
    pub fn get_int(&self, key: i64) -> Option<&Self> {
        let Self::Map(entries) = self else { return None };
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant i <= entries.len(), *self == Cbor::Map(*entries), entries@ == (*entries)@,
            decreases entries.len() - i
        ))]
        while i < entries.len() && entries.len() - i >= 2 {
            if let Some(k) = entries[i].as_int() {
                if k == key {
                    proof! {
                        lemma_map_value(*entries, i + 1);
                    }
                    return Some(&entries[i + 1]);
                }
            }
            i += 2;
        }
        None
    }

    /// The value under text key `key` of a map.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires within(*self, 0, data@.len() as int),
        ensures
            r matches Some(v) ==> entry_value(*self, *v)
    ))]
    #[must_use]
    pub fn get_text(&self, data: &[u8], key: &[u8]) -> Option<&Self> {
        let Self::Map(entries) = self else { return None };
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                i <= entries.len(),
                *self == Cbor::Map(*entries),
                within(*self, 0, data@.len() as int),
                entries@ == (*entries)@,
            decreases entries.len() - i
        ))]
        while i < entries.len() && entries.len() - i >= 2 {
            proof! {
                lemma_map_entry(*entries, i as int, 0, data@.len() as int);
            }
            if let Self::Text(start, end) = entries[i] {
                if range_eq(data, start, end, key) {
                    proof! {
                        lemma_map_value(*entries, i + 1);
                    }
                    return Some(&entries[i + 1]);
                }
            }
            i += 2;
        }
        None
    }

    /// An integer that fits an `i64`.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(n) ==> match *self {
                Cbor::Uint(u) => n as int == u as int,
                Cbor::Neg(u) => n as int == -1 - u as int,
                _ => false,
            }
    ))]
    #[must_use]
    pub const fn as_int(&self) -> Option<i64> {
        match *self {
            Self::Uint(n) if n <= i64::MAX as u64 => Some(n as i64),
            Self::Neg(n) if n <= i64::MAX as u64 => Some(-1 - n as i64),
            _ => None,
        }
    }

    /// A byte string's bytes, from the buffer it was decoded from.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires within(*self, 0, data@.len() as int),
        ensures
            r matches Some(b) ==> match *self { Cbor::Bytes(s, e) => b@ == data@.subrange(s as int, e as int), _ => false }
    ))]
    #[must_use]
    pub fn as_bytes(&self, data: &[u8]) -> Option<Vec<u8>> {
        match *self {
            Self::Bytes(start, end) => Some(copy_range(data, start, end)),
            _ => None,
        }
    }
}

/// Whether two byte strings are equal.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (a@ == b@)))]
#[must_use]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
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
    proof! {
        assert(a@ =~= b@);
    }
    true
}

/// Decodes the item at `data[at..]`, `depth` levels down.
///
/// A count can claim more items than there are bytes; each item takes at
/// least one byte, so anything larger is malformed and refused up front.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires depth <= MAX_DEPTH + 1,
    ensures
        r matches Some((item, end)) ==> at < end <= data@.len() && within(item, at as int, end as int),
    decreases MAX_DEPTH + 1 - depth
))]
fn decode_at(data: &[u8], at: usize, depth: u32) -> Option<(Cbor, usize)> {
    if depth > MAX_DEPTH {
        return None;
    }
    let (major, arg, next) = cbor_head(data, at)?;
    let room = (data.len() - next) as u64;
    if major == 0 {
        Some((Cbor::Uint(arg), next))
    } else if major == 1 {
        Some((Cbor::Neg(arg), next))
    } else if major == 2 || major == 3 {
        if arg > room {
            return None;
        }
        let end = next + arg as usize;
        let item = if major == 2 { Cbor::Bytes(next, end) } else { Cbor::Text(next, end) };
        Some((item, end))
    } else if major == 4 {
        if arg > room {
            return None;
        }
        let n = arg as usize;
        let mut items: Vec<Cbor> = Vec::new();
        let mut pos = next;
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                depth <= MAX_DEPTH,
                at < next <= pos <= data@.len(),
                i <= n,
                items@.len() == i,
                forall|j: int| 0 <= j < i ==> within(#[trigger] items@[j], at as int, pos as int),
            decreases n - i
        ))]
        while i < n {
            let (item, end) = decode_at(data, pos, depth + 1)?;
            proof! {
                lemma_within_widen(item, pos as int, end as int, at as int, end as int);
                assert forall|j: int| 0 <= j < i implies within(#[trigger] items@[j], at as int, end as int) by {
                    lemma_within_widen(items@[j], at as int, pos as int, at as int, end as int);
                }
            }
            items.push(item);
            pos = end;
            i += 1;
        }
        let r = Cbor::Array(items);
        proof! {
            assert(within(r, at as int, pos as int));
        }
        Some((r, pos))
    } else if major == 5 {
        if arg > room / 2 {
            return None;
        }
        let n = arg as usize;
        let mut entries: Vec<Cbor> = Vec::new();
        let mut pos = next;
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                depth <= MAX_DEPTH,
                at < next <= pos <= data@.len(),
                i <= n,
                entries@.len() == 2 * i,
                forall|j: int| 0 <= j < 2 * i ==> within(#[trigger] entries@[j], at as int, pos as int),
            decreases n - i
        ))]
        while i < n {
            let (key, mid) = decode_at(data, pos, depth + 1)?;
            let (value, end) = decode_at(data, mid, depth + 1)?;
            proof! {
                lemma_within_widen(key, pos as int, mid as int, at as int, end as int);
                lemma_within_widen(value, mid as int, end as int, at as int, end as int);
                assert forall|j: int| 0 <= j < 2 * i implies within(#[trigger] entries@[j], at as int, end as int) by {
                    lemma_within_widen(entries@[j], at as int, pos as int, at as int, end as int);
                }
            }
            entries.push(key);
            entries.push(value);
            pos = end;
            i += 1;
        }
        let r = Cbor::Map(entries);
        proof! {
            assert(within(r, at as int, pos as int));
        }
        Some((r, pos))
    } else if major == 7 {
        if arg == 20 {
            Some((Cbor::Bool(false), next))
        } else if arg == 21 {
            Some((Cbor::Bool(true), next))
        } else if arg == 22 || arg == 23 {
            Some((Cbor::Null, next))
        } else {
            None
        }
    } else {
        None
    }
}

/// A credential public key, from its COSE encoding.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub enum PublicKey {
    /// ES256: ECDSA on P-256 with SHA-256. The uncompressed point is `04 ‖ x ‖ y`.
    Es256 {
        /// The x coordinate, 32 bytes.
        x: Vec<u8>,
        /// The y coordinate, 32 bytes.
        y: Vec<u8>,
    },
    /// `EdDSA` with Ed25519.
    Ed25519 {
        /// The 32-byte public key.
        x: Vec<u8>,
    },
    /// RS256: RSASSA-PKCS1-v1_5 with SHA-256.
    Rs256 {
        /// The modulus.
        n: Vec<u8>,
        /// The exponent.
        e: Vec<u8>,
    },
}

/// The client data's origin check: exactly this site's origin, and not
/// relayed from another site's frame.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (origin@ == expected@ && !cross_origin)))]
#[must_use]
pub fn origin_ok(origin: &[u8], expected: &[u8], cross_origin: bool) -> bool {
    bytes_eq(origin, expected) && !cross_origin
}

/// Whether authenticator data starts with `rp_id_hash`, the SHA-256 of this
/// site's relying-party ID.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == (auth_data@.len() >= rp_id_hash@.len() && auth_data@.take(rp_id_hash@.len() as int) == rp_id_hash@)
))]
#[must_use]
pub fn rp_id_hash_ok(auth_data: &[u8], rp_id_hash: &[u8]) -> bool {
    if auth_data.len() < rp_id_hash.len() {
        return false;
    }
    let r = range_eq(auth_data, 0, rp_id_hash.len(), rp_id_hash);
    proof! {
        assert(auth_data@.subrange(0, rp_id_hash@.len() as int) =~= auth_data@.take(rp_id_hash@.len() as int));
    }
    r
}

/// The uncompressed P-256 point `04 ‖ x ‖ y`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == seq![4u8] + x@ + y@))]
#[must_use]
pub fn es256_point(x: &[u8], y: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    out.push(4);
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant i <= x@.len(), out@ == seq![4u8] + x@.take(i as int),
        decreases x@.len() - i
    ))]
    while i < x.len() {
        proof! {
            assert(x@.take(i + 1) =~= x@.take(i as int).push(x@[i as int]));
        }
        out.push(x[i]);
        i += 1;
    }
    let mut j: usize = 0;
    proof! {
        assert(x@.take(x@.len() as int) =~= x@);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant j <= y@.len(), out@ == seq![4u8] + x@ + y@.take(j as int),
        decreases y@.len() - j
    ))]
    while j < y.len() {
        proof! {
            assert(y@.take(j + 1) =~= y@.take(j as int).push(y@[j as int]));
        }
        out.push(y[j]);
        j += 1;
    }
    proof! {
        assert(y@.take(y@.len() as int) =~= y@);
        assert(out@ =~= seq![4u8] + x@ + y@);
    }
    out
}

/// COSE algorithm numbers this server accepts, in order of preference.
pub const ALGORITHMS: [i64; 3] = [-8, -7, -257];

#[cfg_attr(feature = "verus", verus_verify)]
impl PublicKey {
    /// Reads a COSE key decoded from `data`. `None` for any key type or
    /// algorithm not in [`ALGORITHMS`], or a malformed one.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires within(*key, 0, data@.len() as int),
        ensures
            r matches Some(PublicKey::Es256 { x, y }) ==> x@.len() == 32 && y@.len() == 32,
            r matches Some(PublicKey::Ed25519 { x }) ==> x@.len() == 32,
    ))]
    #[must_use]
    pub fn from_cose(key: &Cbor, data: &[u8]) -> Option<Self> {
        let (Some(kty), Some(alg)) = (int_at(key, 1), int_at(key, 3)) else { return None };
        if kty == 2 && alg == -7 {
            // EC2, ES256, curve P-256.
            if int_at(key, -1) != Some(1) {
                return None;
            }
            let (Some(x), Some(y)) = (bytes_at(key, data, -2), bytes_at(key, data, -3)) else { return None };
            if x.len() == 32 && y.len() == 32 { Some(Self::Es256 { x, y }) } else { None }
        } else if kty == 1 && alg == -8 {
            // OKP, EdDSA, curve Ed25519.
            if int_at(key, -1) != Some(6) {
                return None;
            }
            let x = bytes_at(key, data, -2)?;
            if x.len() == 32 { Some(Self::Ed25519 { x }) } else { None }
        } else if kty == 3 && alg == -257 {
            // RSA, RS256.
            let (Some(n), Some(e)) = (bytes_at(key, data, -1), bytes_at(key, data, -2)) else { return None };
            Some(Self::Rs256 { n, e })
        } else {
            None
        }
    }
}

/// The integer under `label` in a COSE map.
#[cfg_attr(feature = "verus", verus_verify)]
fn int_at(key: &Cbor, label: i64) -> Option<i64> {
    match key.get_int(label) {
        Some(v) => v.as_int(),
        None => None,
    }
}

/// The byte string under `label` in a COSE map decoded from `data`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(requires within(*key, 0, data@.len() as int)))]
fn bytes_at(key: &Cbor, data: &[u8], label: i64) -> Option<Vec<u8>> {
    match key.get_int(label) {
        Some(v) => {
            proof! {
                lemma_within_value(*key, *v, 0, data@.len() as int);
            }
            v.as_bytes(data)
        }
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn heads_decode_every_width() {
        assert_eq!(cbor_head(&[0x17], 0), Some((0, 23, 1)));
        assert_eq!(cbor_head(&[0x18, 0xff], 0), Some((0, 255, 2)));
        assert_eq!(cbor_head(&[0x39, 0x01, 0x00], 0), Some((1, 256, 3)));
        assert_eq!(cbor_head(&[0x5a, 0, 1, 0, 0], 0), Some((2, 65_536, 5)));
        assert_eq!(cbor_head(&[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], 0), Some((0, u64::MAX, 9)));
        assert_eq!(cbor_head(&[0x1b, 0xff], 0), None);
        assert_eq!(cbor_head(&[0x5f], 0), None, "indefinite length");
        assert_eq!(cbor_head(&[], 0), None);
    }

    #[test]
    fn decodes_a_cose_key() {
        // {1: 2, 3: -7, -1: 1, -2: h'00…', -3: h'11…'}
        let mut key = vec![0xa5, 0x01, 0x02, 0x03, 0x26, 0x20, 0x01, 0x21, 0x58, 0x20];
        key.extend([0u8; 32]);
        key.extend([0x22, 0x58, 0x20]);
        key.extend([0x11u8; 32]);
        key.push(0xf6); // trailing item
        let (cbor, end) = Cbor::decode(&key).unwrap();
        assert_eq!(&key[end..], &[0xf6]);
        assert_eq!(PublicKey::from_cose(&cbor, &key), Some(PublicKey::Es256 { x: vec![0; 32], y: vec![0x11; 32] }));
    }

    #[test]
    fn refuses_malformed_cbor() {
        assert!(Cbor::decode(&[0x9b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).is_none(), "huge array");
        assert!(Cbor::decode(&[0x43, 0, 0]).is_none(), "string past the end");
        assert!(Cbor::decode(&[0xa2, 0x01, 0x02]).is_none(), "map claims more entries than bytes");
        assert!(Cbor::decode(&[0x81; 20]).is_none(), "too deep");
        assert!(Cbor::decode(&[0xf9, 0, 0]).is_none(), "float");
    }

    #[test]
    fn auth_data_layouts() {
        let mut data = vec![0u8; 37];
        data[32] = USER_PRESENT;
        data[33..37].copy_from_slice(&7u32.to_be_bytes());
        let l = auth_data_layout(&data).unwrap();
        assert_eq!((l.flags, l.sign_count, l.id_start, l.id_end), (USER_PRESENT, 7, 37, 37));

        data[32] |= ATTESTED;
        assert_eq!(auth_data_layout(&data), None, "announces a credential it lacks");
        data.extend([0u8; 16]);
        data.extend([0, 3, 9, 9, 9]);
        let l = auth_data_layout(&data).unwrap();
        assert_eq!(&data[l.id_start..l.id_end], &[9, 9, 9]);
        data.pop();
        assert_eq!(auth_data_layout(&data), None);
    }

    #[test]
    fn counters() {
        assert!(counter_ok(0, 0));
        assert!(counter_ok(5, 6));
        assert!(!counter_ok(5, 5));
        assert!(!counter_ok(5, 0));
    }
}
