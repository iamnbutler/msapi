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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cbor<'a> {
    /// A non-negative integer.
    Uint(u64),
    /// A negative integer, `-1 - n`.
    Neg(u64),
    /// A byte string.
    Bytes(&'a [u8]),
    /// A text string.
    Text(&'a str),
    /// An array.
    Array(Vec<Cbor<'a>>),
    /// A map, in encoded order.
    Map(Vec<(Cbor<'a>, Cbor<'a>)>),
    /// `true` or `false`.
    Bool(bool),
    /// `null` or `undefined`.
    Null,
}

/// Deepest nesting accepted; COSE keys and attestation objects need three.
const MAX_DEPTH: u32 = 8;

impl<'a> Cbor<'a> {
    /// Decodes one item at the start of `data`. Returns it and the bytes after it.
    #[must_use]
    pub fn decode(data: &'a [u8]) -> Option<(Self, &'a [u8])> {
        let (item, end) = decode_at(data, 0, 0)?;
        Some((item, &data[end..]))
    }

    /// The value under integer key `key` of a map.
    #[must_use]
    pub fn get_int(&self, key: i64) -> Option<&Self> {
        let Self::Map(entries) = self else { return None };
        entries.iter().find(|(k, _)| k.as_int() == Some(key)).map(|(_, v)| v)
    }

    /// The value under text key `key` of a map.
    #[must_use]
    pub fn get_text(&self, key: &str) -> Option<&Self> {
        let Self::Map(entries) = self else { return None };
        entries.iter().find(|(k, _)| matches!(k, Self::Text(t) if *t == key)).map(|(_, v)| v)
    }

    /// An integer that fits an `i64`.
    #[must_use]
    pub fn as_int(&self) -> Option<i64> {
        match *self {
            Self::Uint(n) => i64::try_from(n).ok(),
            Self::Neg(n) => i64::try_from(n).ok().map(|n| -1 - n),
            _ => None,
        }
    }

    /// A byte string's bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> Option<&'a [u8]> {
        match *self {
            Self::Bytes(b) => Some(b),
            _ => None,
        }
    }
}

fn decode_at(data: &[u8], at: usize, depth: u32) -> Option<(Cbor<'_>, usize)> {
    if depth > MAX_DEPTH {
        return None;
    }
    let (major, arg, next) = cbor_head(data, at)?;
    let take = |len: u64| -> Option<(&[u8], usize)> {
        let len = usize::try_from(len).ok()?;
        let end = next.checked_add(len)?;
        Some((data.get(next..end)?, end))
    };
    // A count can claim more items than there are bytes; each item needs at
    // least one byte, so anything larger is malformed and refused up front.
    let count = |n: u64, per: usize| -> Option<usize> {
        let n = usize::try_from(n).ok()?;
        (n.checked_mul(per)? <= data.len() - next).then_some(n)
    };
    match major {
        0 => Some((Cbor::Uint(arg), next)),
        1 => Some((Cbor::Neg(arg), next)),
        2 => take(arg).map(|(b, end)| (Cbor::Bytes(b), end)),
        3 => take(arg).and_then(|(b, end)| Some((Cbor::Text(std::str::from_utf8(b).ok()?), end))),
        4 => {
            let n = count(arg, 1)?;
            let mut items = Vec::with_capacity(n);
            let mut at = next;
            for _ in 0..n {
                let (item, end) = decode_at(data, at, depth + 1)?;
                items.push(item);
                at = end;
            }
            Some((Cbor::Array(items), at))
        }
        5 => {
            let n = count(arg, 2)?;
            let mut entries = Vec::with_capacity(n);
            let mut at = next;
            for _ in 0..n {
                let (key, end) = decode_at(data, at, depth + 1)?;
                let (value, end) = decode_at(data, end, depth + 1)?;
                entries.push((key, value));
                at = end;
            }
            Some((Cbor::Map(entries), at))
        }
        7 => match arg {
            20 => Some((Cbor::Bool(false), next)),
            21 => Some((Cbor::Bool(true), next)),
            22 | 23 => Some((Cbor::Null, next)),
            _ => None,
        },
        _ => None,
    }
}

/// A credential public key, from its COSE encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PublicKey<'a> {
    /// ES256: ECDSA on P-256 with SHA-256. The uncompressed point is `04 ‖ x ‖ y`.
    Es256 {
        /// The x coordinate, 32 bytes.
        x: &'a [u8],
        /// The y coordinate, 32 bytes.
        y: &'a [u8],
    },
    /// `EdDSA` with Ed25519.
    Ed25519 {
        /// The 32-byte public key.
        x: &'a [u8],
    },
    /// RS256: RSASSA-PKCS1-v1_5 with SHA-256.
    Rs256 {
        /// The modulus.
        n: &'a [u8],
        /// The exponent.
        e: &'a [u8],
    },
}

/// COSE algorithm numbers this server accepts, in order of preference.
pub const ALGORITHMS: [i64; 3] = [-8, -7, -257];

impl<'a> PublicKey<'a> {
    /// Reads a COSE key. `None` for any key type or algorithm not in
    /// [`ALGORITHMS`], or a malformed one.
    #[must_use]
    pub fn from_cose(key: &Cbor<'a>) -> Option<Self> {
        let kty = key.get_int(1)?.as_int()?;
        let alg = key.get_int(3)?.as_int()?;
        let bytes = |label| key.get_int(label).and_then(Cbor::as_bytes);
        match (kty, alg) {
            // EC2, ES256, curve P-256.
            (2, -7) if key.get_int(-1)?.as_int()? == 1 => {
                let (x, y) = (bytes(-2)?, bytes(-3)?);
                (x.len() == 32 && y.len() == 32).then_some(Self::Es256 { x, y })
            }
            // OKP, EdDSA, curve Ed25519.
            (1, -8) if key.get_int(-1)?.as_int()? == 6 => {
                let x = bytes(-2)?;
                (x.len() == 32).then_some(Self::Ed25519 { x })
            }
            // RSA, RS256.
            (3, -257) => Some(Self::Rs256 { n: bytes(-1)?, e: bytes(-2)? }),
            _ => None,
        }
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
        let (cbor, rest) = Cbor::decode(&key).unwrap();
        assert_eq!(rest, &[0xf6]);
        assert_eq!(PublicKey::from_cose(&cbor), Some(PublicKey::Es256 { x: &[0; 32], y: &[0x11; 32] }));
    }

    #[test]
    fn refuses_malformed_cbor() {
        assert_eq!(Cbor::decode(&[0x9b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]), None, "huge array");
        assert_eq!(Cbor::decode(&[0x62, 0xff, 0xfe]), None, "invalid UTF-8");
        assert_eq!(Cbor::decode(&[0x81; 20]), None, "too deep");
        assert_eq!(Cbor::decode(&[0xf9, 0, 0]), None, "float");
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
