//! Random identifiers and token secrets.

use std::sync::{Mutex, PoisonError};

use ring::rand::{SecureRandom, SystemRandom};

use msapi_core::Timestamp;

const CROCKFORD: &[u8; 32] = b"0123456789abcdefghjkmnpqrstvwxyz";

/// `N` bytes from the OS random number generator.
///
/// # Panics
///
/// If the OS has no randomness to give.
#[must_use]
pub fn random<const N: usize>() -> [u8; N] {
    let mut buf = [0u8; N];
    // SystemRandom reads the OS CSPRNG; failure means the OS cannot provide
    // randomness at all, and there is no safe way to continue.
    #[allow(clippy::expect_used, reason = "no safe fallback without OS randomness")]
    SystemRandom::new().fill(&mut buf).expect("OS random number generator failed");
    buf
}

/// Lowercase Crockford base32 of `bytes`, most significant bits first.
fn base32(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 8 / 5 + 1);
    let (mut acc, mut bits) = (0u32, 0u32);
    for &b in bytes {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(char::from(CROCKFORD[((acc >> bits) & 31) as usize]));
        }
    }
    if bits > 0 {
        out.push(char::from(CROCKFORD[((acc << (5 - bits)) & 31) as usize]));
    }
    out
}

/// The last ID value handed out, so IDs from this process strictly increase.
static LAST: Mutex<u128> = Mutex::new(0);

/// A new ID like `chr_01jb3k…`: 48 bits of milliseconds then 80 random bits.
///
/// IDs sort by creation time, and are strictly increasing within a process:
/// two made in the same millisecond (or after the clock steps back) take the
/// previous value plus one, as monotonic ULIDs do. Audit and history paging
/// rely on that order.
#[must_use]
pub fn new_id(prefix: &str) -> String {
    let ms = u128::from(u64::try_from(Timestamp::now().millis()).unwrap_or(0) & 0xffff_ffff_ffff);
    let mut rand = [0u8; 16];
    rand[6..].copy_from_slice(&random::<10>());
    let candidate = (ms << 80) | u128::from_be_bytes(rand);
    let value = {
        let mut last = LAST.lock().unwrap_or_else(PoisonError::into_inner);
        *last = msapi_core::policy::next_id(*last, candidate);
        *last
    };
    format!("{prefix}_{}", base32(&value.to_be_bytes()))
}

/// A new bearer token: `msk_` followed by 256 random bits.
#[must_use]
pub fn new_token_secret() -> String {
    format!("msk_{}", base32(&random::<32>()))
}

/// SHA-256 of a token, which is what the database stores.
#[must_use]
pub fn hash_token(token: &str) -> Vec<u8> {
    ring::digest::digest(&ring::digest::SHA256, token.as_bytes()).as_ref().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base32_matches_known_vectors() {
        assert_eq!(base32(&[]), "");
        assert_eq!(base32(&[0xff]), "zw");
        assert_eq!(base32(&[0, 0, 0, 0, 0]), "00000000");
    }

    #[test]
    fn ids_sort_by_creation_and_do_not_collide() {
        let a = new_id("x");
        std::thread::sleep(std::time::Duration::from_millis(2));
        let b = new_id("x");
        assert!(a < b, "{a} !< {b}");
        assert_eq!(a.len(), 2 + 26);
    }

    #[test]
    fn ids_strictly_increase_within_a_millisecond() {
        let ids: Vec<String> = (0..10_000).map(|_| new_id("x")).collect();
        assert!(ids.windows(2).all(|w| w[0] < w[1]));
    }

    #[test]
    fn token_shape() {
        let t = new_token_secret();
        assert!(t.starts_with("msk_"));
        assert_eq!(t.len(), 4 + 52);
        assert_ne!(t, new_token_secret());
        assert_eq!(hash_token(&t).len(), 32);
    }
}
