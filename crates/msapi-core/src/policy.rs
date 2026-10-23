//! Token rules as plain code, each checked by Verus.
//!
//! The server keeps the I/O: it parses requests, looks up which accounts a user
//! owns, and stores the result. The decisions are here: what a delegated token
//! may be granted, how long it may live, and the order IDs are issued in.
//!
//! Scope sets are bitsets: scope `i` is bit `i` of a `u16`.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::manual_range_contains,
    reason = "plain comparisons and casts are what Verus checks; each cast here is proven in range"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Longest lifetime of a delegated token: thirty days.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_TTL_SECONDS: u64 = 30 * 24 * 60 * 60;
/// Shortest lifetime of a delegated token: one minute.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MIN_TTL_SECONDS: u64 = 60;
/// Lifetime when the request does not give one: a day.
#[cfg_attr(feature = "verus", verus_verify)]
pub const DEFAULT_TTL_SECONDS: u64 = 24 * 60 * 60;
/// Deepest delegation chain below a root token.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_DEPTH: u64 = 4;

#[cfg(feature = "verus")]
verus! {

/// Scope `i` is in `set`.
pub open spec fn bit_set(set: u16, i: u16) -> bool {
    (set >> i) & 1u16 == 1u16
}

/// Every scope in `a` is in `b`.
pub open spec fn subset(a: u16, b: u16) -> bool {
    forall|i: u16| i < 16 && #[trigger] bit_set(a, i) ==> bit_set(b, i)
}

} // verus!

/// Whether scope `i` is in `set`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => requires i < 16, ensures r == bit_set(set, i)))]
#[must_use]
pub const fn contains(set: u16, i: u16) -> bool {
    (set >> i) & 1 == 1
}

/// The scopes in `a` that are not in `b`. Empty exactly when `a ⊆ b`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        forall|i: u16| i < 16 ==> (bit_set(r, i) <==> bit_set(a, i) && !bit_set(b, i)),
        (r == 0) == subset(a, b),
))]
#[must_use]
pub const fn minus(a: u16, b: u16) -> u16 {
    let r = a & !b;
    proof! {
        assert forall|i: u16| i < 16 implies (bit_set(r, i) <==> bit_set(a, i) && !bit_set(b, i)) by {
            assert(((a & !b) >> i) & 1u16 == 1u16 <==> (a >> i) & 1u16 == 1u16 && (b >> i) & 1u16 != 1u16)
                by (bit_vector) requires i < 16;
        }
        if r == 0 {
            assert forall|i: u16| i < 16 && #[trigger] bit_set(a, i) implies bit_set(b, i) by {
                assert((0u16 >> i) & 1u16 != 1u16) by (bit_vector);
            }
        } else {
            // Some bit of r is set; it is in a and not in b.
            let i = choose_bit(r);
            assert(bit_set(a, i) && !bit_set(b, i));
        }
    }
    r
}

/// Whether every scope in `a` is in `b`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == subset(a, b)))]
#[must_use]
pub const fn is_subset(a: u16, b: u16) -> bool {
    minus(a, b) == 0
}

#[cfg(feature = "verus")]
verus! {

/// A set bit of a nonzero value.
proof fn choose_bit(r: u16) -> (i: u16)
    requires r != 0,
    ensures i < 16, bit_set(r, i),
{
    if bit_set(r, 0) { 0 }
    else if bit_set(r, 1) { 1 } else if bit_set(r, 2) { 2 } else if bit_set(r, 3) { 3 }
    else if bit_set(r, 4) { 4 } else if bit_set(r, 5) { 5 } else if bit_set(r, 6) { 6 }
    else if bit_set(r, 7) { 7 } else if bit_set(r, 8) { 8 } else if bit_set(r, 9) { 9 }
    else if bit_set(r, 10) { 10 } else if bit_set(r, 11) { 11 } else if bit_set(r, 12) { 12 }
    else if bit_set(r, 13) { 13 } else if bit_set(r, 14) { 14 } else {
        assert(bit_set(r, 15)) by (bit_vector)
            requires r != 0,
                (r >> 0u16) & 1u16 != 1u16, (r >> 1u16) & 1u16 != 1u16, (r >> 2u16) & 1u16 != 1u16,
                (r >> 3u16) & 1u16 != 1u16, (r >> 4u16) & 1u16 != 1u16, (r >> 5u16) & 1u16 != 1u16,
                (r >> 6u16) & 1u16 != 1u16, (r >> 7u16) & 1u16 != 1u16, (r >> 8u16) & 1u16 != 1u16,
                (r >> 9u16) & 1u16 != 1u16, (r >> 10u16) & 1u16 != 1u16, (r >> 11u16) & 1u16 != 1u16,
                (r >> 12u16) & 1u16 != 1u16, (r >> 13u16) & 1u16 != 1u16, (r >> 14u16) & 1u16 != 1u16;
        15
    }
}

} // verus!

/// What the server found out about one account a new token asks for.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AccountCheck {
    /// The user owns the account.
    pub owned: bool,
    /// The minting token may reach the account (always true if it is unlimited).
    pub reachable: bool,
}

/// Why a token cannot be minted.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MintRefusal {
    /// The request grants no scopes.
    NoScopes,
    /// The request grants scopes the minting token lacks; these ones.
    ExcessScopes(u16),
    /// The chain below the root token is already [`MAX_DEPTH`] long.
    TooDeep,
    /// The minting token is limited to accounts, so the new one must list some.
    MustListAccounts,
    /// The request lists an empty set of accounts.
    EmptyAccounts,
    /// The account at this index of the request is not the user's.
    UnknownAccount(usize),
    /// The account at this index is the user's, but the minting token cannot reach it.
    UnreachableAccount(usize),
    /// The lifetime is outside `[MIN_TTL_SECONDS, MAX_TTL_SECONDS]`.
    TtlOutOfRange,
    /// An explicit lifetime runs past the minting token's expiry.
    OutlivesParent,
}

/// The minting token, as far as the rules care.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Parent {
    /// Its scopes.
    pub scopes: u16,
    /// Delegations above it: 0 for a root token.
    pub depth: u64,
    /// Whether it is limited to specific accounts.
    pub limited: bool,
    /// When it (or any ancestor) expires, in Unix milliseconds.
    pub expires_at: Option<i64>,
}

/// Decides whether `parent` may mint a token with `scopes`, limited to
/// `accounts` (or to none, if `None`), living `ttl_seconds` (or the default)
/// from `now_ms`. Returns the new token's expiry.
///
/// A minted token never has more than its parent: its scopes are a subset,
/// its accounts are owned and reachable, it is limited whenever the parent is,
/// it expires no later, and the chain stays within [`MAX_DEPTH`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires now_ms >= 0, now_ms <= i64::MAX - (MAX_TTL_SECONDS * 1000) as i64,
    ensures r matches Ok(expires_at) ==> {
        &&& scopes != 0
        &&& subset(scopes, parent.scopes)
        &&& parent.depth < MAX_DEPTH
        &&& (parent.limited ==> accounts is Some)
        &&& (accounts matches Some(list) ==> list@.len() > 0
                && forall|i: int| 0 <= i < list@.len() ==> (#[trigger] list@[i]).owned && list@[i].reachable)
        &&& expires_at <= now_ms + MAX_TTL_SECONDS * 1000
        &&& (parent.expires_at matches Some(p) ==> expires_at <= p)
    },
))]
pub fn check_mint(
    parent: Parent,
    scopes: u16,
    accounts: Option<&[AccountCheck]>,
    ttl_seconds: Option<u64>,
    now_ms: i64,
) -> Result<i64, MintRefusal> {
    if scopes == 0 {
        return Err(MintRefusal::NoScopes);
    }
    let excess = minus(scopes, parent.scopes);
    if excess != 0 {
        return Err(MintRefusal::ExcessScopes(excess));
    }
    if parent.depth >= MAX_DEPTH {
        return Err(MintRefusal::TooDeep);
    }
    match accounts {
        None => {
            if parent.limited {
                return Err(MintRefusal::MustListAccounts);
            }
        }
        Some(list) => {
            if list.is_empty() {
                return Err(MintRefusal::EmptyAccounts);
            }
            let mut i = 0;
            #[cfg_attr(feature = "verus", verus_spec(
                invariant
                    0 <= i <= list@.len(),
                    forall|j: int| 0 <= j < i ==> (#[trigger] list@[j]).owned && list@[j].reachable,
                decreases list@.len() - i
            ))]
            while i < list.len() {
                if !list[i].owned {
                    return Err(MintRefusal::UnknownAccount(i));
                }
                if !list[i].reachable {
                    return Err(MintRefusal::UnreachableAccount(i));
                }
                i += 1;
            }
        }
    }
    let ttl = match ttl_seconds {
        Some(t) => t,
        None => DEFAULT_TTL_SECONDS,
    };
    if ttl < MIN_TTL_SECONDS || ttl > MAX_TTL_SECONDS {
        return Err(MintRefusal::TtlOutOfRange);
    }
    let expires_at = now_ms + (ttl * 1000) as i64;
    match parent.expires_at {
        Some(p) if expires_at > p => {
            // The default shortens to fit; an explicit lifetime the parent cannot grant is refused.
            if ttl_seconds.is_some() { Err(MintRefusal::OutlivesParent) } else { Ok(p) }
        }
        _ => Ok(expires_at),
    }
}

/// The next ID value after `last`, given a fresh `candidate` (time in the high
/// bits, randomness below): the candidate if it is larger, else `last + 1`.
///
/// IDs therefore strictly increase within a process even when two land in the
/// same millisecond or the clock steps back. (`last` would have to reach
/// `u128::MAX`, past the year 10,000, for that to stop holding.)
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r >= candidate, r >= last, last < u128::MAX ==> r > last,
))]
#[must_use]
pub const fn next_id(last: u128, candidate: u128) -> u128 {
    if candidate > last { candidate } else { last.saturating_add(1) }
}

/// A page size from the `limit` query parameter: 50 when absent, else 1-200.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        requested is None ==> r == Some(50u32),
        requested matches Some(n) ==> (r is Some <==> 1 <= n <= 200) && (r is Some ==> r == Some(n as u32)),
))]
#[must_use]
pub fn page_size(requested: Option<u64>) -> Option<u32> {
    match requested {
        None => Some(50),
        Some(n) if n >= 1 && n <= 200 => Some(n as u32),
        Some(_) => None,
    }
}
