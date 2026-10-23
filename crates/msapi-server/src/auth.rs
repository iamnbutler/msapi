//! Bearer tokens: root tokens for people, delegated tokens for their agents.
//!
//! A token is `msk_` plus 256 random bits. The database keeps only its SHA-256,
//! so a leaked database does not leak usable credentials. Plain SHA-256 is
//! enough because the secret is random, not a password.
//!
//! Delegation is attenuation only. A token can mint a child with a subset of
//! its scopes, a subset of its accounts and an earlier expiry, and nothing
//! else. Every request re-checks the whole ancestor chain, so revoking or
//! expiring a token cuts off everything minted from it immediately.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_map,
    clippy::single_match,
    clippy::collapsible_if,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening, `Option` combinators or `if let` chains"
)]

use std::fmt;
use std::str::FromStr;

use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};

use msapi_core::Timestamp;
use msapi_core::api;
use msapi_core::msg;
use msapi_core::policy::{self, AccountCheck, Link, MintRefusal, Parent};
use msapi_core::scope;

use crate::error::ApiError;
use crate::ids;
#[cfg(feature = "verus")]
use msapi_core::msg::{chars, lemma_boundary_after_ascii};
#[cfg(feature = "verus")]
use msapi_core::policy::{bit_set, reaches_spec, subset};
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(feature = "verus")]
use vstd::utf8::{
    encode_utf8, encode_utf8_valid_utf8, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq,
};

/// One permission.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Scope {
    /// Read accounts.
    AccountsRead,
    /// Create and edit accounts.
    AccountsWrite,
    /// Read characters and their stats.
    CharactersRead,
    /// Create and edit characters and record their stats.
    CharactersWrite,
    /// Delete accounts and characters. Separate so an agent can edit without being able to destroy.
    Delete,
    /// List tokens.
    TokensRead,
    /// Mint and revoke tokens.
    TokensWrite,
    /// Read the audit log.
    AuditRead,
}

impl Scope {
    /// Every scope.
    pub const ALL: [Self; 8] = [
        Self::AccountsRead,
        Self::AccountsWrite,
        Self::CharactersRead,
        Self::CharactersWrite,
        Self::Delete,
        Self::TokensRead,
        Self::TokensWrite,
        Self::AuditRead,
    ];
}

#[cfg(feature = "verus")]
verus! {

impl Scope {
    /// The wire name, e.g. `"characters:write"`.
    pub open spec fn wire(self) -> Seq<char> {
        match self {
            Self::AccountsRead => "accounts:read"@,
            Self::AccountsWrite => "accounts:write"@,
            Self::CharactersRead => "characters:read"@,
            Self::CharactersWrite => "characters:write"@,
            Self::Delete => "delete"@,
            Self::TokensRead => "tokens:read"@,
            Self::TokensWrite => "tokens:write"@,
            Self::AuditRead => "audit:read"@,
        }
    }
}

/// The error for a name that is no scope.
pub open spec fn unknown_message(name: Seq<char>) -> Seq<char> {
    "unknown scope `"@ + name
        + "`; known scopes: accounts:read, accounts:write, characters:read, characters:write, delete, tokens:read, tokens:write, audit:read"@
}

/// The scope `names[i]` names, if any.
pub open spec fn named(names: Seq<String>, i: int) -> Option<u16> {
    scope::index_of(encode_utf8(names[i]@))
}

/// `ids` separated by `", "`, as `[String]::join(", ")` gives.
pub open spec fn joined(ids: Seq<String>) -> Seq<char>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else if ids.len() == 1 {
        ids[0]@
    } else {
        joined(ids.drop_last()) + ", "@ + ids.last()@
    }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl Scope {
    /// The wire name, e.g. `"characters:write"`. The tests check it is the
    /// text the proven [`scope::scope_name`] table parses.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == self.wire()))]
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AccountsRead => "accounts:read",
            Self::AccountsWrite => "accounts:write",
            Self::CharactersRead => "characters:read",
            Self::CharactersWrite => "characters:write",
            Self::Delete => "delete",
            Self::TokensRead => "tokens:read",
            Self::TokensWrite => "tokens:write",
            Self::AuditRead => "audit:read",
        }
    }

    /// The scope at index `k` of [`Scope::ALL`].
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(s) ==> s as u16 == k,
            k < scope::COUNT ==> r is Some,
    ))]
    #[must_use]
    pub fn from_index(k: u16) -> Option<Self> {
        match k {
            0 => Some(Self::AccountsRead),
            1 => Some(Self::AccountsWrite),
            2 => Some(Self::CharactersRead),
            3 => Some(Self::CharactersWrite),
            4 => Some(Self::Delete),
            5 => Some(Self::TokensRead),
            6 => Some(Self::TokensWrite),
            7 => Some(Self::AuditRead),
            _ => None,
        }
    }

    /// The scope `name` names: the proven [`scope::scope_index`].
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(s) ==> scope::index_of(name.spec_bytes()) == Some(s as u16),
            scope::index_of(name.spec_bytes()) is None <==> r is None,
    ))]
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        match scope::scope_index(name.as_bytes()) {
            Some(k) => Self::from_index(k),
            None => None,
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FromStr for Scope {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match Self::parse(s) {
            Some(x) => Ok(x),
            None => Err(unknown_scope(s)),
        }
    }
}

/// The error for `name`, which is no scope.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == unknown_message(name@)))]
fn unknown_scope(name: &str) -> String {
    let mut m = String::new();
    m.push_str("unknown scope `");
    m.push_str(name);
    m.push_str(
        "`; known scopes: accounts:read, accounts:write, characters:read, characters:write, delete, tokens:read, tokens:write, audit:read",
    );
    proof! {
        assert(Seq::<char>::empty() + "unknown scope `"@ =~= "unknown scope `"@);
    }
    m
}

/// A set of scopes: bit `i` is scope `i` of [`Scope::ALL`].
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Scopes(u16);

#[cfg(feature = "verus")]
verus! {

impl Scopes {
    /// The set as bits.
    pub closed spec fn bits(self) -> u16 {
        self.0
    }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl Scopes {
    /// Every scope, as a root token has.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures forall|j: u16| j < 16 ==> (bit_set(r.bits(), j) <==> j < scope::COUNT),
    ))]
    #[must_use]
    pub fn all() -> Self {
        Self(policy::first(scope::COUNT))
    }

    /// Whether `scope` is in the set.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == bit_set(self.bits(), scope as u16)))]
    #[must_use]
    pub const fn contains(self, scope: Scope) -> bool {
        policy::contains(self.0, scope as u16)
    }

    /// Whether every scope in `self` is also in `other`.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == subset(self.bits(), other.bits())))]
    #[must_use]
    pub const fn is_subset_of(self, other: Self) -> bool {
        policy::is_subset(self.0, other.0)
    }

    /// The scopes in `self` that are not in `other`.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures forall|i: u16| i < 16 ==> (bit_set(r.bits(), i) <==> bit_set(self.bits(), i) && !bit_set(other.bits(), i)),
    ))]
    #[must_use]
    pub const fn minus(self, other: Self) -> Self {
        Self(policy::minus(self.0, other.0))
    }

    /// The scopes, in declaration order.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            forall|i: int| 0 <= i < r@.len() ==> bit_set(self.bits(), #[trigger] r@[i] as u16),
            forall|i: int, j: int| 0 <= i < j < r@.len() ==> (#[trigger] r@[i] as u16) < (#[trigger] r@[j] as u16),
            forall|k: u16| k < scope::COUNT && #[trigger] bit_set(self.bits(), k) ==> exists|i: int| 0 <= i < r@.len() && #[trigger] r@[i] as u16 == k,
    ))]
    #[must_use]
    pub fn list(self) -> Vec<Scope> {
        let mut out: Vec<Scope> = Vec::new();
        let mut k: u16 = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                k <= scope::COUNT,
                forall|i: int| 0 <= i < out@.len() ==> bit_set(self.bits(), #[trigger] out@[i] as u16) && (out@[i] as u16) < k,
                forall|i: int, j: int| 0 <= i < j < out@.len() ==> (#[trigger] out@[i] as u16) < (#[trigger] out@[j] as u16),
                forall|m: u16| m < k && #[trigger] bit_set(self.bits(), m) ==> exists|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as u16 == m,
            decreases scope::COUNT - k
        ))]
        while k < scope::COUNT {
            proof_decl! {
                let ghost before = out@;
            }
            if let Some(s) = Scope::from_index(k) {
                if self.contains(s) {
                    out.push(s);
                    proof! {
                        assert(out@[out@.len() - 1] as u16 == k);
                    }
                }
            }
            proof! {
                assert forall|m: u16| m < k + 1 && #[trigger] bit_set(self.bits(), m)
                    implies exists|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as u16 == m by {
                    if m < k {
                        let i = choose|i: int| 0 <= i < before.len() && #[trigger] before[i] as u16 == m;
                        assert(out@[i] == before[i]);
                    } else {
                        assert(out@[out@.len() - 1] as u16 == k);
                    }
                }
            }
            k += 1;
        }
        out
    }

    /// The scopes named in `names`.
    ///
    /// # Errors
    ///
    /// The first name that is no scope, worded by [`unknown_scope`].
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(set) => forall|k: u16| k < 16 ==> (#[trigger] bit_set(set.bits(), k)
                    <==> exists|i: int| 0 <= i < names@.len() && #[trigger] named(names@, i) == Some(k)),
                Err(m) => exists|i: int| 0 <= i < names@.len() && #[trigger] named(names@, i) is None
                    && m@ == unknown_message(names@[i]@),
            },
    ))]
    pub fn from_names(names: &[String]) -> Result<Self, String> {
        let mut acc: u16 = 0;
        let mut i: usize = 0;
        proof! {
            assert forall|k: u16| k < 16 implies !bit_set(0u16, k) by {
                assert((0u16 >> k) & 1u16 == 0u16) by (bit_vector);
            }
        }
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                i <= names@.len(),
                forall|k: u16| k < 16 ==> (#[trigger] bit_set(acc, k)
                    <==> exists|j: int| 0 <= j < i && #[trigger] named(names@, j) == Some(k)),
            decreases names@.len() - i
        ))]
        while i < names.len() {
            match Scope::parse(names[i].as_str()) {
                Some(s) => {
                    let next = policy::with(acc, s as u16);
                    proof! {
                        assert forall|k: u16| k < 16 implies (#[trigger] bit_set(next, k)
                            <==> exists|j: int| 0 <= j < i + 1 && #[trigger] named(names@, j) == Some(k)) by {
                            if bit_set(next, k) {
                                if k == s as u16 {
                                    assert(named(names@, i as int) == Some(k));
                                } else {
                                    assert(bit_set(acc, k));
                                }
                            }
                            if exists|j: int| 0 <= j < i + 1 && #[trigger] named(names@, j) == Some(k) {
                                let j = choose|j: int| 0 <= j < i + 1 && #[trigger] named(names@, j) == Some(k);
                                if j < i {
                                    assert(bit_set(acc, k));
                                }
                            }
                        }
                    }
                    acc = next;
                }
                None => {
                    proof! {
                        assert(named(names@, i as int) is None);
                    }
                    return Err(unknown_scope(names[i].as_str()));
                }
            }
            i += 1;
        }
        Ok(Self(acc))
    }

    /// The names of the scopes, separated by spaces: the proven
    /// [`scope::format_scopes`].
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == chars(scope::fmt(self.bits(), 8))))]
    #[must_use]
    pub fn text(self) -> String {
        msg::text(scope::format_scopes(self.0).as_slice())
    }

    /// What `Debug` writes: `Scopes(delete tokens:read)`.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == "Scopes("@ + chars(scope::fmt(self.bits(), 8)) + ")"@))]
    #[must_use]
    pub fn debug_text(self) -> String {
        let mut m = String::new();
        m.push_str("Scopes(");
        m.push_str(self.text().as_str());
        m.push_str(")");
        proof! {
            assert(Seq::<char>::empty() + "Scopes("@ =~= "Scopes("@);
        }
        m
    }

    /// The scopes in space-separated `s`: the proven [`scope::parse_scopes`].
    ///
    /// # Errors
    ///
    /// A word that is no scope, worded by [`unknown_scope`].
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(set) => scope::parse(s.spec_bytes()) == Some(set.bits()),
                Err(m) => scope::parse(s.spec_bytes()) is None
                    && exists|w: Seq<char>| scope::index_of(encode_utf8(w)) is None && m@ == #[trigger] unknown_message(w),
            },
    ))]
    pub fn parse(s: &str) -> Result<Self, String> {
        match scope::parse_scopes(s.as_bytes()) {
            Ok(bits) => Ok(Self(bits)),
            Err((start, end)) => {
                // The offending word is bounded by ASCII whitespace or the
                // ends, so both cuts fall on character boundaries.
                proof! {
                    let b = s.spec_bytes();
                    encode_utf8_valid_utf8(s@);
                    is_char_boundary_start_end_of_seq(b);
                    if start > 0 {
                        lemma_boundary_after_ascii(b, start - 1);
                    }
                    if end < b.len() {
                        is_char_boundary_iff_not_is_continuation_byte(b, end as int);
                    }
                }
                let word = msg::cut(s, start, end);
                let m = unknown_scope(word);
                proof! {
                    assert(word.spec_bytes() == s.spec_bytes().subrange(start as int, end as int));
                    assert(unknown_message(word@) == m@);
                }
                Err(m)
            }
        }
    }
}

impl fmt::Display for Scopes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.text())
    }
}

impl fmt::Debug for Scopes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.debug_text())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FromStr for Scopes {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl Serialize for Scopes {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.list().into_iter().map(Scope::as_str))
    }
}

impl<'de> Deserialize<'de> for Scopes {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let names = Vec::<String>::deserialize(deserializer)?;
        Self::from_names(&names).map_err(serde::de::Error::custom)
    }
}

/// Who is making a request, as established by their token.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Debug)]
pub struct Principal {
    /// The user.
    pub user_id: String,
    /// The token used.
    pub token_id: String,
    /// The token's label, recorded in audit events.
    pub label: String,
    /// Whether this is a root (non-delegated) token.
    pub root: bool,
    /// What the token may do.
    pub scopes: Scopes,
    /// The accounts the token may touch; `None` means all of the user's.
    pub account_ids: Option<Vec<String>>,
    /// When the token stops working.
    pub expires_at: Option<Timestamp>,
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Principal {
    /// Fails unless the token has `scope`.
    ///
    /// # Errors
    ///
    /// 403 naming the token and the missing scope.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r is Ok <==> bit_set(self.scopes.bits(), scope as u16),
            r matches Err(e) ==> e.status == 403 && e.name == "forbidden" && e.details is None
                && e.message@ == "token `"@ + self.label@ + "` lacks the `"@ + scope.wire() + "` scope"@,
    ))]
    pub fn require(&self, scope: Scope) -> Result<(), ApiError> {
        if self.scopes.contains(scope) {
            Ok(())
        } else {
            let mut m = String::new();
            m.push_str("token `");
            m.push_str(self.label.as_str());
            m.push_str("` lacks the `");
            m.push_str(scope.as_str());
            m.push_str("` scope");
            proof! {
                assert(Seq::<char>::empty() + "token `"@ =~= "token `"@);
            }
            Err(ApiError { status: 403, name: "forbidden", message: m, details: None })
        }
    }

    /// Fails unless the token may touch `account_id`.
    ///
    /// # Errors
    ///
    /// 403 naming the token and the accounts it is limited to.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r is Ok <==> match self.account_ids {
                None => true,
                Some(ids) => exists|i: int| 0 <= i < ids@.len() && #[trigger] encode_utf8(ids@[i]@) == account_id.spec_bytes(),
            },
            r matches Err(e) ==> e.status == 403 && e.name == "forbidden" && e.details is None
                && e.message@ == "token `"@ + self.label@ + "` is limited to accounts "@
                    + joined(match self.account_ids { Some(ids) => ids@, None => Seq::empty() }),
    ))]
    pub fn require_account(&self, account_id: &str) -> Result<(), ApiError> {
        if self.reaches_account(account_id) {
            return Ok(());
        }
        let mut m = String::new();
        m.push_str("token `");
        m.push_str(self.label.as_str());
        m.push_str("` is limited to accounts ");
        match &self.account_ids {
            Some(ids) => m.push_str(join(ids.as_slice()).as_str()),
            None => {
                proof! {
                    assert(joined(Seq::<String>::empty()) =~= Seq::<char>::empty());
                }
            }
        }
        proof! {
            assert(Seq::<char>::empty() + "token `"@ =~= "token `"@);
        }
        Err(ApiError { status: 403, name: "forbidden", message: m, details: None })
    }
}

/// `ids` separated by `", "`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == joined(ids@)))]
fn join(ids: &[String]) -> String {
    let mut out = String::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= ids@.len(),
            out@ == joined(ids@.subrange(0, i as int)),
        decreases ids@.len() - i
    ))]
    while i < ids.len() {
        proof! {
            assert(ids@.subrange(0, i + 1).drop_last() =~= ids@.subrange(0, i as int));
        }
        proof! {
            if i == 0 {
                assert(Seq::<char>::empty() + ids@[0]@ =~= ids@[0]@);
            }
        }
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(ids[i].as_str());
        i += 1;
    }
    proof! {
        assert(ids@.subrange(0, ids@.len() as int) =~= ids@);
    }
    out
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Principal {
    /// Whether the token may touch `account_id`: the proven
    /// [`policy::reaches`] over the token's account list.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r == match self.account_ids {
            None => true,
            Some(ids) => exists|i: int| 0 <= i < ids@.len() && #[trigger] encode_utf8(ids@[i]@) == account_id.spec_bytes(),
        },
    ))]
    #[must_use]
    pub fn reaches_account(&self, account_id: &str) -> bool {
        match &self.account_ids {
            None => policy::reaches(account_id.as_bytes(), None),
            Some(ids) => {
                let allowed = as_bytes(ids);
                let r = policy::reaches(account_id.as_bytes(), Some(allowed.as_slice()));
                proof! {
                    if r {
                        let j = choose|j: int| 0 <= j < allowed@.len() && (#[trigger] allowed@[j])@ == account_id.spec_bytes();
                        assert(encode_utf8(ids@[j]@) == account_id.spec_bytes());
                    } else {
                        assert forall|i: int| 0 <= i < ids@.len() implies #[trigger] encode_utf8(ids@[i]@) != account_id.spec_bytes() by {
                            assert(allowed@[i]@ == encode_utf8(ids@[i]@));
                        }
                    }
                }
                r
            }
        }
    }
}

/// Views IDs as the byte strings `msapi_core::policy` compares.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@.len() == ids@.len(),
        forall|i: int| 0 <= i < ids@.len() ==> #[trigger] r@[i]@ == encode_utf8(ids@[i]@),
))]
pub(crate) fn as_bytes(ids: &[String]) -> Vec<&[u8]> {
    let mut out: Vec<&[u8]> = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= ids@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j]@ == encode_utf8(ids@[j]@),
        decreases ids@.len() - i
    ))]
    while i < ids.len() {
        // vstd specifies `str::as_bytes`, not `String::as_bytes`.
        #[allow(clippy::redundant_as_str, reason = "Verus needs the `&str` step")]
        out.push(ids[i].as_str().as_bytes());
        i += 1;
    }
    out
}

/// Resolves an `Authorization` header to a principal.
pub fn authenticate(conn: &Connection, authorization: Option<&str>) -> Result<Principal, ApiError> {
    // `bearer` cuts after an ASCII prefix and trims whole characters, so the
    // range always falls on character boundaries.
    let token = authorization
        .and_then(|h| api::bearer(h.as_bytes()).and_then(|(a, b)| h.get(a..b)))
        .ok_or_else(|| ApiError::unauthorized("send `Authorization: Bearer msk_…`"))?;
    let now = Timestamp::now().millis();

    let row = conn
        .query_row(
            "SELECT id, user_id, label, parent_id IS NULL, scopes, account_ids FROM tokens WHERE secret_hash = ?1",
            [ids::hash_token(token)],
            |r| {
                Ok((
                    r.get::<_, String>(0)?,
                    r.get::<_, String>(1)?,
                    r.get::<_, String>(2)?,
                    r.get::<_, bool>(3)?,
                    r.get::<_, String>(4)?,
                    r.get::<_, Option<String>>(5)?,
                ))
            },
        )
        .optional()?;
    let Some((token_id, user_id, label, root, scopes, account_ids)) = row else {
        return Err(ApiError::unauthorized("unknown token"));
    };

    // The token and every ancestor must be live; the earliest expiry wins.
    // SQL gathers the chain; `policy::chain_expiry` (checked by Verus) decides.
    let chain: Vec<Link> = conn
        .prepare_cached(
            "WITH RECURSIVE chain(id, parent_id, revoked_at, expires_at) AS (
                 SELECT id, parent_id, revoked_at, expires_at FROM tokens WHERE id = ?1
                 UNION ALL
                 SELECT t.id, t.parent_id, t.revoked_at, t.expires_at FROM tokens t JOIN chain c ON t.id = c.parent_id
             )
             SELECT revoked_at IS NOT NULL, expires_at FROM chain",
        )?
        .query_map([&token_id], |r| Ok(Link { revoked: r.get(0)?, expires_at: r.get(1)? }))?
        .collect::<rusqlite::Result<_>>()?;
    let Some(earliest_expiry) = policy::chain_expiry(&chain, now) else {
        return Err(ApiError::unauthorized("token is revoked or expired, or was minted from one that is"));
    };

    conn.execute(
        "UPDATE tokens SET last_used_at = ?2 WHERE id = ?1 AND (last_used_at IS NULL OR last_used_at < ?2 - 60000)",
        params![token_id, now],
    )?;

    Ok(Principal {
        user_id,
        token_id,
        label,
        root,
        scopes: scopes.parse().map_err(|e: String| {
            eprintln!("stored scopes unreadable: {e}");
            ApiError::internal()
        })?,
        account_ids: account_ids.as_deref().map(serde_json::from_str).transpose().map_err(|e| {
            eprintln!("stored account_ids unreadable: {e}");
            ApiError::internal()
        })?,
        expires_at: earliest_expiry.map(Timestamp::from_millis),
    })
}

/// Creates a user and their first root token. Returns `(user_id, token)`.
///
/// This is the bootstrap path (`msapi user create`); passkey and GitHub sign-in
/// will mint root tokens the same way.
pub fn create_user(conn: &mut Connection, display_name: &str) -> rusqlite::Result<(String, String)> {
    let tx = crate::durable::Logged::begin(conn)?;
    let now = Timestamp::now().millis();
    let user_id = ids::new_id("usr");
    tx.execute(
        "INSERT INTO users (id, display_name, created_at) VALUES (?1, ?2, ?3)",
        params![user_id, display_name, now],
    )?;
    let token = ids::new_token_secret();
    tx.execute(
        "INSERT INTO tokens (id, user_id, parent_id, label, scopes, account_ids, secret_hash, created_at, expires_at)
         VALUES (?1, ?2, NULL, 'root', ?3, NULL, ?4, ?5, NULL)",
        params![ids::new_id("tok"), user_id, Scopes::all().to_string(), ids::hash_token(&token), now],
    )?;
    tx.commit()?;
    Ok((user_id, token))
}

/// Default lifetime of a delegated token: one day.
#[cfg_attr(feature = "verus", verus_verify)]
pub const DEFAULT_TTL_SECONDS: u64 = policy::DEFAULT_TTL_SECONDS;
/// Longest lifetime of a delegated token: thirty days.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_TTL_SECONDS: u64 = policy::MAX_TTL_SECONDS;
/// Deepest delegation chain below a root token.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_DEPTH: u64 = policy::MAX_DEPTH;

/// `POST /v1/tokens` body.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug)]
pub struct MintRequest {
    /// Shown in listings and copied into every audit event, e.g. `"ChatGPT import"`.
    pub label: String,
    /// The scopes to grant; must be a subset of the caller's.
    pub scopes: Scopes,
    /// Accounts to limit the token to. Required if the caller is itself limited.
    pub account_ids: Option<Vec<String>>,
    /// Lifetime in seconds: at most thirty days, and never past the caller's own
    /// expiry. Defaults to a day, or to the caller's expiry if that is sooner.
    pub expires_in_seconds: Option<u64>,
}

// Verus checks `MintRequest` and cannot take serde's derive on a checked
// type, so it deserializes through a derived twin with the same wire format
// and the same error messages.
impl<'de> Deserialize<'de> for MintRequest {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct MintRequest {
            label: String,
            scopes: Scopes,
            #[serde(default)]
            account_ids: Option<Vec<String>>,
            #[serde(default)]
            expires_in_seconds: Option<u64>,
        }
        let MintRequest { label, scopes, account_ids, expires_in_seconds } = MintRequest::deserialize(d)?;
        Ok(Self { label, scopes, account_ids, expires_in_seconds })
    }
}

/// A validated mint, ready to insert.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug)]
pub struct Mint {
    /// The new token's label.
    pub label: String,
    /// Its scopes.
    pub scopes: Scopes,
    /// Its account limit.
    pub account_ids: Option<Vec<String>>,
    /// Its expiry.
    pub expires_at: Timestamp,
}

#[cfg(feature = "verus")]
verus! {

/// `id` is one of `list`.
pub open spec fn listed(id: Seq<u8>, list: Seq<String>) -> bool {
    exists|j: int| 0 <= j < list.len() && #[trigger] encode_utf8(list[j]@) == id
}

} // verus!

impl MintRequest {
    /// Checks the request against what `parent` may delegate at `now_ms`:
    /// [`check_mint`] on this request's fields.
    ///
    /// `depth` is how many delegations already sit above `parent`
    /// (0 for a root token). `owned_accounts` are the user's account IDs.
    ///
    /// # Errors
    ///
    /// The refusal [`check_mint`] gives.
    #[cfg_attr(feature = "verus", verus_verify)]
    #[cfg_attr(feature = "verus", verus_spec(requires 0 <= now_ms))]
    pub fn validate(
        self,
        parent: &Principal,
        depth: u64,
        owned_accounts: &[String],
        now_ms: i64,
    ) -> Result<Mint, ApiError> {
        check_mint(
            &self.label,
            self.scopes,
            self.account_ids,
            self.expires_in_seconds,
            parent,
            depth,
            owned_accounts,
            now_ms,
        )
    }
}

/// The latest clock reading [`policy::check_mint`] accepts.
#[cfg_attr(feature = "verus", verus_verify)]
#[allow(
    clippy::cast_possible_wrap,
    reason = "thirty days of milliseconds fits an i64; Verus has no spec for `cast_signed`"
)]
pub const LATEST_MS: i64 = i64::MAX - (MAX_TTL_SECONDS * 1000) as i64;

/// Checks a mint of `label`, `scopes`, `account_ids` and
/// `expires_in_seconds` against what `parent` may delegate at `now_ms`.
///
/// The rules are the proven [`policy::check_mint`] and
/// [`policy::account_checks`]; this gathers their inputs and words their
/// refusals. `depth` is how many delegations already sit above `parent`
/// (0 for a root token). `owned_accounts` are the user's account IDs.
///
/// # Errors
///
/// A label that is not 1-100 characters once trimmed, or the refusal
/// [`policy::check_mint`] gives.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= now_ms,
    ensures
        r matches Ok(m) ==> {
            &&& encode_utf8(m.label@) == msapi_core::text::trimmed(encode_utf8(label@))
            &&& 1 <= msapi_core::text::chars(msapi_core::text::trimmed(encode_utf8(label@))) <= 100
            &&& m.scopes == scopes
            &&& m.account_ids == account_ids
            &&& scopes.bits() != 0
            &&& subset(scopes.bits(), parent.scopes.bits())
            &&& depth < MAX_DEPTH
            &&& (parent.account_ids is Some ==> account_ids is Some)
            &&& (account_ids matches Some(ids) ==> ids@.len() > 0 && forall|i: int| 0 <= i < ids@.len() ==> {
                    let id = #[trigger] encode_utf8(ids@[i]@);
                    &&& listed(id, owned_accounts@)
                    &&& (parent.account_ids matches Some(p) ==> listed(id, p@))
                })
            &&& now_ms <= LATEST_MS ==> m.expires_at.ms() <= now_ms + MAX_TTL_SECONDS * 1000
            &&& (parent.expires_at matches Some(p) ==> m.expires_at.ms() <= p.ms())
        },
))]
#[allow(clippy::too_many_arguments, reason = "the fields of a `MintRequest`, which Verus cannot see, plus the clock")]
pub fn check_mint(
    label: &str,
    scopes: Scopes,
    account_ids: Option<Vec<String>>,
    expires_in_seconds: Option<u64>,
    parent: &Principal,
    depth: u64,
    owned_accounts: &[String],
    now_ms: i64,
) -> Result<Mint, ApiError> {
    // `name_in` trims whole characters, so the range falls on character
    // boundaries; checking costs nothing and spares a proof that it does.
    let label = match api::name_in(label.as_bytes(), 1, 100) {
        Some((a, b)) if label.is_char_boundary(a) && label.is_char_boundary(b) => {
            let kept = msg::cut(label, a, b).to_owned();
            proof! {
                assert(encode_utf8(kept@) == encode_utf8(label@).subrange(a as int, b as int));
            }
            kept
        }
        _ => return Err(ApiError::invalid("label must be 1-100 characters")),
    };
    let owned = as_bytes(owned_accounts);
    let allowed: Option<Vec<&[u8]>> = match &parent.account_ids {
        Some(ids) => Some(as_bytes(ids.as_slice())),
        None => None,
    };
    let allowed_slice: Option<&[&[u8]]> = match &allowed {
        Some(v) => Some(v.as_slice()),
        None => None,
    };
    let checks: Option<Vec<AccountCheck>> = match &account_ids {
        Some(ids) => Some(policy::account_checks(as_bytes(ids.as_slice()).as_slice(), owned.as_slice(), allowed_slice)),
        None => None,
    };
    let check_slice: Option<&[AccountCheck]> = match &checks {
        Some(v) => Some(v.as_slice()),
        None => None,
    };
    let parent_expiry = match parent.expires_at {
        Some(t) => Some(t.millis()),
        None => None,
    };
    // A real clock is far inside this range; clamping keeps the policy's
    // arithmetic in bounds without a fallible step.
    let now = if now_ms > LATEST_MS { LATEST_MS } else { now_ms };
    let decision = policy::check_mint(
        Parent { scopes: parent.scopes.0, depth, limited: parent.account_ids.is_some(), expires_at: parent_expiry },
        scopes.0,
        check_slice,
        expires_in_seconds,
        now,
    );
    match decision {
        Ok(expires_at) => {
            proof! {
                if account_ids is Some {
                    let ids = account_ids->0;
                    assert forall|i: int| 0 <= i < ids@.len() implies {
                        let id = #[trigger] encode_utf8(ids@[i]@);
                        &&& listed(id, owned_accounts@)
                        &&& (parent.account_ids matches Some(p) ==> listed(id, p@))
                    } by {
                        let id = encode_utf8(ids@[i]@);
                        let c = (check_slice->0)@[i];
                        assert(c.owned && c.reachable);
                        let j = choose|j: int| 0 <= j < owned@.len() && (#[trigger] owned@[j])@ == id;
                        assert(encode_utf8(owned_accounts@[j]@) == id);
                        if parent.account_ids is Some {
                            let p = parent.account_ids->0;
                            let a = (allowed_slice->0)@;
                            let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k])@ == id;
                            assert(encode_utf8(p@[k]@) == id);
                        }
                    }
                }
            }
            Ok(Mint { label, scopes, account_ids, expires_at: Timestamp::from_millis(expires_at) })
        }
        Err(refusal) => Err(refusal_error(refusal, account_ids.as_ref(), parent.expires_at)),
    }
}

/// The error for `refusal`; `account_ids` are the requested accounts and
/// `parent_expiry` the minting token's expiry.
#[cfg_attr(feature = "verus", verus_verify)]
fn refusal_error(
    refusal: MintRefusal,
    account_ids: Option<&Vec<String>>,
    parent_expiry: Option<Timestamp>,
) -> ApiError {
    match refusal {
        MintRefusal::NoScopes => ApiError::invalid("grant at least one scope"),
        MintRefusal::ExcessScopes(excess) => {
            let mut m = String::new();
            m.push_str("cannot grant scopes this token does not have: ");
            m.push_str(Scopes(excess).text().as_str());
            ApiError::forbidden(m)
        }
        MintRefusal::TooDeep => {
            let mut m = String::new();
            m.push_str("delegation chains are limited to ");
            msg::push_uint(&mut m, MAX_DEPTH as u128);
            m.push_str(" levels");
            ApiError::forbidden(m)
        }
        MintRefusal::MustListAccounts => {
            ApiError::invalid("this token is limited to specific accounts, so the new token must list account_ids too")
        }
        MintRefusal::EmptyAccounts => {
            ApiError::invalid("account_ids must not be empty; omit it to allow every account")
        }
        MintRefusal::UnknownAccount(i) => ApiError::not_found_id("account", account_at(account_ids, i)),
        MintRefusal::UnreachableAccount(i) => {
            let mut m = String::new();
            m.push_str("this token cannot reach account `");
            m.push_str(account_at(account_ids, i));
            m.push_str("`");
            ApiError::forbidden(m)
        }
        MintRefusal::TtlOutOfRange => {
            let mut m = String::new();
            m.push_str("expires_in_seconds must be between ");
            msg::push_uint(&mut m, policy::MIN_TTL_SECONDS as u128);
            m.push_str(" and ");
            msg::push_uint(&mut m, MAX_TTL_SECONDS as u128);
            ApiError::invalid(m)
        }
        MintRefusal::OutlivesParent => {
            let mut m = String::new();
            m.push_str("a token cannot outlive the token that mints it; this one expires at ");
            if let Some(t) = parent_expiry {
                m.push_str(t.to_rfc3339().as_str());
            }
            ApiError::invalid(m)
        }
    }
}

/// Requested account `i`, or `""` if there is none.
#[cfg_attr(feature = "verus", verus_verify)]
fn account_at(account_ids: Option<&Vec<String>>, i: usize) -> &str {
    match account_ids {
        Some(ids) if i < ids.len() => ids[i].as_str(),
        _ => "",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn now() -> i64 {
        Timestamp::now().millis()
    }

    fn principal(scopes: &str, accounts: Option<&[&str]>) -> Principal {
        Principal {
            user_id: "usr_1".into(),
            token_id: "tok_1".into(),
            label: "test".into(),
            root: accounts.is_none(),
            scopes: scopes.parse().unwrap(),
            account_ids: accounts.map(|a| a.iter().map(|s| (*s).to_owned()).collect()),
            expires_at: None,
        }
    }

    fn request(scopes: &str, accounts: Option<&[&str]>) -> MintRequest {
        MintRequest {
            label: "agent".into(),
            scopes: scopes.parse().unwrap(),
            account_ids: accounts.map(|a| a.iter().map(|s| (*s).to_owned()).collect()),
            expires_in_seconds: None,
        }
    }

    #[test]
    fn scopes_round_trip_and_reject_unknown_names() {
        let s: Scopes = "characters:read characters:write".parse().unwrap();
        assert!(s.contains(Scope::CharactersWrite));
        assert!(!s.contains(Scope::Delete));
        assert_eq!(s.to_string().parse::<Scopes>().unwrap(), s);
        assert_eq!(
            "delete characters:admin".parse::<Scopes>().unwrap_err(),
            "characters:admin".parse::<Scope>().unwrap_err()
        );
        for (k, s) in Scope::ALL.into_iter().enumerate() {
            assert_eq!(s.as_str().parse::<Scope>().unwrap(), s, "scope {k} round-trips by name");
            assert_eq!(s as usize, k);
        }
        assert_eq!(Scopes::all().list().len(), Scope::ALL.len());
    }

    #[test]
    fn wording_is_unchanged() {
        for (k, s) in Scope::ALL.into_iter().enumerate() {
            assert_eq!(s.as_str().as_bytes(), scope::scope_name(s as u16), "scope {k} has its proven name");
        }
        let known: Vec<_> = Scope::ALL.iter().map(|s| s.as_str()).collect();
        assert_eq!(unknown_scope("x"), format!("unknown scope `x`; known scopes: {}", known.join(", ")));
        let s: Scopes = "tokens:read delete".parse().unwrap();
        assert_eq!(s.to_string(), "delete tokens:read");
        assert_eq!(format!("{s:?}"), "Scopes(delete tokens:read)");
        assert_eq!(s.list(), vec![Scope::Delete, Scope::TokensRead]);
        let names = vec!["delete".to_owned(), "tokens:read".to_owned()];
        assert_eq!(Scopes::from_names(&names).unwrap(), s);
        assert_eq!(
            Scopes::from_names(&["delete".to_owned(), "nope".to_owned()]).unwrap_err(),
            "nope".parse::<Scope>().unwrap_err()
        );
        assert_eq!("delete\u{a0}x".parse::<Scopes>().unwrap_err(), unknown_scope("delete\u{a0}x"));
        assert_eq!("  é:x\tdelete".parse::<Scopes>().unwrap_err(), unknown_scope("é:x"));
        let p = principal("delete", Some(&["acc_a", "acc_b"]));
        assert_eq!(p.require(Scope::TokensRead).unwrap_err().message, "token `test` lacks the `tokens:read` scope");
        assert_eq!(p.require_account("acc_c").unwrap_err().message, "token `test` is limited to accounts acc_a, acc_b");
        assert!(p.require_account("acc_b").is_ok() && p.require(Scope::Delete).is_ok());
    }

    #[test]
    fn mint_refusals_are_worded_as_before() {
        let mut parent = principal("characters:read tokens:write", Some(&["acc_a"]));
        let owned = vec!["acc_a".to_owned(), "acc_b".to_owned()];
        let msg = |r: Result<Mint, ApiError>| r.unwrap_err().message;
        assert_eq!(
            msg(request("delete", Some(&["acc_a"])).validate(&parent, 0, &owned, now())),
            "cannot grant scopes this token does not have: delete"
        );
        assert_eq!(
            msg(request("characters:read", Some(&["acc_a"])).validate(&parent, MAX_DEPTH, &owned, now())),
            "delegation chains are limited to 4 levels"
        );
        assert_eq!(
            msg(request("characters:read", Some(&["acc_z"])).validate(&parent, 0, &owned, now())),
            "account `acc_z` not found"
        );
        assert_eq!(
            msg(request("characters:read", Some(&["acc_b"])).validate(&parent, 0, &owned, now())),
            "this token cannot reach account `acc_b`"
        );
        let ttl = MintRequest { expires_in_seconds: Some(1), ..request("characters:read", Some(&["acc_a"])) };
        assert_eq!(msg(ttl.validate(&parent, 0, &owned, now())), "expires_in_seconds must be between 60 and 2592000");
        let blank = MintRequest { label: " \u{3000} ".into(), ..request("characters:read", Some(&["acc_a"])) };
        assert_eq!(msg(blank.validate(&parent, 0, &owned, now())), "label must be 1-100 characters");
        let padded =
            MintRequest { label: "\u{a0} agent é \u{3000}".into(), ..request("characters:read", Some(&["acc_a"])) };
        assert_eq!(padded.validate(&parent, 0, &owned, now()).unwrap().label, "agent é");
        parent.expires_at = Some(Timestamp::from_millis(1_800_000_000_000));
        let long = MintRequest {
            expires_in_seconds: Some(DEFAULT_TTL_SECONDS),
            ..request("characters:read", Some(&["acc_a"]))
        };
        assert_eq!(
            msg(check_mint(
                &long.label,
                long.scopes,
                long.account_ids,
                long.expires_in_seconds,
                &parent,
                0,
                &owned,
                1_799_999_000_000
            )),
            format!(
                "a token cannot outlive the token that mints it; this one expires at {}",
                parent.expires_at.unwrap()
            )
        );
    }

    #[test]
    fn children_cannot_gain_scopes() {
        let parent = principal("characters:read tokens:write", None);
        let err = request("characters:read delete", None).validate(&parent, 0, &[], now()).unwrap_err();
        assert_eq!(err.status, 403);
        assert!(err.message.contains("delete"), "{}", err.message);
    }

    #[test]
    fn children_of_limited_tokens_stay_limited() {
        let owned = vec!["acc_a".to_owned(), "acc_b".to_owned()];
        let parent = principal("characters:read tokens:write", Some(&["acc_a"]));
        assert_eq!(request("characters:read", None).validate(&parent, 1, &owned, now()).unwrap_err().status, 422);
        assert_eq!(
            request("characters:read", Some(&["acc_b"])).validate(&parent, 1, &owned, now()).unwrap_err().status,
            403
        );
        assert!(request("characters:read", Some(&["acc_a"])).validate(&parent, 1, &owned, now()).is_ok());
    }

    #[test]
    fn children_cannot_outlive_parents() {
        let mut parent = principal("characters:read tokens:write", None);
        parent.expires_at = Some(Timestamp::now().plus_millis(60 * 60 * 1000));
        let defaulted = request("characters:read", None).validate(&parent, 1, &[], now()).unwrap();
        assert_eq!(Some(defaulted.expires_at), parent.expires_at, "the default shortens to the parent's expiry");
        let explicit =
            MintRequest { expires_in_seconds: Some(DEFAULT_TTL_SECONDS), ..request("characters:read", None) };
        let err = explicit.validate(&parent, 1, &[], now()).unwrap_err();
        assert!(err.message.contains("outlive"), "{}", err.message);
    }

    #[test]
    fn depth_is_capped() {
        let parent = principal("characters:read tokens:write", None);
        assert!(request("characters:read", None).validate(&parent, MAX_DEPTH, &[], now()).is_err());
    }
}

/// The JSON contract of the hand-written serde impls, captured from the
/// derived ones they replaced: every message must stay word for word.
#[cfg(test)]
mod wire {
    use super::MintRequest;

    #[test]
    fn errors_match_the_derived_impl() {
        for (json, err) in [
            (
                r#"{"label":"a","scopes":["delete"],"x":1}"#,
                r"unknown field `x`, expected one of `label`, `scopes`, `account_ids`, `expires_in_seconds` at line 1 column 36",
            ),
            (r#"{"scopes":["delete"]}"#, r"missing field `label` at line 1 column 21"),
            (
                r#"{"label":"a","scopes":["nope"]}"#,
                r"unknown scope `nope`; known scopes: accounts:read, accounts:write, characters:read, characters:write, delete, tokens:read, tokens:write, audit:read at line 1 column 31",
            ),
            (
                r#"{"label":"a","scopes":["delete"],"expires_in_seconds":-1}"#,
                r"invalid value: integer `-1`, expected u64 at line 1 column 56",
            ),
            (
                r#"{"label":"a","scopes":["delete"],"account_ids":"x"}"#,
                r#"invalid type: string "x", expected a sequence at line 1 column 50"#,
            ),
            (r"7", r"invalid type: integer `7`, expected struct MintRequest at line 1 column 1"),
            (r#"{"label":"a","scopes":["delete"],"label":"b"}"#, r"duplicate field `label` at line 1 column 40"),
        ] {
            assert_eq!(serde_json::from_str::<MintRequest>(json).unwrap_err().to_string(), err, "{json}");
        }
        assert!(
            serde_json::from_str::<MintRequest>(
                r#"{"label":"a","scopes":["delete"],"account_ids":null,"expires_in_seconds":null}"#
            )
            .is_ok()
        );
    }
}
