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

use std::fmt;
use std::str::FromStr;

use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};

use msapi_core::Timestamp;
use msapi_core::api;
use msapi_core::policy::{self, AccountCheck, Link, MintRefusal, Parent};
use msapi_core::scope;

use crate::error::ApiError;
use crate::ids;

/// One permission.
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

    /// The wire name, e.g. `"characters:write"`, from the proven table in
    /// [`scope::scope_name`] (whose names are ASCII).
    #[must_use]
    pub fn as_str(self) -> &'static str {
        std::str::from_utf8(scope::scope_name(self as u16)).unwrap_or_default()
    }
}

impl FromStr for Scope {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        scope::scope_index(s.as_bytes()).map(|k| Self::ALL[usize::from(k)]).ok_or_else(|| unknown_scope(s))
    }
}

fn unknown_scope(name: &str) -> String {
    let known: Vec<_> = Scope::ALL.iter().map(|s| s.as_str()).collect();
    format!("unknown scope `{name}`; known scopes: {}", known.join(", "))
}

/// A set of scopes.
#[derive(Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Scopes(u16);

impl Scopes {
    /// Every scope, as a root token has.
    #[must_use]
    pub fn all() -> Self {
        Self::ALL_SET
    }

    const ALL_SET: Self = Self(policy::first(scope::COUNT));

    /// Whether `scope` is in the set.
    #[must_use]
    pub const fn contains(self, scope: Scope) -> bool {
        policy::contains(self.0, scope as u16)
    }

    /// Whether every scope in `self` is also in `other`.
    #[must_use]
    pub const fn is_subset_of(self, other: Self) -> bool {
        policy::is_subset(self.0, other.0)
    }

    /// The scopes in `self` that are not in `other`.
    #[must_use]
    pub const fn minus(self, other: Self) -> Self {
        Self(policy::minus(self.0, other.0))
    }

    /// The scopes, in declaration order.
    pub fn iter(self) -> impl Iterator<Item = Scope> {
        Scope::ALL.into_iter().filter(move |s| self.contains(*s))
    }
}

impl FromIterator<Scope> for Scopes {
    fn from_iter<I: IntoIterator<Item = Scope>>(iter: I) -> Self {
        Self(iter.into_iter().fold(0, |acc, s| policy::with(acc, s as u16)))
    }
}

impl fmt::Display for Scopes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Scope names are ASCII, so this never fails.
        f.write_str(std::str::from_utf8(&scope::format_scopes(self.0)).map_err(|_| fmt::Error)?)
    }
}

impl fmt::Debug for Scopes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Scopes({self})")
    }
}

impl FromStr for Scopes {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The offending token is bounded by ASCII whitespace or the ends, so
        // slicing there is on a char boundary.
        scope::parse_scopes(s.as_bytes()).map(Self).map_err(|(start, end)| unknown_scope(&s[start..end]))
    }
}

impl Serialize for Scopes {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter().map(Scope::as_str))
    }
}

impl<'de> Deserialize<'de> for Scopes {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let names = Vec::<String>::deserialize(deserializer)?;
        names.iter().map(|n| n.parse::<Scope>()).collect::<Result<Self, _>>().map_err(serde::de::Error::custom)
    }
}

/// Who is making a request, as established by their token.
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

impl Principal {
    /// Fails unless the token has `scope`.
    pub fn require(&self, scope: Scope) -> Result<(), ApiError> {
        if self.scopes.contains(scope) {
            Ok(())
        } else {
            Err(ApiError::forbidden(format!("token `{}` lacks the `{}` scope", self.label, scope.as_str())))
        }
    }

    /// Fails unless the token may touch `account_id`.
    pub fn require_account(&self, account_id: &str) -> Result<(), ApiError> {
        let allowed = self.account_ids.as_deref().map(as_bytes);
        if policy::reaches(account_id.as_bytes(), allowed.as_deref()) {
            return Ok(());
        }
        let ids = self.account_ids.as_deref().unwrap_or_default().join(", ");
        Err(ApiError::forbidden(format!("token `{}` is limited to accounts {ids}", self.label)))
    }

    /// Whether the token may touch `account_id`.
    #[must_use]
    pub fn reaches_account(&self, account_id: &str) -> bool {
        self.require_account(account_id).is_ok()
    }
}

/// Views IDs as the byte strings `msapi_core::policy` compares.
pub(crate) fn as_bytes(ids: &[String]) -> Vec<&[u8]> {
    ids.iter().map(String::as_bytes).collect()
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
pub const DEFAULT_TTL_SECONDS: u64 = policy::DEFAULT_TTL_SECONDS;
/// Longest lifetime of a delegated token: thirty days.
pub const MAX_TTL_SECONDS: u64 = policy::MAX_TTL_SECONDS;
/// Deepest delegation chain below a root token.
pub const MAX_DEPTH: u64 = policy::MAX_DEPTH;

/// `POST /v1/tokens` body.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MintRequest {
    /// Shown in listings and copied into every audit event, e.g. `"ChatGPT import"`.
    pub label: String,
    /// The scopes to grant; must be a subset of the caller's.
    pub scopes: Scopes,
    /// Accounts to limit the token to. Required if the caller is itself limited.
    #[serde(default)]
    pub account_ids: Option<Vec<String>>,
    /// Lifetime in seconds: at most thirty days, and never past the caller's own
    /// expiry. Defaults to a day, or to the caller's expiry if that is sooner.
    #[serde(default)]
    pub expires_in_seconds: Option<u64>,
}

/// A validated mint, ready to insert.
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

impl MintRequest {
    /// Checks the request against what `parent` may delegate.
    ///
    /// `depth` is how many delegations already sit above `parent`
    /// (0 for a root token). `owned_accounts` are the user's account IDs.
    pub fn validate(self, parent: &Principal, depth: u64, owned_accounts: &[String]) -> Result<Mint, ApiError> {
        let label = api::name_in(self.label.as_bytes(), 1, 100)
            .and_then(|(a, b)| self.label.get(a..b))
            .ok_or_else(|| ApiError::invalid("label must be 1-100 characters"))?
            .to_owned();
        // The rules themselves are in `msapi_core::policy`, checked by Verus; this
        // gathers their inputs and words their refusals.
        let owned = as_bytes(owned_accounts);
        let allowed = parent.account_ids.as_deref().map(as_bytes);
        let checks: Option<Vec<AccountCheck>> =
            self.account_ids.as_deref().map(|ids| policy::account_checks(&as_bytes(ids), &owned, allowed.as_deref()));
        let decision = policy::check_mint(
            Parent {
                scopes: parent.scopes.0,
                depth,
                limited: parent.account_ids.is_some(),
                expires_at: parent.expires_at.map(Timestamp::millis),
            },
            self.scopes.0,
            checks.as_deref(),
            self.expires_in_seconds,
            Timestamp::now().millis(),
        );
        let account = |i: usize| self.account_ids.as_ref().and_then(|ids| ids.get(i)).map_or("", String::as_str);
        let expires_at = decision.map_err(|refusal| match refusal {
            MintRefusal::NoScopes => ApiError::invalid("grant at least one scope"),
            MintRefusal::ExcessScopes(excess) => {
                ApiError::forbidden(format!("cannot grant scopes this token does not have: {}", Scopes(excess)))
            }
            MintRefusal::TooDeep => ApiError::forbidden(format!("delegation chains are limited to {MAX_DEPTH} levels")),
            MintRefusal::MustListAccounts => ApiError::invalid(
                "this token is limited to specific accounts, so the new token must list account_ids too",
            ),
            MintRefusal::EmptyAccounts => {
                ApiError::invalid("account_ids must not be empty; omit it to allow every account")
            }
            MintRefusal::UnknownAccount(i) => ApiError::not_found(format!("account `{}`", account(i))),
            MintRefusal::UnreachableAccount(i) => {
                ApiError::forbidden(format!("this token cannot reach account `{}`", account(i)))
            }
            MintRefusal::TtlOutOfRange => ApiError::invalid(format!(
                "expires_in_seconds must be between {} and {MAX_TTL_SECONDS}",
                policy::MIN_TTL_SECONDS
            )),
            MintRefusal::OutlivesParent => ApiError::invalid(format!(
                "a token cannot outlive the token that mints it; this one expires at {}",
                parent.expires_at.map(|t| t.to_string()).unwrap_or_default()
            )),
        })?;

        Ok(Mint {
            label,
            scopes: self.scopes,
            account_ids: self.account_ids,
            expires_at: Timestamp::from_millis(expires_at),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(Scopes::all().iter().count(), Scope::ALL.len());
    }

    #[test]
    fn children_cannot_gain_scopes() {
        let parent = principal("characters:read tokens:write", None);
        let err = request("characters:read delete", None).validate(&parent, 0, &[]).unwrap_err();
        assert_eq!(err.status, 403);
        assert!(err.message.contains("delete"), "{}", err.message);
    }

    #[test]
    fn children_of_limited_tokens_stay_limited() {
        let owned = vec!["acc_a".to_owned(), "acc_b".to_owned()];
        let parent = principal("characters:read tokens:write", Some(&["acc_a"]));
        assert_eq!(request("characters:read", None).validate(&parent, 1, &owned).unwrap_err().status, 422);
        assert_eq!(request("characters:read", Some(&["acc_b"])).validate(&parent, 1, &owned).unwrap_err().status, 403);
        assert!(request("characters:read", Some(&["acc_a"])).validate(&parent, 1, &owned).is_ok());
    }

    #[test]
    fn children_cannot_outlive_parents() {
        let mut parent = principal("characters:read tokens:write", None);
        parent.expires_at = Some(Timestamp::now().plus_millis(60 * 60 * 1000));
        let defaulted = request("characters:read", None).validate(&parent, 1, &[]).unwrap();
        assert_eq!(Some(defaulted.expires_at), parent.expires_at, "the default shortens to the parent's expiry");
        let explicit =
            MintRequest { expires_in_seconds: Some(DEFAULT_TTL_SECONDS), ..request("characters:read", None) };
        let err = explicit.validate(&parent, 1, &[]).unwrap_err();
        assert!(err.message.contains("outlive"), "{}", err.message);
    }

    #[test]
    fn depth_is_capped() {
        let parent = principal("characters:read tokens:write", None);
        assert!(request("characters:read", None).validate(&parent, MAX_DEPTH, &[]).is_err());
    }
}
