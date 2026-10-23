//! Routing: path and method to a typed [`Route`], then to its handler.

mod accounts;
mod audit_log;
mod characters;
mod meta;
mod stats;
mod tokens;

use std::time::Instant;

use rusqlite::Connection;
use rusqlite::types::Value as SqlValue;
use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::audit::{self, Ctx};
use crate::auth::{self, Principal};
use crate::error::ApiError;
use crate::http::{Method, Request, Response};
use crate::ids;

/// Character resources the Nexon Open API has that msapi will add later.
const PLANNED: &[(&str, &str)] = &[
    ("item-equipment", "equipment: items, star force, potentials, flames"),
    ("symbol-equipment", "Arcane and Sacred symbols"),
    ("hyper-stat", "hyper stat presets"),
    ("ability", "Inner Ability presets"),
    ("link-skill", "equipped link skills"),
    ("vmatrix", "V Matrix nodes"),
    ("hexamatrix", "HEXA skills and HEXA stat cores"),
];

/// Every authenticated route, with its path parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Route<'a> {
    Me,
    ListTokens,
    MintToken,
    GetToken(&'a str),
    RevokeToken(&'a str),
    Audit,
    ListAccounts,
    CreateAccount,
    GetAccount(&'a str),
    UpdateAccount(&'a str),
    DeleteAccount(&'a str),
    ListAccountCharacters(&'a str),
    CreateCharacter(&'a str),
    ListCharacters,
    GetCharacter(&'a str),
    UpdateCharacter(&'a str),
    DeleteCharacter(&'a str),
    GetStat(&'a str),
    ReplaceStat(&'a str),
    UpdateStat(&'a str),
    StatHistory(&'a str),
    Planned(&'a str, &'static str),
}

/// Picks the route for `method` among those a path supports, or 405.
fn by_method<'a>(method: Method, options: &[(Method, Route<'a>)]) -> Result<Route<'a>, ApiError> {
    options.iter().find(|(m, _)| *m == method).map(|(_, r)| *r).ok_or_else(ApiError::method_not_allowed)
}

impl<'a> Route<'a> {
    fn parse(method: Method, segments: &[&'a str]) -> Result<Option<Self>, ApiError> {
        use Method::{Delete, Get, Patch, Post, Put};
        let route = match *segments {
            ["v1", "me"] => by_method(method, &[(Get, Self::Me)])?,
            ["v1", "tokens"] => by_method(method, &[(Get, Self::ListTokens), (Post, Self::MintToken)])?,
            ["v1", "tokens", id] => by_method(method, &[(Get, Self::GetToken(id)), (Delete, Self::RevokeToken(id))])?,
            ["v1", "audit"] => by_method(method, &[(Get, Self::Audit)])?,
            ["v1", "accounts"] => by_method(method, &[(Get, Self::ListAccounts), (Post, Self::CreateAccount)])?,
            ["v1", "accounts", id] => by_method(
                method,
                &[(Get, Self::GetAccount(id)), (Patch, Self::UpdateAccount(id)), (Delete, Self::DeleteAccount(id))],
            )?,
            ["v1", "accounts", id, "characters"] => {
                by_method(method, &[(Get, Self::ListAccountCharacters(id)), (Post, Self::CreateCharacter(id))])?
            }
            ["v1", "characters"] => by_method(method, &[(Get, Self::ListCharacters)])?,
            ["v1", "characters", id] => by_method(
                method,
                &[
                    (Get, Self::GetCharacter(id)),
                    (Patch, Self::UpdateCharacter(id)),
                    (Delete, Self::DeleteCharacter(id)),
                ],
            )?,
            ["v1", "characters", id, "stat"] => by_method(
                method,
                &[(Get, Self::GetStat(id)), (Put, Self::ReplaceStat(id)), (Patch, Self::UpdateStat(id))],
            )?,
            ["v1", "characters", id, "stat", "history"] => by_method(method, &[(Get, Self::StatHistory(id))])?,
            ["v1", "characters", id, resource] => match PLANNED.iter().find(|(name, _)| *name == resource) {
                Some((name, _)) => by_method(method, &[(Get, Self::Planned(id, name))])?,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        Ok(Some(route))
    }

    /// The audit action name.
    const fn action(self) -> &'static str {
        match self {
            Self::Me => "me.read",
            Self::ListTokens | Self::GetToken(_) => "token.read",
            Self::MintToken => "token.mint",
            Self::RevokeToken(_) => "token.revoke",
            Self::Audit => "audit.read",
            Self::ListAccounts | Self::GetAccount(_) => "account.read",
            Self::CreateAccount => "account.create",
            Self::UpdateAccount(_) => "account.update",
            Self::DeleteAccount(_) => "account.delete",
            Self::ListAccountCharacters(_) | Self::ListCharacters | Self::GetCharacter(_) | Self::Planned(..) => {
                "character.read"
            }
            Self::CreateCharacter(_) => "character.create",
            Self::UpdateCharacter(_) => "character.update",
            Self::DeleteCharacter(_) => "character.delete",
            Self::GetStat(_) | Self::StatHistory(_) => "stat.read",
            Self::ReplaceStat(_) => "stat.replace",
            Self::UpdateStat(_) => "stat.update",
        }
    }

    fn run(self, conn: &mut Connection, ctx: &Ctx, req: &Request) -> Result<Response, ApiError> {
        match self {
            Self::Me => tokens::me(conn, ctx),
            Self::ListTokens => tokens::list(conn, ctx),
            Self::MintToken => tokens::mint(conn, ctx, req),
            Self::GetToken(id) => tokens::get(conn, ctx, id),
            Self::RevokeToken(id) => tokens::revoke(conn, ctx, id),
            Self::Audit => audit_log::list(conn, ctx, req),
            Self::ListAccounts => accounts::list(conn, ctx),
            Self::CreateAccount => accounts::create(conn, ctx, req),
            Self::GetAccount(id) => accounts::get(conn, ctx, id),
            Self::UpdateAccount(id) => accounts::update(conn, ctx, req, id),
            Self::DeleteAccount(id) => accounts::delete(conn, ctx, id),
            Self::ListAccountCharacters(id) => characters::list(conn, ctx, req, Some(id)),
            Self::CreateCharacter(id) => characters::create(conn, ctx, req, id),
            Self::ListCharacters => characters::list(conn, ctx, req, None),
            Self::GetCharacter(id) => characters::get(conn, ctx, id),
            Self::UpdateCharacter(id) => characters::update(conn, ctx, req, id),
            Self::DeleteCharacter(id) => characters::delete(conn, ctx, id),
            Self::GetStat(id) => stats::get(conn, ctx, id),
            Self::ReplaceStat(id) => stats::replace(conn, ctx, req, id),
            Self::UpdateStat(id) => stats::update(conn, ctx, req, id),
            Self::StatHistory(id) => stats::history(conn, ctx, req, id),
            Self::Planned(id, resource) => {
                characters::find(conn, &ctx.principal, id)?;
                let what = PLANNED.iter().find(|(name, _)| *name == resource).map_or("", |(_, what)| *what);
                Err(ApiError::not_implemented(format!(
                    "`{resource}` ({what}) is planned but not built yet; the stat window is at /v1/characters/{id}/stat"
                )))
            }
        }
    }
}

/// Handles one request. Never panics on bad input; every failure becomes an
/// error response carrying the request ID.
pub fn handle(conn: &mut Connection, req: &Request) -> Response {
    let started = Instant::now();
    let request_id = ids::new_id("req");
    let (response, token) = match dispatch(conn, req, &request_id) {
        Ok((response, token)) => (response, token),
        Err((err, token)) => (err.to_response(), token),
    };
    eprintln!(
        "{request_id} {} {} {} {}ms token={}",
        req.method.as_str(),
        req.path,
        response.status,
        started.elapsed().as_millis(),
        token.as_deref().unwrap_or("-")
    );
    response.with_header("x-request-id", request_id)
}

type Outcome = (Response, Option<String>);

fn dispatch(conn: &mut Connection, req: &Request, request_id: &str) -> Result<Outcome, (ApiError, Option<String>)> {
    let segments: Vec<&str> = req.path.split('/').filter(|s| !s.is_empty()).collect();
    if let Some(response) = meta::public(req.method, &segments).map_err(|e| (e, None))? {
        return Ok((response, None));
    }
    let route = Route::parse(req.method, &segments)
        .map_err(|e| (e, None))?
        .ok_or_else(|| (ApiError::not_found(format!("route {}", req.path)), None))?;
    let principal = auth::authenticate(conn, req.header("authorization")).map_err(|e| (e, None))?;
    let token = Some(principal.token_id.clone());
    let ctx = Ctx {
        principal,
        request_id: request_id.to_owned(),
        method: req.method,
        path: req.path.clone(),
        client: req.client.clone(),
        user_agent: req.header("user-agent").map(str::to_owned),
        action: route.action(),
    };
    match route.run(conn, &ctx, req) {
        Ok(response) => Ok((response, token)),
        Err(err) => {
            if err.status == 403 && req.method.is_write() {
                audit::record_refused(conn, &ctx, err.status);
            }
            Err((err, token))
        }
    }
}

/// `limit` (1-200, default 50) and `before` (an ID cursor) query parameters.
fn page(req: &Request) -> Result<(u32, Option<String>), ApiError> {
    // Unparseable limits become 0, which `page_size` refuses.
    let requested = req.query("limit").map(|s| s.parse::<u64>().unwrap_or(0));
    let limit = msapi_core::policy::page_size(requested).ok_or_else(|| ApiError::bad_request("limit must be 1-200"))?;
    Ok((limit, req.query("before").map(str::to_owned)))
}

/// A unit-like enum's wire string, for storing in a TEXT column.
fn enum_to_sql<T: Serialize>(value: &T) -> Option<String> {
    serde_json::to_value(value).ok().and_then(|v| v.as_str().map(str::to_owned))
}

/// Parses a TEXT column written by [`enum_to_sql`].
fn enum_from_sql<T: DeserializeOwned>(column: usize, text: Option<String>) -> rusqlite::Result<Option<T>> {
    text.map(|s| {
        serde_json::from_value(serde_json::Value::String(s))
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(column, rusqlite::types::Type::Text, Box::new(e)))
    })
    .transpose()
}

/// A failed conversion of a stored value.
fn corrupt(column: usize, message: String) -> rusqlite::Error {
    rusqlite::Error::FromSqlConversionFailure(column, rusqlite::types::Type::Text, message.into())
}

/// Whether `err` is a UNIQUE constraint failure.
fn is_unique_violation(err: &rusqlite::Error) -> bool {
    matches!(err, rusqlite::Error::SqliteFailure(e, _) if e.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_UNIQUE)
}

/// The IDs of `principal`'s own token and every token minted below it.
fn token_subtree(conn: &Connection, principal: &Principal) -> rusqlite::Result<Vec<String>> {
    let mut stmt = conn.prepare(
        "WITH RECURSIVE sub(id) AS (
             SELECT id FROM tokens WHERE id = ?1
             UNION ALL
             SELECT t.id FROM tokens t JOIN sub ON t.parent_id = sub.id
         )
         SELECT id FROM sub",
    )?;
    stmt.query_map([&principal.token_id], |r| r.get(0))?.collect()
}

/// `?, ?, ?` for `n` parameters, and the parameters as SQL values.
fn in_list(values: &[String]) -> (String, Vec<SqlValue>) {
    let placeholders = vec!["?"; values.len()].join(", ");
    (placeholders, values.iter().cloned().map(SqlValue::Text).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn routes_parse_with_params_and_405_on_wrong_method() {
        assert_eq!(
            Route::parse(Method::Patch, &["v1", "characters", "chr_x"]).unwrap(),
            Some(Route::UpdateCharacter("chr_x"))
        );
        assert_eq!(
            Route::parse(Method::Get, &["v1", "characters", "chr_x", "hyper-stat"]).unwrap(),
            Some(Route::Planned("chr_x", "hyper-stat"))
        );
        assert_eq!(Route::parse(Method::Put, &["v1", "characters"]).unwrap_err().status, 405);
        assert_eq!(Route::parse(Method::Get, &["v1", "nope"]).unwrap(), None);
        assert_eq!(Route::parse(Method::Get, &["v1", "characters", "chr_x", "nope"]).unwrap(), None);
    }
}
