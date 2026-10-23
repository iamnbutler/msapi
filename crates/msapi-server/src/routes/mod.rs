//! Routing: path and method to a typed [`Route`], then to its handler.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_map,
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening or `Option` combinators"
)]

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
use crate::http::{self, Request, Response};
use crate::ids;
use msapi_core::api::{self, Route, Routed};
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(feature = "verus")]
use vstd::utf8::encode_utf8;

/// What each of [`api::PLANNED`] is, in the same order.
#[cfg_attr(feature = "verus", verus_verify)]
#[allow(clippy::redundant_static_lifetimes, reason = "Verus needs the lifetime spelled out")]
const PLANNED_WHAT: [&'static str; 7] = [
    "equipment: items, star force, potentials, flames",
    "Arcane and Sacred symbols",
    "hyper stat presets",
    "Inner Ability presets",
    "equipped link skills",
    "V Matrix nodes",
    "HEXA skills and HEXA stat cores",
];

/// Planned resource `k`: its path name and what it is.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        k < 7 ==> (r matches Some((name, _)) && name@ == msapi_core::msg::chars(api::word(api::PLANNED[k as int]))),
        k >= 7 ==> r is None,
))]
fn planned_at(k: usize) -> Option<(&'static str, &'static str)> {
    if k < api::PLANNED.len() { Some((http::word(api::PLANNED[k]), PLANNED_WHAT[k])) } else { None }
}

/// 501 for planned resource `k` of character `id`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 501, r.name == "not_implemented"))]
fn planned_error(k: u8, id: &str) -> ApiError {
    let (resource, what) = match planned_at(k as usize) {
        Some(p) => p,
        None => ("", ""),
    };
    let mut m = String::new();
    m.push_str("`");
    m.push_str(resource);
    m.push_str("` (");
    m.push_str(what);
    m.push_str(") is planned but not built yet; the stat window is at /v1/characters/");
    m.push_str(id);
    m.push_str("/stat");
    ApiError::not_implemented(m)
}

/// Runs an authenticated route; `id` is its path parameter (segment 2), if
/// it has one.
fn run(route: Route, id: &str, conn: &mut Connection, ctx: &Ctx, req: &Request) -> Result<Response, ApiError> {
    match route {
        Route::Me => tokens::me(conn, ctx),
        Route::ListTokens => tokens::list(conn, ctx),
        Route::MintToken => tokens::mint(conn, ctx, req),
        Route::GetToken => tokens::get(conn, ctx, id),
        Route::RevokeToken => tokens::revoke(conn, ctx, id),
        Route::Audit => audit_log::list(conn, ctx, req),
        Route::ListAccounts => accounts::list(conn, ctx),
        Route::CreateAccount => accounts::create(conn, ctx, req),
        Route::GetAccount => accounts::get(conn, ctx, id),
        Route::UpdateAccount => accounts::update(conn, ctx, req, id),
        Route::DeleteAccount => accounts::delete(conn, ctx, id),
        Route::ListAccountCharacters => characters::list(conn, ctx, req, Some(id)),
        Route::CreateCharacter => characters::create(conn, ctx, req, id),
        Route::ListCharacters => characters::list(conn, ctx, req, None),
        Route::GetCharacter => characters::get(conn, ctx, id),
        Route::UpdateCharacter => characters::update(conn, ctx, req, id),
        Route::DeleteCharacter => characters::delete(conn, ctx, id),
        Route::GetStat => stats::get(conn, ctx, id),
        Route::ReplaceStat => stats::replace(conn, ctx, req, id),
        Route::UpdateStat => stats::update(conn, ctx, req, id),
        Route::StatHistory => stats::history(conn, ctx, req, id),
        Route::Planned(k) => {
            characters::find(conn, &ctx.principal, id)?;
            Err(planned_error(k, id))
        }
        // Public and passkey routes are answered before authentication.
        Route::Health
        | Route::Index
        | Route::Docs
        | Route::RefRegions
        | Route::RefWorlds
        | Route::RefClasses
        | Route::RegisterStart
        | Route::RegisterFinish
        | Route::LoginStart
        | Route::LoginFinish => Err(ApiError::not_found_route(&req.path)),
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
        http::method_name(req.method),
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
    let words: Vec<&[u8]> = segments.iter().map(|s| s.as_bytes()).collect();
    let route = match api::route(req.method, &words) {
        Routed::Found(route) => route,
        Routed::NotAllowed => return Err((ApiError::method_not_allowed(), None)),
        Routed::NotFound => return Err((ApiError::not_found_route(&req.path), None)),
    };
    if let Some(response) = meta::public(route) {
        return Ok((response, None));
    }
    if let Some(result) = crate::passkey::handle(conn, req, request_id, route) {
        return result.map(|response| (response, None)).map_err(|e| (e, None));
    }
    let id = segments.get(2).copied().unwrap_or("");
    let principal = auth::authenticate(conn, req.header("authorization")).map_err(|e| (e, None))?;
    let token = Some(principal.token_id.clone());
    let ctx = Ctx {
        principal,
        request_id: request_id.to_owned(),
        method: req.method,
        path: req.path.clone(),
        client: req.client.clone(),
        user_agent: req.header("user-agent").map(str::to_owned),
        action: api::action(route).map_or("", http::word),
    };
    match run(route, id, conn, &ctx, req) {
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
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Ok((limit, before)) =>
                api::page_limit_spec(http::utf8(http::first(req.query@, "limit".spec_bytes()))) == Some(limit)
                && match before {
                    Some(b) => http::first(req.query@, "before".spec_bytes()) == Some(b@),
                    None => http::first(req.query@, "before".spec_bytes()) is None,
                },
            Err(e) => e.status == 400 && api::page_limit_spec(http::utf8(http::first(req.query@, "limit".spec_bytes()))) is None,
        }
))]
fn page(req: &Request) -> Result<(u32, Option<String>), ApiError> {
    let Some(limit) = api::page_limit(req.query("limit").map(str::as_bytes)) else {
        return Err(ApiError::bad_request("limit must be 1-200"));
    };
    // Verus has a spec for `str::to_owned` called directly, not as a function value.
    #[allow(clippy::manual_map, reason = "Verus cannot take `str::to_owned` as a value")]
    let before = match req.query("before") {
        Some(b) => Some(b.to_owned()),
        None => None,
    };
    Ok((limit, before))
}

/// An optional text field as the bytes `msapi_core` checks.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match v {
            Some(s) => r matches Some(b) && b@ == encode_utf8(s@),
            None => r is None,
        }
))]
fn opt_bytes(v: Option<&String>) -> Option<&[u8]> {
    match v {
        // vstd specifies `str::as_bytes`, not `String::as_bytes`.
        #[allow(clippy::redundant_as_str, reason = "Verus needs the `&str` step")]
        Some(s) => Some(s.as_str().as_bytes()),
        None => None,
    }
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
    fn planned_names_line_up_with_core() {
        let names: Vec<_> = (0..8).filter_map(planned_at).map(|(name, _)| name).collect();
        assert_eq!(
            names,
            ["item-equipment", "symbol-equipment", "hyper-stat", "ability", "link-skill", "vmatrix", "hexamatrix"]
        );
        assert_eq!(
            planned_error(1, "chr_1").message,
            "`symbol-equipment` (Arcane and Sacred symbols) is planned but not built yet; the stat window is at /v1/characters/chr_1/stat"
        );
    }
}
