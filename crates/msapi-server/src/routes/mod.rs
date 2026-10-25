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
mod equipment;
mod meta;
mod sheet;
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
use crate::http::{self, Method, Request, Response};
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
const PLANNED_WHAT: [&'static str; 6] = [
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
        k < 6 ==> (r matches Some((name, _)) && name@ == msapi_core::msg::chars(api::word(api::PLANNED[k as int]))),
        k >= 6 ==> r is None,
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
        Route::UpdateCharacter => characters::update(conn, ctx, req, id),
        Route::DeleteCharacter => characters::delete(conn, ctx, id),
        Route::ReplaceStat => stats::replace(conn, ctx, req, id),
        Route::UpdateStat => stats::update(conn, ctx, req, id),
        Route::ReplaceItemEquipment => equipment::replace(conn, ctx, req, id),
        Route::Planned(k) => {
            characters::find(conn, &ctx.principal, id)?;
            Err(planned_error(k, id))
        }
        // Public, open and passkey routes are answered by their own stages.
        Route::GetCharacter
        | Route::GetStat
        | Route::StatHistory
        | Route::GetItemEquipment
        | Route::ItemEquipmentHistory
        | Route::CharacterSheet
        | Route::Health
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

/// Runs a route that reads a character, for its owner or, if the character
/// is public, for anyone: `principal` is `None` without a token.
fn read(
    route: Route,
    id: &str,
    conn: &Connection,
    principal: Option<&Principal>,
    req: &Request,
) -> Result<Response, ApiError> {
    match route {
        Route::GetCharacter => characters::get(conn, principal, id),
        Route::GetStat => stats::get(conn, principal, id),
        Route::StatHistory => stats::history(conn, principal, req, id),
        Route::GetItemEquipment => equipment::get(conn, principal, id),
        Route::ItemEquipmentHistory => equipment::history(conn, principal, req, id),
        Route::CharacterSheet => sheet::get(conn, principal, id),
        _ => Err(ApiError::not_found_route(&req.path)),
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

/// Who answers a routed request.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stage {
    /// Public reference data, answered without a token.
    Public,
    /// A passkey ceremony, answered without a token.
    Passkey,
    /// A character read: a token is checked if sent, but none is needed for
    /// a public character.
    Open,
    /// Everything else: authenticate, then [`run`].
    Authed,
}

/// Which [`Stage`] answers `route`: [`stage_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == stage_spec(route)))]
const fn stage(route: Route) -> Stage {
    match route {
        Route::Health | Route::Index | Route::Docs | Route::RefRegions | Route::RefWorlds | Route::RefClasses => {
            Stage::Public
        }
        Route::RegisterStart | Route::RegisterFinish | Route::LoginStart | Route::LoginFinish => Stage::Passkey,
        Route::GetCharacter
        | Route::GetStat
        | Route::StatHistory
        | Route::GetItemEquipment
        | Route::ItemEquipmentHistory
        | Route::CharacterSheet => Stage::Open,
        _ => Stage::Authed,
    }
}

/// A request's route, its path parameter (segment 2, or `""`) and who
/// answers it.
#[cfg_attr(feature = "verus", verus_verify)]
struct Plan<'a> {
    route: Route,
    id: &'a str,
    stage: Stage,
}

/// Routes `method` and `path`: the proven [`api::route`] on the path's
/// [`http::segments`], or the 405 or 404 it gives.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures ({
        let segs = http::segments_spec(path.spec_bytes(), seq![]);
        match r {
            Ok(p) => (exists|w: Seq<&[u8]>| #[trigger] http::views(w) == segs
                        && api::route_spec(method, w) == Routed::Found(p.route))
                && p.stage == stage_spec(p.route)
                && p.id.spec_bytes() == (if segs.len() > 2 { segs[2] } else { Seq::<u8>::empty() }),
            Err(e) => (exists|w: Seq<&[u8]>| #[trigger] http::views(w) == segs && match api::route_spec(method, w) {
                Routed::NotAllowed => e.status == 405,
                Routed::NotFound => e.status == 404 && e.message@ == "route "@ + path@ + " not found"@,
                Routed::Found(_) => false,
            }),
        }
    }),
))]
fn plan(method: Method, path: &str) -> Result<Plan<'_>, ApiError> {
    let segments = http::segments(path);
    let words = http::words(&segments);
    proof! {
        assert(http::views(words@) =~= segments@.map_values(|x: &str| x.spec_bytes()));
    }
    let route = match api::route(method, &words) {
        Routed::Found(route) => route,
        Routed::NotAllowed => return Err(ApiError::method_not_allowed()),
        Routed::NotFound => return Err(ApiError::not_found_route(path)),
    };
    let id = if segments.len() > 2 {
        segments[2]
    } else {
        proof! { reveal_strlit(""); }
        ""
    };
    Ok(Plan { route, id, stage: stage(route) })
}

/// The audit context of an authenticated request to `route`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r.principal == principal,
        r.request_id@ == request_id@,
        r.method == req.method,
        r.path@ == req.path@,
        r.action@ == match api::action_spec(route) {
            Some(w) => msapi_core::msg::chars(api::word(w)),
            None => Seq::<char>::empty(),
        },
))]
fn context(principal: Principal, request_id: &str, req: &Request, route: Route) -> Ctx {
    let client = match &req.client {
        Some(c) => Some(c.clone()),
        None => None,
    };
    let user_agent = match req.header("user-agent") {
        Some(u) => Some(u.to_owned()),
        None => None,
    };
    let action = match api::action(route) {
        Some(w) => http::word(w),
        None => {
            proof! { reveal_strlit(""); }
            ""
        }
    };
    Ctx {
        principal,
        request_id: request_id.to_owned(),
        method: req.method,
        path: req.path.clone(),
        client,
        user_agent,
        action,
    }
}

/// Whether a refusal is recorded in the audit trail: a 403 to a write.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (status == 403 && api::writes(method))))]
const fn audits_refusal(status: u16, method: Method) -> bool {
    status == 403 && method.is_write()
}

/// Answers a request along its proven [`plan`]: the public and passkey
/// handlers, a character [`read`] with any token sent, or authentication and
/// then [`run`], auditing a refused write.
fn dispatch(conn: &mut Connection, req: &Request, request_id: &str) -> Result<Outcome, (ApiError, Option<String>)> {
    let plan = plan(req.method, &req.path).map_err(|e| (e, None))?;
    match plan.stage {
        Stage::Public => match meta::public(plan.route) {
            Some(response) => Ok((response, None)),
            None => Err((ApiError::not_found_route(&req.path), None)),
        },
        Stage::Passkey => match crate::passkey::handle(conn, req, request_id, plan.route) {
            Some(Ok(response)) => Ok((response, None)),
            Some(Err(e)) => Err((e, None)),
            None => Err((ApiError::not_found_route(&req.path), None)),
        },
        Stage::Open => {
            // A bad token is refused even here, so a client learns it has expired.
            let principal = match req.header("authorization") {
                Some(header) => Some(auth::authenticate(conn, Some(header)).map_err(|e| (e, None))?),
                None => None,
            };
            let token = principal.as_ref().map(|p| p.token_id.clone());
            match read(plan.route, plan.id, conn, principal.as_ref(), req) {
                Ok(response) => Ok((response, token)),
                Err(err) => Err((err, token)),
            }
        }
        Stage::Authed => {
            let principal = auth::authenticate(conn, req.header("authorization")).map_err(|e| (e, None))?;
            let token = Some(principal.token_id.clone());
            let ctx = context(principal, request_id, req, plan.route);
            match run(plan.route, plan.id, conn, &ctx, req) {
                Ok(response) => Ok((response, token)),
                Err(err) => {
                    if audits_refusal(err.status, req.method) {
                        audit::record_refused(conn, &ctx, err.status);
                    }
                    Err((err, token))
                }
            }
        }
    }
}

#[cfg(feature = "verus")]
verus! {

/// The public routes are answered without a token, as are the passkey
/// ceremonies; the character reads take a token if one is sent; every other
/// route authenticates first.
spec fn stage_spec(route: Route) -> Stage {
    match route {
        Route::Health | Route::Index | Route::Docs | Route::RefRegions | Route::RefWorlds | Route::RefClasses => Stage::Public,
        Route::RegisterStart | Route::RegisterFinish | Route::LoginStart | Route::LoginFinish => Stage::Passkey,
        Route::GetCharacter | Route::GetStat | Route::StatHistory | Route::GetItemEquipment | Route::ItemEquipmentHistory
        | Route::CharacterSheet => Stage::Open,
        _ => Stage::Authed,
    }
}

} // verus!

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
        let names: Vec<_> = (0..7).filter_map(planned_at).map(|(name, _)| name).collect();
        assert_eq!(names, ["symbol-equipment", "hyper-stat", "ability", "link-skill", "vmatrix", "hexamatrix"]);
        assert_eq!(
            planned_error(0, "chr_1").message,
            "`symbol-equipment` (Arcane and Sacred symbols) is planned but not built yet; the stat window is at /v1/characters/chr_1/stat"
        );
    }
}
