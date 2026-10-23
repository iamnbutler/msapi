//! `GET /v1/audit`: what each token did.

use rusqlite::types::Value as SqlValue;
use rusqlite::{Connection, Row};
use serde::Serialize;
use serde_json::{Value, json};

use msapi_core::Timestamp;
use msapi_core::api;
use msapi_core::policy;

use super::{in_list, page, token_subtree};
use crate::audit::Ctx;
use crate::auth::{Scope, as_bytes};
use crate::error::ApiError;
use crate::http::Request;
use crate::http::Response;

#[derive(Serialize, Debug)]
struct EventView {
    id: String,
    at: Timestamp,
    token_id: String,
    token_label: String,
    request_id: String,
    method: String,
    path: String,
    action: String,
    target_type: Option<String>,
    target_id: Option<String>,
    status: u16,
    client: Option<String>,
    user_agent: Option<String>,
    before: Option<Value>,
    after: Option<Value>,
}

fn parse_json(r: &Row<'_>, column: usize) -> rusqlite::Result<Option<Value>> {
    r.get::<_, Option<String>>(column)?
        .map(|s| serde_json::from_str(&s).map_err(|e| super::corrupt(column, e.to_string())))
        .transpose()
}

fn from_row(r: &Row<'_>) -> rusqlite::Result<EventView> {
    Ok(EventView {
        id: r.get(0)?,
        at: Timestamp::from_millis(r.get(1)?),
        token_id: r.get(2)?,
        token_label: r.get(3)?,
        request_id: r.get(4)?,
        method: r.get(5)?,
        path: r.get(6)?,
        action: r.get(7)?,
        target_type: r.get(8)?,
        target_id: r.get(9)?,
        status: r.get(10)?,
        client: r.get(11)?,
        user_agent: r.get(12)?,
        before: parse_json(r, 13)?,
        after: parse_json(r, 14)?,
    })
}

/// `GET /v1/audit?token_id=&include_descendants=&target_id=&action=&before=&limit=`.
///
/// A root token sees every event of its user. A delegated token sees only
/// events made by itself and the tokens minted below it.
pub fn list(conn: &Connection, ctx: &Ctx, req: &Request) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::AuditRead)?;
    let (limit, before) = page(req)?;
    let mut sql = String::from(
        "SELECT id, at, token_id, token_label, request_id, method, path, action, target_type, target_id, status,
                client, user_agent, before_json, after_json
         FROM audit_events WHERE user_id = ?",
    );
    let mut args = vec![SqlValue::Text(ctx.principal.user_id.clone())];
    let restrict = |sql: &mut String, args: &mut Vec<SqlValue>, ids: &[String]| {
        let (placeholders, values) = in_list(ids);
        sql.push_str(" AND token_id IN (");
        sql.push_str(&placeholders);
        sql.push(')');
        args.extend(values);
    };

    let visible = if ctx.principal.root { None } else { Some(token_subtree(conn, &ctx.principal)?) };
    if let Some(visible) = &visible {
        restrict(&mut sql, &mut args, visible);
    }
    if let Some(token_id) = req.query("token_id") {
        if visible.as_ref().is_some_and(|v| !policy::is_member(token_id.as_bytes(), &as_bytes(v))) {
            return Err(ApiError::not_found(format!("token `{token_id}`")));
        }
        let ids = match api::flag(req.query("include_descendants").map(str::as_bytes)) {
            Some(true) => {
                let principal = crate::auth::Principal { token_id: token_id.to_owned(), ..ctx.principal.clone() };
                token_subtree(conn, &principal)?
            }
            Some(false) => vec![token_id.to_owned()],
            None => return Err(ApiError::bad_request("include_descendants must be true or false")),
        };
        restrict(&mut sql, &mut args, &ids);
    }
    if let Some(target_id) = req.query("target_id") {
        sql.push_str(" AND target_id = ?");
        args.push(SqlValue::Text(target_id.to_owned()));
    }
    if let Some(action) = req.query("action") {
        sql.push_str(" AND action = ?");
        args.push(SqlValue::Text(action.to_owned()));
    }
    if let Some(before) = before {
        sql.push_str(" AND id < ?");
        args.push(SqlValue::Text(before));
    }
    sql.push_str(" ORDER BY id DESC LIMIT ?");
    args.push(SqlValue::Integer(limit.into()));

    let mut stmt = conn.prepare(&sql)?;
    let events = stmt.query_map(rusqlite::params_from_iter(args), from_row)?.collect::<rusqlite::Result<Vec<_>>>()?;
    let next = api::more_pages(events.len(), limit).then(|| events.last().map(|e| e.id.clone())).flatten();
    Ok(Response::json(200, &json!({ "events": events, "next_before": next })))
}
