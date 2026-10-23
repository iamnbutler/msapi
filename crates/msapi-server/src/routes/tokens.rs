//! `/v1/me` and `/v1/tokens`.

use rusqlite::{Connection, OptionalExtension, Row, params};
use serde::Serialize;
use serde_json::json;

use msapi_core::Timestamp;

use super::{corrupt, token_subtree};
use crate::audit::{Ctx, Target, Write};
use crate::auth::{MintRequest, Scope, Scopes};
use crate::error::ApiError;
use crate::http::{Request, Response};
use crate::ids;

/// A token as listings show it. Never includes the secret.
#[derive(Serialize, Debug)]
pub struct TokenView {
    id: String,
    label: String,
    kind: &'static str,
    parent_id: Option<String>,
    scopes: Scopes,
    account_ids: Option<Vec<String>>,
    created_at: Timestamp,
    expires_at: Option<Timestamp>,
    revoked_at: Option<Timestamp>,
    last_used_at: Option<Timestamp>,
}

const SELECT: &str =
    "SELECT id, label, parent_id, scopes, account_ids, created_at, expires_at, revoked_at, last_used_at
                      FROM tokens";

fn from_row(r: &Row<'_>) -> rusqlite::Result<TokenView> {
    let parent_id: Option<String> = r.get(2)?;
    let scopes: String = r.get(3)?;
    let accounts: Option<String> = r.get(4)?;
    Ok(TokenView {
        id: r.get(0)?,
        label: r.get(1)?,
        kind: if parent_id.is_some() { "delegated" } else { "root" },
        parent_id,
        scopes: scopes.parse().map_err(|e| corrupt(3, e))?,
        account_ids: accounts
            .as_deref()
            .map(serde_json::from_str)
            .transpose()
            .map_err(|e| corrupt(4, e.to_string()))?,
        created_at: Timestamp::from_millis(r.get(5)?),
        expires_at: r.get::<_, Option<i64>>(6)?.map(Timestamp::from_millis),
        revoked_at: r.get::<_, Option<i64>>(7)?.map(Timestamp::from_millis),
        last_used_at: r.get::<_, Option<i64>>(8)?.map(Timestamp::from_millis),
    })
}

fn load(conn: &Connection, id: &str) -> rusqlite::Result<Option<TokenView>> {
    conn.query_row(&format!("{SELECT} WHERE id = ?1"), [id], from_row).optional()
}

/// Tokens the caller may see and revoke: all of the user's for a root token,
/// otherwise the caller's own token and everything minted below it.
fn visible(conn: &Connection, ctx: &Ctx) -> rusqlite::Result<Vec<String>> {
    if ctx.principal.root {
        let mut stmt = conn.prepare("SELECT id FROM tokens WHERE user_id = ?1")?;
        stmt.query_map([&ctx.principal.user_id], |r| r.get(0))?.collect()
    } else {
        token_subtree(conn, &ctx.principal)
    }
}

/// `GET /v1/me`: who the token belongs to and what it can do.
pub fn me(conn: &Connection, ctx: &Ctx) -> Result<Response, ApiError> {
    let (name, created): (String, i64) =
        conn.query_row("SELECT display_name, created_at FROM users WHERE id = ?1", [&ctx.principal.user_id], |r| {
            Ok((r.get(0)?, r.get(1)?))
        })?;
    let token = load(conn, &ctx.principal.token_id)?.ok_or_else(ApiError::internal)?;
    Ok(Response::json(
        200,
        &json!({
            "user": { "id": ctx.principal.user_id, "display_name": name, "created_at": Timestamp::from_millis(created) },
            "token": token,
        }),
    ))
}

/// `GET /v1/tokens`.
pub fn list(conn: &Connection, ctx: &Ctx) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::TokensRead)?;
    let ids = visible(conn, ctx)?;
    let mut tokens = Vec::with_capacity(ids.len());
    for id in &ids {
        tokens.extend(load(conn, id)?);
    }
    tokens.sort_by(|a, b| b.id.cmp(&a.id));
    Ok(Response::json(200, &json!({ "tokens": tokens })))
}

/// `GET /v1/tokens/{id}`.
pub fn get(conn: &Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    if id != ctx.principal.token_id {
        ctx.principal.require(Scope::TokensRead)?;
    }
    if !visible(conn, ctx)?.iter().any(|v| v == id) {
        return Err(ApiError::not_found(format!("token `{id}`")));
    }
    let token = load(conn, id)?.ok_or_else(|| ApiError::not_found(format!("token `{id}`")))?;
    Ok(Response::json(200, &token))
}

/// `POST /v1/tokens`: mint a delegated token below the caller's.
pub fn mint(conn: &mut Connection, ctx: &Ctx, req: &Request) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::TokensWrite)?;
    let request: MintRequest = req.json()?;

    let depth: u32 = conn.query_row(
        "WITH RECURSIVE up(id, parent_id) AS (
             SELECT id, parent_id FROM tokens WHERE id = ?1
             UNION ALL
             SELECT t.id, t.parent_id FROM tokens t JOIN up ON t.id = up.parent_id
         )
         SELECT COUNT(*) - 1 FROM up",
        [&ctx.principal.token_id],
        |r| r.get(0),
    )?;
    let owned: Vec<String> = {
        let mut stmt = conn.prepare("SELECT id FROM accounts WHERE user_id = ?1")?;
        stmt.query_map([&ctx.principal.user_id], |r| r.get(0))?.collect::<rusqlite::Result<_>>()?
    };
    let mint = request.validate(&ctx.principal, depth as usize, &owned)?;

    let secret = ids::new_token_secret();
    let id = ids::new_id("tok");
    let write = Write::begin(conn, ctx)?;
    write.tx().execute(
        "INSERT INTO tokens (id, user_id, parent_id, label, scopes, account_ids, secret_hash, created_at, expires_at)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)",
        params![
            id,
            ctx.principal.user_id,
            ctx.principal.token_id,
            mint.label,
            mint.scopes.to_string(),
            mint.account_ids.as_ref().map(|a| serde_json::to_string(a).unwrap_or_default()),
            ids::hash_token(&secret),
            Timestamp::now().millis(),
            mint.expires_at.millis(),
        ],
    )?;
    let view = write.tx().query_row(&format!("{SELECT} WHERE id = ?1"), [&id], from_row)?;
    write.commit(None, Target { kind: "token", id: &id }, None::<&()>, Some(&view))?;

    Ok(Response::json(
        201,
        &json!({
            "token": secret,
            "note": "This is the only time the token is shown. Store it now.",
            "details": view,
        }),
    ))
}

/// `DELETE /v1/tokens/{id}`: revoke a token and everything minted from it.
///
/// Any token may revoke itself. Revoking others needs `tokens:write`, and a
/// delegated token can only revoke tokens below it, never its parent.
pub fn revoke(conn: &mut Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    if id != ctx.principal.token_id {
        ctx.principal.require(Scope::TokensWrite)?;
    }
    if !visible(conn, ctx)?.iter().any(|v| v == id) {
        return Err(ApiError::not_found(format!("token `{id}`")));
    }
    let before = load(conn, id)?.ok_or_else(|| ApiError::not_found(format!("token `{id}`")))?;
    let now = Timestamp::now().millis();

    let write = Write::begin(conn, ctx)?;
    let revoked: Vec<String> = {
        let mut stmt = write.tx().prepare(
            "WITH RECURSIVE sub(id) AS (
                 SELECT id FROM tokens WHERE id = ?1
                 UNION ALL
                 SELECT t.id FROM tokens t JOIN sub ON t.parent_id = sub.id
             )
             UPDATE tokens SET revoked_at = ?2
             WHERE id IN (SELECT id FROM sub) AND revoked_at IS NULL
             RETURNING id",
        )?;
        stmt.query_map(params![id, now], |r| r.get(0))?.collect::<rusqlite::Result<_>>()?
    };
    let after = json!({ "revoked": revoked });
    write.commit(None, Target { kind: "token", id }, Some(&before), Some(&after))?;
    Ok(Response::json(200, &after))
}
