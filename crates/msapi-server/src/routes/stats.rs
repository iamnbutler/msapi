//! `/v1/characters/{id}/stat`: the character screen's stat window.
//!
//! Every write appends a snapshot, so the history is a record of what the
//! window read at each capture. GET returns the newest.

use rusqlite::{Connection, OptionalExtension, Row, params};
use serde::Serialize;
use serde_json::json;

use msapi_core::stat::{Issue, Severity, StatWindow};
use msapi_core::{Timestamp, api, rules};

use super::{characters, corrupt, page};
use crate::audit::{Ctx, Target, Write};
use crate::auth::{Principal, Scope};
use crate::error::ApiError;
use crate::http::{Request, Response};
use crate::json::merge_patch;

/// One recorded stat window.
#[derive(Serialize, Debug)]
struct Snapshot {
    id: String,
    character_id: String,
    recorded_at: Timestamp,
    /// The audit event that recorded it.
    event_id: String,
    stat: StatWindow,
}

const SELECT: &str = "SELECT id, character_id, recorded_at, event_id, data FROM stat_snapshots";

fn from_row(r: &Row<'_>) -> rusqlite::Result<Snapshot> {
    let data: String = r.get(4)?;
    Ok(Snapshot {
        id: r.get(0)?,
        character_id: r.get(1)?,
        recorded_at: Timestamp::from_millis(r.get(2)?),
        event_id: r.get(3)?,
        stat: serde_json::from_str(&data).map_err(|e| corrupt(4, e.to_string()))?,
    })
}

fn latest(conn: &Connection, character_id: &str) -> rusqlite::Result<Option<Snapshot>> {
    conn.query_row(&format!("{SELECT} WHERE character_id = ?1 ORDER BY id DESC LIMIT 1"), [character_id], from_row)
        .optional()
}

/// `GET /v1/characters/{id}/stat`: the latest window, or `{"stat": null}`.
pub fn get(conn: &Connection, principal: Option<&Principal>, id: &str) -> Result<Response, ApiError> {
    characters::find_readable(conn, principal, id)?;
    Ok(match latest(conn, id)? {
        Some(snapshot) => Response::json(200, &snapshot),
        None => Response::json(200, &json!({ "character_id": id, "stat": null })),
    })
}

/// `PUT /v1/characters/{id}/stat`: records a complete window. Fields left out
/// are recorded as not captured, not as zero.
pub fn replace(conn: &mut Connection, ctx: &Ctx, req: &Request, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersWrite)?;
    characters::find(conn, &ctx.principal, id)?;
    let window: StatWindow = req.json()?;
    record(conn, ctx, id, window)
}

/// `PATCH /v1/characters/{id}/stat`: JSON Merge Patch over the latest window.
/// `captured_at` becomes now unless the patch sets it.
pub fn update(conn: &mut Connection, ctx: &Ctx, req: &Request, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersWrite)?;
    characters::find(conn, &ctx.principal, id)?;
    let patch: serde_json::Value = req.json()?;
    let current = latest(conn, id)?.map(|s| s.stat).unwrap_or_default();
    let mut doc =
        serde_json::to_value(StatWindow { captured_at: None, ..current }).map_err(|_| ApiError::internal())?;
    merge_patch(&mut doc, &patch);
    let window: StatWindow = crate::json::decode(&doc).map_err(|e| ApiError::invalid_json(&e))?;
    record(conn, ctx, id, window)
}

/// Validates and appends a window.
fn record(conn: &mut Connection, ctx: &Ctx, id: &str, mut window: StatWindow) -> Result<Response, ApiError> {
    let now = Timestamp::now();
    let captured_at = *window.captured_at.get_or_insert(now);
    if !rules::captured_at_ok(now.millis(), captured_at.millis()) {
        return Err(ApiError::invalid(format!("captured_at {captured_at} is in the future")));
    }
    let (errors, warnings): (Vec<Issue>, Vec<Issue>) =
        window.check().into_iter().partition(|i| i.severity == Severity::Error);
    if !errors.is_empty() {
        return Err(ApiError::invalid("the stat window is inconsistent").with_details(errors));
    }
    let data = serde_json::to_string(&window).map_err(|_| ApiError::internal())?;
    let before = latest(conn, id)?.map(|s| s.stat);

    let write = Write::begin(conn, ctx)?;
    let snapshot_id = crate::ids::new_id("sts");
    let event_id = Write::reserve_event_id();
    write.execute(
        "INSERT INTO stat_snapshots (id, character_id, captured_at, recorded_at, event_id, data)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
        params![snapshot_id, id, captured_at.millis(), now.millis(), event_id, data],
    )?;
    write.execute("UPDATE characters SET updated_at = ?2 WHERE id = ?1", params![id, now.millis()])?;
    write.commit(Some(event_id.clone()), Target { kind: "character", id }, before.as_ref(), Some(&window))?;

    let snapshot = Snapshot { id: snapshot_id, character_id: id.to_owned(), recorded_at: now, event_id, stat: window };
    Ok(Response::json(200, &json!({ "snapshot": snapshot, "warnings": warnings })))
}

/// `GET /v1/characters/{id}/stat/history?limit=&before=`, newest first.
pub fn history(
    conn: &Connection,
    principal: Option<&Principal>,
    req: &Request,
    id: &str,
) -> Result<Response, ApiError> {
    characters::find_readable(conn, principal, id)?;
    let (limit, before) = page(req)?;
    let mut stmt = conn
        .prepare(&format!("{SELECT} WHERE character_id = ?1 AND (?2 IS NULL OR id < ?2) ORDER BY id DESC LIMIT ?3"))?;
    let snapshots = stmt.query_map(params![id, before, limit], from_row)?.collect::<rusqlite::Result<Vec<_>>>()?;
    let next = api::more_pages(snapshots.len(), limit).then(|| snapshots.last().map(|s| s.id.clone())).flatten();
    Ok(Response::json(200, &json!({ "history": snapshots, "next_before": next })))
}
