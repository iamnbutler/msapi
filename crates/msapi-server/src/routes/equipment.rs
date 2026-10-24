//! `/v1/characters/{id}/item-equipment`: the equipment window.
//!
//! Like the stat window, every write appends a snapshot of the whole window,
//! so the history is a record of what was worn at each capture. GET returns
//! the newest.

use rusqlite::{Connection, OptionalExtension, Row, params};
use serde::Serialize;
use serde_json::json;

use msapi_core::equipment::ItemEquipment;
use msapi_core::stat::{Issue, Severity};
use msapi_core::{Timestamp, api, rules};

use super::{characters, corrupt, page};
use crate::audit::{Ctx, Target, Write};
use crate::auth::{Principal, Scope};
use crate::error::ApiError;
use crate::http::{Request, Response};

/// One recorded equipment window.
#[derive(Serialize, Debug)]
struct Snapshot {
    id: String,
    character_id: String,
    recorded_at: Timestamp,
    /// The audit event that recorded it.
    event_id: String,
    equipment: ItemEquipment,
}

const SELECT: &str = "SELECT id, character_id, recorded_at, event_id, data FROM item_equipment_snapshots";

fn from_row(r: &Row<'_>) -> rusqlite::Result<Snapshot> {
    let data: String = r.get(4)?;
    Ok(Snapshot {
        id: r.get(0)?,
        character_id: r.get(1)?,
        recorded_at: Timestamp::from_millis(r.get(2)?),
        event_id: r.get(3)?,
        equipment: serde_json::from_str(&data).map_err(|e| corrupt(4, e.to_string()))?,
    })
}

fn latest(conn: &Connection, character_id: &str) -> rusqlite::Result<Option<Snapshot>> {
    conn.query_row(&format!("{SELECT} WHERE character_id = ?1 ORDER BY id DESC LIMIT 1"), [character_id], from_row)
        .optional()
}

/// `GET /v1/characters/{id}/item-equipment`: the latest window, or
/// `{"equipment": null}`.
pub fn get(conn: &Connection, principal: Option<&Principal>, id: &str) -> Result<Response, ApiError> {
    characters::find_readable(conn, principal, id)?;
    Ok(match latest(conn, id)? {
        Some(snapshot) => Response::json(200, &snapshot),
        None => Response::json(200, &json!({ "character_id": id, "equipment": null })),
    })
}

/// `PUT /v1/characters/{id}/item-equipment`: records the whole window. A
/// slot left out was not captured, or is empty.
pub fn replace(conn: &mut Connection, ctx: &Ctx, req: &Request, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersWrite)?;
    characters::find(conn, &ctx.principal, id)?;
    let mut equipment: ItemEquipment = req.json()?;
    let now = Timestamp::now();
    let captured_at = *equipment.captured_at.get_or_insert(now);
    if !rules::captured_at_ok(now.millis(), captured_at.millis()) {
        return Err(ApiError::invalid(format!("captured_at {captured_at} is in the future")));
    }
    let (errors, warnings): (Vec<Issue>, Vec<Issue>) =
        equipment.check().into_iter().partition(|i| i.severity == Severity::Error);
    if !errors.is_empty() {
        return Err(ApiError::invalid("the equipment window is inconsistent").with_details(errors));
    }
    let data = serde_json::to_string(&equipment).map_err(|_| ApiError::internal())?;
    let before = latest(conn, id)?.map(|s| s.equipment);

    let write = Write::begin(conn, ctx)?;
    let snapshot_id = crate::ids::new_id("eqs");
    let event_id = Write::reserve_event_id();
    write.execute(
        "INSERT INTO item_equipment_snapshots (id, character_id, captured_at, recorded_at, event_id, data)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
        params![snapshot_id, id, captured_at.millis(), now.millis(), event_id, data],
    )?;
    write.execute("UPDATE characters SET updated_at = ?2 WHERE id = ?1", params![id, now.millis()])?;
    write.commit(Some(event_id.clone()), Target { kind: "character", id }, before.as_ref(), Some(&equipment))?;

    let snapshot = Snapshot { id: snapshot_id, character_id: id.to_owned(), recorded_at: now, event_id, equipment };
    Ok(Response::json(200, &json!({ "snapshot": snapshot, "warnings": warnings })))
}

/// `GET /v1/characters/{id}/item-equipment/history?limit=&before=`, newest
/// first.
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
