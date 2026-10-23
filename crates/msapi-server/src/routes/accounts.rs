//! `/v1/accounts`: game accounts, one per region login.

use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use serde_json::json;

use msapi_core::api::{self, AccountRefusal};
use msapi_core::{DataCenter, Region, Timestamp, WorldType, world};

use super::enum_from_sql;
use super::opt_bytes;
use crate::audit::{Ctx, Target, Write};
use crate::auth::Scope;
use crate::error::ApiError;
use crate::http::{Request, Response};
use crate::ids;
use crate::json::merge_patch;

/// The editable fields of an account.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct AccountInput {
    region: Region,
    #[serde(default)]
    label: Option<String>,
    #[serde(default)]
    notes: Option<String>,
}

impl AccountInput {
    fn validate(&self) -> Result<(), ApiError> {
        if !self.region.is_supported() {
            return Err(ApiError::invalid(format!(
                "region `{}` is not supported yet: its worlds are not catalogued (see /v1/ref/regions)",
                self.region
            )));
        }
        api::account_fields(opt_bytes(self.label.as_ref()), opt_bytes(self.notes.as_ref())).map_err(|refusal| {
            match refusal {
                AccountRefusal::LabelTooLong => ApiError::invalid("label must be at most 100 characters"),
                AccountRefusal::NotesTooLong => ApiError::invalid("notes must be at most 4000 characters"),
            }
        })
    }
}

/// One world the account has characters in.
#[derive(Serialize, Debug)]
struct WorldSummary {
    world_name: &'static str,
    world_type: WorldType,
    data_center: DataCenter,
    character_count: u32,
}

/// A character as an account lists it. Named after the Open API's `character_list`.
#[derive(Serialize, Debug)]
struct CharacterSummary {
    id: String,
    character_name: String,
    world_name: &'static str,
    character_class: &'static str,
    character_level: u16,
}

#[derive(Serialize, Debug)]
struct AccountView {
    id: String,
    #[serde(flatten)]
    input: AccountInput,
    created_at: Timestamp,
    updated_at: Timestamp,
    worlds: Vec<WorldSummary>,
    character_list: Vec<CharacterSummary>,
}

/// Loads an account the caller owns and its token may reach.
fn load(conn: &Connection, ctx: &Ctx, id: &str) -> Result<AccountView, ApiError> {
    let row = conn
        .query_row(
            "SELECT region, label, notes, created_at, updated_at FROM accounts WHERE id = ?1 AND user_id = ?2",
            params![id, ctx.principal.user_id],
            |r| {
                Ok((
                    enum_from_sql::<Region>(0, Some(r.get(0)?))?,
                    r.get::<_, Option<String>>(1)?,
                    r.get::<_, Option<String>>(2)?,
                    r.get::<_, i64>(3)?,
                    r.get::<_, i64>(4)?,
                ))
            },
        )
        .optional()?;
    let Some((Some(region), label, notes, created, updated)) = row else {
        return Err(ApiError::not_found_id("account", id));
    };
    ctx.principal.require_account(id)?;

    let mut stmt = conn.prepare(
        "SELECT id, character_name, world_key, class_id, level FROM characters WHERE account_id = ?1
         ORDER BY level DESC, character_name",
    )?;
    let mut characters = Vec::new();
    for row in stmt.query_map([id], |r| {
        Ok((r.get::<_, String>(0)?, r.get::<_, String>(1)?, r.get::<_, String>(2)?, r.get::<_, String>(3)?, r.get(4)?))
    })? {
        let (cid, name, world_key, class_id, level) = row?;
        let w = world::by_key(&world_key).ok_or_else(ApiError::internal)?;
        let c = msapi_core::class::find(&class_id).ok_or_else(ApiError::internal)?;
        characters.push((
            w,
            CharacterSummary {
                id: cid,
                character_name: name,
                world_name: w.name,
                character_class: c.name,
                character_level: level,
            },
        ));
    }

    let mut worlds: Vec<WorldSummary> = Vec::new();
    for (w, _) in &characters {
        match worlds.iter_mut().find(|s| s.world_name == w.name) {
            Some(s) => s.character_count += 1,
            None => worlds.push(WorldSummary {
                world_name: w.name,
                world_type: w.world_type,
                data_center: w.data_center,
                character_count: 1,
            }),
        }
    }

    Ok(AccountView {
        id: id.to_owned(),
        input: AccountInput { region, label, notes },
        created_at: Timestamp::from_millis(created),
        updated_at: Timestamp::from_millis(updated),
        worlds,
        character_list: characters.into_iter().map(|(_, c)| c).collect(),
    })
}

/// `GET /v1/accounts`.
pub fn list(conn: &Connection, ctx: &Ctx) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::AccountsRead)?;
    let ids: Vec<String> = {
        let mut stmt = conn.prepare("SELECT id FROM accounts WHERE user_id = ?1 ORDER BY id")?;
        stmt.query_map([&ctx.principal.user_id], |r| r.get(0))?.collect::<rusqlite::Result<_>>()?
    };
    let accounts = ids
        .iter()
        .filter(|id| ctx.principal.reaches_account(id))
        .map(|id| load(conn, ctx, id))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Response::json(200, &json!({ "account_list": accounts })))
}

/// `GET /v1/accounts/{id}`.
pub fn get(conn: &Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::AccountsRead)?;
    Ok(Response::json(200, &load(conn, ctx, id)?))
}

/// `POST /v1/accounts`.
pub fn create(conn: &mut Connection, ctx: &Ctx, req: &Request) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::AccountsWrite)?;
    if ctx.principal.account_ids.is_some() {
        return Err(ApiError::forbidden("a token limited to specific accounts cannot create accounts"));
    }
    let input: AccountInput = req.json()?;
    input.validate()?;
    let id = ids::new_id("acc");
    let now = Timestamp::now().millis();
    let write = Write::begin(conn, ctx)?;
    write.execute(
        "INSERT INTO accounts (id, user_id, region, label, notes, created_at, updated_at) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?6)",
        params![id, ctx.principal.user_id, input.region.as_str(), input.label, input.notes, now],
    )?;
    let view = load(write.tx(), ctx, &id)?;
    write.commit(None, Target { kind: "account", id: &id }, None::<&()>, Some(&view))?;
    Ok(Response::json(201, &view))
}

/// `PATCH /v1/accounts/{id}`: JSON Merge Patch over `region`, `label` and `notes`.
pub fn update(conn: &mut Connection, ctx: &Ctx, req: &Request, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::AccountsWrite)?;
    let patch: serde_json::Value = req.json()?;
    let before = load(conn, ctx, id)?;
    let mut doc = serde_json::to_value(&before.input).map_err(|_| ApiError::internal())?;
    merge_patch(&mut doc, &patch);
    let input: AccountInput = crate::json::decode(&doc).map_err(|e| ApiError::invalid_json(&e))?;
    if input.region != before.input.region {
        return Err(ApiError::invalid("an account's region cannot change; create a new account instead"));
    }
    input.validate()?;

    let write = Write::begin(conn, ctx)?;
    write.execute(
        "UPDATE accounts SET label = ?2, notes = ?3, updated_at = ?4 WHERE id = ?1",
        params![id, input.label, input.notes, Timestamp::now().millis()],
    )?;
    let after = load(write.tx(), ctx, id)?;
    write.commit(None, Target { kind: "account", id }, Some(&before), Some(&after))?;
    Ok(Response::json(200, &after))
}

/// `DELETE /v1/accounts/{id}`: deletes the account, its characters and their history.
pub fn delete(conn: &mut Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::Delete)?;
    let before = load(conn, ctx, id)?;
    let write = Write::begin(conn, ctx)?;
    write.execute("DELETE FROM accounts WHERE id = ?1", params![id])?;
    write.commit(None, Target { kind: "account", id }, Some(&before), None::<&()>)?;
    Ok(Response::no_content())
}
