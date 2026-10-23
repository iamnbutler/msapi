//! `/v1/accounts`: game accounts, one per region login.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_map,
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening or `Option` combinators"
)]

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
#[cfg(feature = "verus")]
use vstd::prelude::*;

/// The editable fields of an account.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct AccountInput {
    region: Region,
    label: Option<String>,
    notes: Option<String>,
}

impl AccountInput {
    /// The proven [`check_account`] on this input's fields.
    #[cfg_attr(feature = "verus", verus_verify)]
    fn validate(&self) -> Result<(), ApiError> {
        check_account(self.region, self.label.as_ref(), self.notes.as_ref())
    }
}

// Verus checks `AccountInput` and cannot take serde's derives on a checked
// type, so it goes through derived twins with the same wire format and the
// same error messages.

impl Serialize for AccountInput {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        #[derive(Serialize)]
        struct Wire<'a> {
            region: Region,
            label: &'a Option<String>,
            notes: &'a Option<String>,
        }
        Wire { region: self.region, label: &self.label, notes: &self.notes }.serialize(s)
    }
}

impl<'de> Deserialize<'de> for AccountInput {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct AccountInput {
            region: Region,
            #[serde(default)]
            label: Option<String>,
            #[serde(default)]
            notes: Option<String>,
        }
        let AccountInput { region, label, notes } = AccountInput::deserialize(d)?;
        Ok(Self { region, label, notes })
    }
}

/// Checks an account's fields: its region must be catalogued, and the label
/// and notes within the proven [`api::account_fields`] limits.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Err(e) ==> e.status == 422 && e.name == "invalid",
))]
fn check_account(region: Region, label: Option<&String>, notes: Option<&String>) -> Result<(), ApiError> {
    if !region.is_supported() {
        let mut m = String::new();
        m.push_str("region `");
        m.push_str(region.as_str());
        m.push_str("` is not supported yet: its worlds are not catalogued (see /v1/ref/regions)");
        return Err(ApiError::invalid(m));
    }
    match api::account_fields(opt_bytes(label), opt_bytes(notes)) {
        Ok(()) => Ok(()),
        Err(AccountRefusal::LabelTooLong) => Err(ApiError::invalid("label must be at most 100 characters")),
        Err(AccountRefusal::NotesTooLong) => Err(ApiError::invalid("notes must be at most 4000 characters")),
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

/// The JSON contract of the hand-written serde impls, captured from the
/// derived ones they replaced: every message must stay word for word.
#[cfg(test)]
mod wire {
    use super::AccountInput;

    #[test]
    fn errors_match_the_derived_impl() {
        for (json, err) in [
            (
                r#"{"region":"gms","x":1}"#,
                r"unknown field `x`, expected one of `region`, `label`, `notes` at line 1 column 19",
            ),
            (r#"{"label":"a"}"#, r"missing field `region` at line 1 column 13"),
            (
                r#"{"region":"zzz"}"#,
                r"unknown variant `zzz`, expected one of `gms`, `kms`, `msea`, `tms`, `jms` at line 1 column 15",
            ),
            (r#"{"region":5}"#, r"expected value at line 1 column 11"),
            (r"[]", r"invalid length 0, expected struct AccountInput with 3 elements at line 1 column 2"),
            (r#"{"region":"gms","label":3}"#, r"invalid type: integer `3`, expected a string at line 1 column 25"),
            (r#"{"region":"gms","region":"kms"}"#, r"duplicate field `region` at line 1 column 24"),
        ] {
            assert_eq!(serde_json::from_str::<AccountInput>(json).unwrap_err().to_string(), err, "{json}");
        }
    }

    #[test]
    fn round_trips() {
        let input: AccountInput = serde_json::from_str(r#"{"region":"gms","label":"x"}"#).unwrap();
        let out = serde_json::to_string(&input).unwrap();
        assert_eq!(out, r#"{"region":"gms","label":"x","notes":null}"#);
        assert_eq!(serde_json::to_string(&serde_json::from_str::<AccountInput>(&out).unwrap()).unwrap(), out);
    }
}
