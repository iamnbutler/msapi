//! `/v1/characters` and `/v1/accounts/{id}/characters`.
//!
//! Field names follow the Nexon Open API's `character/basic` (`character_name`,
//! `world_name`, `character_class`, `character_level`, …) so code written
//! against it reads the same here, but values are typed rather than strings.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_map,
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening or `Option` combinators"
)]

use rusqlite::{Connection, OptionalExtension, Row, params};
use serde::{Deserialize, Serialize};
use serde_json::json;

use msapi_core::api::{self, CharacterRefusal};
use msapi_core::class::Class;
use msapi_core::{
    CharacterName, ClassLevel, DataCenter, ExpRate, Gender, JobType, Level, Liberation, Region, Timestamp, World,
    WorldType, class, world,
};

use super::{corrupt, enum_from_sql, enum_to_sql, in_list, is_unique_violation, opt_bytes};
use crate::audit::{Ctx, Target, Write};
use crate::auth::{Principal, Scope};
use crate::error::ApiError;
use crate::http::{Request, Response};
use crate::ids;
use crate::json::merge_patch;
#[cfg(feature = "verus")]
use vstd::prelude::*;

/// The fields a client sets. `world_name` and `character_class` accept any
/// spelling the reference data resolves (`"Night Walker"`, `"night-walker"`).
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
struct CharacterInput {
    character_name: CharacterName,
    world_name: String,
    character_class: String,
    character_level: Level,
    #[serde(default)]
    character_class_level: Option<ClassLevel>,
    #[serde(default)]
    character_exp: Option<u64>,
    #[serde(default)]
    character_exp_rate: Option<ExpRate>,
    #[serde(default)]
    character_gender: Option<Gender>,
    #[serde(default)]
    character_guild_name: Option<String>,
    #[serde(default)]
    popularity: Option<i32>,
    #[serde(default)]
    liberation: Option<Liberation>,
    #[serde(default)]
    character_image: Option<String>,
    #[serde(default)]
    notes: Option<String>,
}

/// A [`CharacterInput`] whose references resolved and whose values are in range.
struct Valid {
    input: CharacterInput,
    world: &'static World,
    class: &'static Class,
    exp: Option<i64>,
}

impl CharacterInput {
    /// The proven [`check_character`] on this input's fields.
    fn validate(self, region: Region) -> Result<Valid, ApiError> {
        let (world, class, exp) = check_character(
            region,
            &self.character_name,
            &self.world_name,
            &self.character_class,
            self.character_exp_rate,
            self.character_exp,
            self.character_guild_name.as_ref(),
            self.character_image.as_ref(),
            self.notes.as_ref(),
        )?;
        Ok(Valid { input: self, world, class, exp })
    }
}

/// Resolves a character's world and class and checks its values against
/// the region's naming rules and the proven [`api::character_fields`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r matches Err(e) ==> e.status == 422 && e.name == "invalid"))]
#[allow(clippy::too_many_arguments, reason = "the fields of a `CharacterInput`, which Verus cannot see")]
#[allow(clippy::type_complexity, reason = "the parts of a `Valid` besides its input")]
fn check_character(
    region: Region,
    name: &CharacterName,
    world_name: &str,
    class_name: &str,
    exp_rate: Option<ExpRate>,
    exp: Option<u64>,
    guild: Option<&String>,
    image: Option<&String>,
    notes: Option<&String>,
) -> Result<(&'static World, &'static Class, Option<i64>), ApiError> {
    if let Err(m) = name.check_region(region) {
        return Err(ApiError::invalid(m));
    }
    let Some(world) = world::find(region, world_name) else {
        {
            let worlds = world::in_region(region);
            let mut m = String::new();
            m.push_str("unknown ");
            m.push_str(region.as_str());
            m.push_str(" world `");
            m.push_str(world_name);
            m.push_str("`; expected one of ");
            let mut i: usize = 0;
            #[cfg_attr(feature = "verus", verus_spec(invariant i <= worlds@.len(), decreases worlds@.len() - i))]
            while i < worlds.len() {
                if i > 0 {
                    m.push_str(", ");
                }
                m.push_str(worlds[i].name);
                i += 1;
            }
            return Err(ApiError::invalid(m));
        }
    };
    let Some(class) = class::find(class_name) else {
        {
            let mut m = String::new();
            m.push_str("unknown class `");
            m.push_str(class_name);
            m.push_str("`; see /v1/ref/classes");
            return Err(ApiError::invalid(m));
        }
    };
    let raw_rate = match exp_rate {
        Some(r) => Some(r.raw()),
        None => None,
    };
    match api::character_fields(raw_rate, exp, opt_bytes(guild), opt_bytes(image), opt_bytes(notes)) {
        Ok(exp) => Ok((world, class, exp)),
        Err(refusal) => Err(ApiError::invalid(match refusal {
            CharacterRefusal::ExpRate => {
                let mut m = String::new();
                m.push_str("character_exp_rate must be in [0, 100), got ");
                if let Some(r) = exp_rate {
                    m.push_str(r.text().as_str());
                }
                m
            }
            CharacterRefusal::ExpTooLarge => "character_exp is too large".to_owned(),
            CharacterRefusal::GuildTooLong => "character_guild_name must be at most 32 characters".to_owned(),
            CharacterRefusal::ImageTooLong => "character_image must be at most 4096 characters".to_owned(),
            CharacterRefusal::NotesTooLong => "notes must be at most 4000 characters".to_owned(),
            CharacterRefusal::ImageNotHttps => "character_image must be an https:// URL".to_owned(),
        })),
    }
}

/// A character as the API returns it.
#[derive(Serialize, Debug)]
pub struct CharacterView {
    id: String,
    account_id: String,
    region: Region,
    character_name: CharacterName,
    world_name: &'static str,
    world_type: WorldType,
    data_center: DataCenter,
    character_class: &'static str,
    character_class_id: &'static str,
    job_type: JobType,
    character_class_level: Option<ClassLevel>,
    character_level: Level,
    character_exp: Option<u64>,
    character_exp_rate: Option<ExpRate>,
    character_gender: Option<Gender>,
    character_guild_name: Option<String>,
    popularity: Option<i32>,
    liberation: Option<Liberation>,
    character_image: Option<String>,
    notes: Option<String>,
    /// When the latest stat window was captured; `null` if none has been recorded.
    stat_captured_at: Option<Timestamp>,
    created_at: Timestamp,
    updated_at: Timestamp,
}

impl CharacterView {
    fn to_input(&self) -> CharacterInput {
        CharacterInput {
            character_name: self.character_name.clone(),
            world_name: self.world_name.to_owned(),
            character_class: self.character_class.to_owned(),
            character_level: self.character_level,
            character_class_level: self.character_class_level,
            character_exp: self.character_exp,
            character_exp_rate: self.character_exp_rate,
            character_gender: self.character_gender,
            character_guild_name: self.character_guild_name.clone(),
            popularity: self.popularity,
            liberation: self.liberation,
            character_image: self.character_image.clone(),
            notes: self.notes.clone(),
        }
    }
}

const SELECT: &str = "SELECT c.id, c.account_id, a.region, c.character_name, c.world_key, c.class_id, c.class_level,
        c.level, c.exp, c.exp_rate, c.gender, c.guild_name, c.popularity, c.liberation, c.image_url, c.notes,
        c.created_at, c.updated_at,
        (SELECT s.captured_at FROM stat_snapshots s WHERE s.character_id = c.id ORDER BY s.id DESC LIMIT 1)
    FROM characters c JOIN accounts a ON a.id = c.account_id";

fn from_row(r: &Row<'_>) -> rusqlite::Result<CharacterView> {
    let region: Region = enum_from_sql(2, Some(r.get(2)?))?.ok_or_else(|| corrupt(2, "missing region".into()))?;
    let world_key: String = r.get(4)?;
    let world = world::by_key(&world_key).ok_or_else(|| corrupt(4, format!("unknown world `{world_key}`")))?;
    let class_id: String = r.get(5)?;
    let class = class::find(&class_id).ok_or_else(|| corrupt(5, format!("unknown class `{class_id}`")))?;
    let name: String = r.get(3)?;
    Ok(CharacterView {
        id: r.get(0)?,
        account_id: r.get(1)?,
        region,
        character_name: CharacterName::new(name).map_err(|e| corrupt(3, e))?,
        world_name: world.name,
        world_type: world.world_type,
        data_center: world.data_center,
        character_class: class.name,
        character_class_id: class.id,
        job_type: class.job_type,
        character_class_level: r
            .get::<_, Option<i64>>(6)?
            .map(ClassLevel::new)
            .transpose()
            .map_err(|e| corrupt(6, e))?,
        character_level: Level::new(r.get(7)?).map_err(|e| corrupt(7, e))?,
        character_exp: r.get::<_, Option<i64>>(8)?.map(|v| u64::try_from(v).unwrap_or(0)),
        character_exp_rate: r.get::<_, Option<i64>>(9)?.map(ExpRate::from_raw),
        character_gender: enum_from_sql(10, r.get(10)?)?,
        character_guild_name: r.get(11)?,
        popularity: r.get(12)?,
        liberation: enum_from_sql(13, r.get(13)?)?,
        character_image: r.get(14)?,
        notes: r.get(15)?,
        created_at: Timestamp::from_millis(r.get(16)?),
        updated_at: Timestamp::from_millis(r.get(17)?),
        stat_captured_at: r.get::<_, Option<i64>>(18)?.map(Timestamp::from_millis),
    })
}

/// Loads a character the caller owns and its token may reach.
pub fn find(conn: &Connection, principal: &Principal, id: &str) -> Result<CharacterView, ApiError> {
    let view = conn
        .query_row(&format!("{SELECT} WHERE c.id = ?1 AND c.user_id = ?2"), params![id, principal.user_id], from_row)
        .optional()?
        .ok_or_else(|| ApiError::not_found_id("character", id))?;
    principal.require_account(&view.account_id)?;
    Ok(view)
}

fn account_region(conn: &Connection, ctx: &Ctx, account_id: &str) -> Result<Region, ApiError> {
    let region: Option<String> = conn
        .query_row(
            "SELECT region FROM accounts WHERE id = ?1 AND user_id = ?2",
            params![account_id, ctx.principal.user_id],
            |r| r.get(0),
        )
        .optional()?;
    let region = region.ok_or_else(|| ApiError::not_found_id("account", account_id))?;
    ctx.principal.require_account(account_id)?;
    enum_from_sql(0, Some(region))?.ok_or_else(ApiError::internal)
}

/// 409 for a second character named `name` in `world`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 409, r.name == "conflict"))]
fn duplicate(name: &CharacterName, world: &World) -> ApiError {
    let mut m = String::new();
    m.push_str("you already have a character named `");
    m.push_str(name.as_str());
    m.push_str("` in ");
    m.push_str(world.name);
    ApiError::conflict(m)
}

/// `GET /v1/characters` and `GET /v1/accounts/{id}/characters`, optionally `?world=`.
pub fn list(conn: &Connection, ctx: &Ctx, req: &Request, account_id: Option<&str>) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersRead)?;
    let mut sql = format!("{SELECT} WHERE c.user_id = ?");
    let mut args = vec![rusqlite::types::Value::Text(ctx.principal.user_id.clone())];
    if let Some(account_id) = account_id {
        account_region(conn, ctx, account_id)?;
        sql.push_str(" AND c.account_id = ?");
        args.push(rusqlite::types::Value::Text(account_id.to_owned()));
    } else if let Some(allowed) = &ctx.principal.account_ids {
        let (placeholders, values) = in_list(allowed);
        sql.push_str(" AND c.account_id IN (");
        sql.push_str(&placeholders);
        sql.push(')');
        args.extend(values);
    }
    if let Some(name) = req.query("world") {
        let world = msapi_core::world::WORLDS
            .iter()
            .find(|w| w.key.eq_ignore_ascii_case(name) || w.name.eq_ignore_ascii_case(name))
            .ok_or_else(|| ApiError::bad_request(format!("unknown world `{name}`")))?;
        sql.push_str(" AND c.world_key = ?");
        args.push(rusqlite::types::Value::Text(world.key.to_owned()));
    }
    sql.push_str(" ORDER BY c.level DESC, c.character_name");
    let mut stmt = conn.prepare(&sql)?;
    let characters =
        stmt.query_map(rusqlite::params_from_iter(args), from_row)?.collect::<rusqlite::Result<Vec<_>>>()?;
    Ok(Response::json(200, &json!({ "character_list": characters })))
}

/// `GET /v1/characters/{id}`.
pub fn get(conn: &Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersRead)?;
    Ok(Response::json(200, &find(conn, &ctx.principal, id)?))
}

/// `POST /v1/accounts/{id}/characters`.
pub fn create(conn: &mut Connection, ctx: &Ctx, req: &Request, account_id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersWrite)?;
    let region = account_region(conn, ctx, account_id)?;
    let valid = req.json::<CharacterInput>()?.validate(region)?;
    let id = ids::new_id("chr");
    let now = Timestamp::now().millis();

    let write = Write::begin(conn, ctx)?;
    let inserted = write.execute(
        "INSERT INTO characters (id, user_id, account_id, character_name, name_key, world_key, class_id, class_level,
             level, exp, exp_rate, gender, guild_name, popularity, liberation, image_url, notes, created_at, updated_at)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?18)",
        params![
            id,
            ctx.principal.user_id,
            account_id,
            valid.input.character_name.as_str(),
            valid.input.character_name.as_str().to_lowercase(),
            valid.world.key,
            valid.class.id,
            valid.input.character_class_level.map(i64::from),
            i64::from(valid.input.character_level),
            valid.exp,
            valid.input.character_exp_rate.map(ExpRate::raw),
            valid.input.character_gender.as_ref().and_then(enum_to_sql),
            valid.input.character_guild_name,
            valid.input.popularity,
            valid.input.liberation.as_ref().and_then(enum_to_sql),
            valid.input.character_image,
            valid.input.notes,
            now,
        ],
    );
    match inserted {
        Err(e) if is_unique_violation(&e) => return Err(duplicate(&valid.input.character_name, valid.world)),
        other => other?,
    };
    let view = find(write.tx(), &ctx.principal, &id)?;
    write.commit(None, Target { kind: "character", id: &id }, None::<&()>, Some(&view))?;
    Ok(Response::json(201, &view))
}

/// `PATCH /v1/characters/{id}`: JSON Merge Patch over the [`CharacterInput`] fields.
pub fn update(conn: &mut Connection, ctx: &Ctx, req: &Request, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::CharactersWrite)?;
    let patch: serde_json::Value = req.json()?;
    let before = find(conn, &ctx.principal, id)?;
    let mut doc = serde_json::to_value(before.to_input()).map_err(|_| ApiError::internal())?;
    merge_patch(&mut doc, &patch);
    let valid =
        crate::json::decode::<CharacterInput>(&doc).map_err(|e| ApiError::invalid_json(&e))?.validate(before.region)?;

    let write = Write::begin(conn, ctx)?;
    let updated = write.execute(
        "UPDATE characters SET character_name = ?2, name_key = ?3, world_key = ?4, class_id = ?5, class_level = ?6,
             level = ?7, exp = ?8, exp_rate = ?9, gender = ?10, guild_name = ?11, popularity = ?12, liberation = ?13,
             image_url = ?14, notes = ?15, updated_at = ?16
         WHERE id = ?1",
        params![
            id,
            valid.input.character_name.as_str(),
            valid.input.character_name.as_str().to_lowercase(),
            valid.world.key,
            valid.class.id,
            valid.input.character_class_level.map(i64::from),
            i64::from(valid.input.character_level),
            valid.exp,
            valid.input.character_exp_rate.map(ExpRate::raw),
            valid.input.character_gender.as_ref().and_then(enum_to_sql),
            valid.input.character_guild_name,
            valid.input.popularity,
            valid.input.liberation.as_ref().and_then(enum_to_sql),
            valid.input.character_image,
            valid.input.notes,
            Timestamp::now().millis(),
        ],
    );
    match updated {
        Err(e) if is_unique_violation(&e) => return Err(duplicate(&valid.input.character_name, valid.world)),
        other => other?,
    };
    let after = find(write.tx(), &ctx.principal, id)?;
    write.commit(None, Target { kind: "character", id }, Some(&before), Some(&after))?;
    Ok(Response::json(200, &after))
}

/// `DELETE /v1/characters/{id}`: deletes the character and its stat history.
pub fn delete(conn: &mut Connection, ctx: &Ctx, id: &str) -> Result<Response, ApiError> {
    ctx.principal.require(Scope::Delete)?;
    let before = find(conn, &ctx.principal, id)?;
    let write = Write::begin(conn, ctx)?;
    write.execute("DELETE FROM characters WHERE id = ?1", params![id])?;
    write.commit(None, Target { kind: "character", id }, Some(&before), None::<&()>)?;
    Ok(Response::no_content())
}
