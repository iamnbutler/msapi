//! The audit trail.
//!
//! [`Write`] wraps a database transaction and has exactly one way to commit:
//! [`Write::commit`], which inserts the audit event in the same transaction.
//! Dropping a `Write` rolls back. So any code that changes data necessarily
//! records who did it, with which token, and what the data looked like before
//! and after.

use rusqlite::{Connection, Transaction, TransactionBehavior, params};
use serde::Serialize;

use msapi_core::Timestamp;

use crate::auth::Principal;
use crate::http::Method;
use crate::ids;

/// Everything about a request that an audit event records.
#[derive(Clone, Debug)]
pub struct Ctx {
    /// Who is calling.
    pub principal: Principal,
    /// This request's ID, also returned as `x-request-id`.
    pub request_id: String,
    /// The method.
    pub method: Method,
    /// The path.
    pub path: String,
    /// The client address, when known.
    pub client: Option<String>,
    /// The `user-agent` header.
    pub user_agent: Option<String>,
    /// The route's action name, e.g. `"character.update"`.
    pub action: &'static str,
}

/// What an event is about.
#[derive(Clone, Copy, Debug)]
pub struct Target<'a> {
    /// The kind of resource, e.g. `"character"`.
    pub kind: &'static str,
    /// Its ID.
    pub id: &'a str,
}

/// A write in progress. Commit with [`Write::commit`]; drop to roll back.
pub struct Write<'c> {
    tx: Transaction<'c>,
    ctx: &'c Ctx,
}

impl<'c> Write<'c> {
    /// Starts a write. `IMMEDIATE` takes the write lock up front, so two
    /// writers queue on `busy_timeout` instead of deadlocking on upgrade.
    pub fn begin(conn: &'c mut Connection, ctx: &'c Ctx) -> rusqlite::Result<Self> {
        Ok(Self { tx: conn.transaction_with_behavior(TransactionBehavior::Immediate)?, ctx })
    }

    /// The transaction, for the write's own statements.
    #[must_use]
    pub fn tx(&self) -> &Transaction<'c> {
        &self.tx
    }

    /// Reserves the ID the audit event will have, so rows written in this
    /// transaction (such as stat snapshots) can point at it.
    #[must_use]
    pub fn reserve_event_id() -> String {
        ids::new_id("evt")
    }

    /// Records the event and commits everything. Returns the event ID.
    pub fn commit(
        self,
        event_id: Option<String>,
        target: Target<'_>,
        before: Option<&impl Serialize>,
        after: Option<&impl Serialize>,
    ) -> rusqlite::Result<String> {
        let id = event_id.unwrap_or_else(Self::reserve_event_id);
        insert(
            &self.tx,
            &id,
            self.ctx,
            Some(target),
            200,
            before.and_then(to_json).as_deref(),
            after.and_then(to_json).as_deref(),
        )?;
        self.tx.commit()?;
        Ok(id)
    }
}

fn to_json(value: &impl Serialize) -> Option<String> {
    serde_json::to_string(value).ok()
}

fn insert(
    conn: &Connection,
    id: &str,
    ctx: &Ctx,
    target: Option<Target<'_>>,
    status: u16,
    before: Option<&str>,
    after: Option<&str>,
) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO audit_events
           (id, at, user_id, token_id, token_label, request_id, method, path, action,
            target_type, target_id, status, client, user_agent, before_json, after_json)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16)",
        params![
            id,
            Timestamp::now().millis(),
            ctx.principal.user_id,
            ctx.principal.token_id,
            ctx.principal.label,
            ctx.request_id,
            ctx.method.as_str(),
            ctx.path,
            ctx.action,
            target.map(|t| t.kind),
            target.map(|t| t.id),
            status,
            ctx.client,
            ctx.user_agent,
            before,
            after,
        ],
    )?;
    Ok(())
}

/// Records a write that was refused (403), so "what did my agent try?" has an
/// answer too. Failures to record are logged, not returned: the caller is
/// already returning an error.
pub fn record_refused(conn: &Connection, ctx: &Ctx, status: u16) {
    if let Err(err) = insert(conn, &ids::new_id("evt"), ctx, None, status, None, None) {
        eprintln!("{} could not record refused write: {err}", ctx.request_id);
    }
}
