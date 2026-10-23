//! Opening the SQLite database and applying migrations.

use std::path::Path;
use std::time::Duration;

use rusqlite::Connection;

/// Migrations in order. `PRAGMA user_version` records how many have run.
const MIGRATIONS: &[&str] = &[include_str!("../migrations/0001_init.sql")];

/// Opens (creating if needed) the database at `path` and brings it up to date.
///
/// Each server worker opens its own connection; WAL mode lets readers proceed
/// while one writer commits.
pub fn open(path: &Path) -> rusqlite::Result<Connection> {
    let conn = Connection::open(path)?;
    configure(&conn)?;
    conn.pragma_update(None, "journal_mode", "WAL")?;
    migrate(&conn)?;
    Ok(conn)
}

/// An in-memory database with the schema applied, for tests.
pub fn open_in_memory() -> rusqlite::Result<Connection> {
    let conn = Connection::open_in_memory()?;
    configure(&conn)?;
    migrate(&conn)?;
    Ok(conn)
}

fn configure(conn: &Connection) -> rusqlite::Result<()> {
    conn.busy_timeout(Duration::from_secs(5))?;
    conn.pragma_update(None, "foreign_keys", "ON")?;
    conn.pragma_update(None, "synchronous", "NORMAL")?;
    Ok(())
}

fn migrate(conn: &Connection) -> rusqlite::Result<()> {
    let applied: u32 = conn.pragma_query_value(None, "user_version", |r| r.get(0))?;
    for (i, sql) in MIGRATIONS.iter().enumerate().skip(applied as usize) {
        conn.execute_batch(&format!("BEGIN IMMEDIATE;\n{sql}\nPRAGMA user_version = {};\nCOMMIT;", i + 1))?;
    }
    Ok(())
}
