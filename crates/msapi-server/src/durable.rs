//! Durability when the database lives on a disk that can vanish.
//!
//! On Cloudflare the server runs in a container whose disk is lost when it
//! stops. With a log host configured (`MSAPI_LOG`, passed to [`restore`]), the
//! statements of every write transaction are sent there **before** it commits;
//! if the log does not acknowledge them, the transaction rolls back. An
//! acknowledged write is therefore never lost. The log also keeps periodic
//! snapshots, and on boot [`restore`] rebuilds the database from the latest
//! snapshot plus the batches after it.
//!
//! Replaying statements reproduces the database because every value is a bound
//! parameter (IDs and times are made in Rust, never by SQL functions) and
//! batches replay in commit order.
//!
//! Without a log this module does nothing beyond plain transactions.
//!
//! The log speaks three requests:
//!
//! ```text
//! GET  /state            → frames: (seq u64, len u64, bytes) — the snapshot, then batches
//! POST /changeset?seq=N  ← one batch of statements; refused unless N follows the last one
//! PUT  /snapshot?seq=N   ← the whole database after batch N; older batches are dropped
//! ```

use std::cell::RefCell;
use std::io::{self, Read, Write as _};
use std::net::TcpStream;
use std::path::Path;
use std::sync::{Mutex, OnceLock, PoisonError};
use std::time::{Duration, Instant};

use msapi_core::batch::{self, Param, Statement};
use rusqlite::types::{ToSqlOutput, Value, ValueRef};
use rusqlite::{Connection, Row, ToSql, params_from_iter};

/// Snapshot after this many changesets, so restores stay short.
const SNAPSHOT_EVERY: u64 = 256;

struct Log {
    host: String,
    state: Mutex<Position>,
}

#[derive(Clone, Copy)]
struct Position {
    /// The last changeset the log acknowledged.
    seq: u64,
    /// The changeset the latest snapshot includes.
    snapshot: u64,
}

static LOG: OnceLock<Log> = OnceLock::new();

fn log() -> Option<&'static Log> {
    LOG.get()
}

/// A write transaction whose statements are logged before they commit.
///
/// Every statement that changes the database must go through
/// [`Logged::execute`] or [`Logged::query_map`]; [`Logged::conn`] is for reads.
/// Dropping it without [`Logged::commit`] rolls back.
pub struct Logged<'c> {
    conn: &'c Connection,
    batch: RefCell<Vec<u8>>,
    open: bool,
}

impl<'c> Logged<'c> {
    /// `BEGIN IMMEDIATE`.
    pub fn begin(conn: &'c Connection) -> rusqlite::Result<Self> {
        conn.execute_batch("BEGIN IMMEDIATE")?;
        Ok(Self { conn, batch: RefCell::new(Vec::new()), open: true })
    }

    /// The connection, for the transaction's reads.
    #[must_use]
    pub fn conn(&self) -> &'c Connection {
        self.conn
    }

    /// Runs a statement that changes the database and records it.
    pub fn execute(&self, sql: &str, params: &[&dyn ToSql]) -> rusqlite::Result<usize> {
        let values = self.record(sql, params)?;
        self.conn.execute(sql, params_from_iter(&values))
    }

    /// Runs a changing statement that returns rows (`RETURNING`) and records it.
    pub fn query_map<T>(
        &self,
        sql: &str,
        params: &[&dyn ToSql],
        f: impl FnMut(&Row<'_>) -> rusqlite::Result<T>,
    ) -> rusqlite::Result<Vec<T>> {
        let values = self.record(sql, params)?;
        let mut stmt = self.conn.prepare(sql)?;
        stmt.query_map(params_from_iter(&values), f)?.collect()
    }

    fn record(&self, sql: &str, params: &[&dyn ToSql]) -> rusqlite::Result<Vec<Value>> {
        let values = params
            .iter()
            .map(|p| match p.to_sql()? {
                ToSqlOutput::Borrowed(v) => Ok(match v {
                    ValueRef::Null => Value::Null,
                    ValueRef::Integer(i) => Value::Integer(i),
                    ValueRef::Real(r) => Value::Real(r),
                    ValueRef::Text(t) => Value::Text(String::from_utf8_lossy(t).into_owned()),
                    ValueRef::Blob(b) => Value::Blob(b.to_vec()),
                }),
                ToSqlOutput::Owned(v) => Ok(v),
                _ => Err(rusqlite::Error::ToSqlConversionFailure("unsupported parameter type".into())),
            })
            .collect::<rusqlite::Result<Vec<_>>>()?;
        if log().is_some() {
            encode_statement(&mut self.batch.borrow_mut(), sql, &values)
                .ok_or_else(|| rusqlite::Error::ToSqlConversionFailure("statement too large to log".into()))?;
        }
        Ok(values)
    }

    /// Logs the statements, then commits. If the log refuses or cannot be
    /// reached, rolls back and returns the error.
    pub fn commit(mut self) -> rusqlite::Result<()> {
        let batch = self.batch.take();
        let Some(log) = log().filter(|_| !batch.is_empty()) else {
            self.open = false;
            return self.conn.execute_batch("COMMIT");
        };

        // Hold the position across send and commit, so the log's order is the
        // commit order.
        let mut pos = log.state.lock().unwrap_or_else(PoisonError::into_inner);
        let seq = pos.seq + 1;
        if let Err(err) = send(&log.host, "POST", &format!("/changeset?seq={seq}"), &batch) {
            // `self` drops here and rolls back.
            return Err(rusqlite::Error::ToSqlConversionFailure(Box::new(err)));
        }
        self.open = false;
        if let Err(err) = self.conn.execute_batch("COMMIT") {
            // The log has a change the database does not. Restarting replays the
            // log, which is the state clients were told about.
            eprintln!("commit failed after logging batch {seq}: {err}; exiting to restore from the log");
            std::process::exit(70);
        }
        pos.seq = seq;
        if pos.seq - pos.snapshot >= SNAPSHOT_EVERY {
            match snapshot(self.conn, &log.host, pos.seq) {
                Ok(()) => pos.snapshot = pos.seq,
                Err(err) => eprintln!("snapshot at {seq} failed (will retry later): {err}"),
            }
        }
        Ok(())
    }
}

impl Drop for Logged<'_> {
    fn drop(&mut self) {
        if self.open {
            let _ = self.conn.execute_batch("ROLLBACK");
        }
    }
}

/// The batch encoding of one statement (see [`msapi_core::batch`]). `None` if
/// a length does not fit the format's u32.
fn encode_statement(out: &mut Vec<u8>, sql: &str, values: &[Value]) -> Option<()> {
    let params = values
        .iter()
        .map(|v| match v {
            Value::Null => Param::Null,
            Value::Integer(i) => Param::Integer(*i),
            Value::Real(r) => Param::Real(r.to_bits()),
            Value::Text(t) => Param::Text(t.as_bytes().to_vec()),
            Value::Blob(b) => Param::Blob(b.clone()),
        })
        .collect();
    batch::encode_statement(out, &Statement { sql: sql.as_bytes().to_vec(), params }).then_some(())
}

/// Decodes a batch into its statements.
fn decode_batch(data: &[u8]) -> io::Result<Vec<(String, Vec<Value>)>> {
    let statements = batch::decode_batch(data).ok_or_else(|| bad("batch is malformed"))?;
    statements
        .into_iter()
        .map(|s| {
            let sql = String::from_utf8(s.sql).map_err(|_| bad("SQL is not UTF-8"))?;
            let values = s
                .params
                .into_iter()
                .map(|p| {
                    Ok(match p {
                        Param::Null => Value::Null,
                        Param::Integer(i) => Value::Integer(i),
                        Param::Real(bits) => Value::Real(f64::from_bits(bits)),
                        Param::Text(t) => Value::Text(String::from_utf8(t).map_err(|_| bad("text is not UTF-8"))?),
                        Param::Blob(b) => Value::Blob(b),
                    })
                })
                .collect::<io::Result<_>>()?;
            Ok((sql, values))
        })
        .collect()
}

/// Starts logging to `host` and rebuilds the database at `path` from the log.
/// Call once, before opening the database. With no host, does nothing.
pub fn restore(path: &Path, host: Option<&str>) -> io::Result<()> {
    let Some(host) = host.map(str::to_owned) else { return Ok(()) };
    let state = fetch_state(&host)?;
    let (snapshot, seq) = rebuild(path, &state)?;
    eprintln!("restored snapshot {snapshot} and {} batches from {host}", seq - snapshot);
    let log = Log { host, state: Mutex::new(Position { seq, snapshot }) };
    if LOG.set(log).is_err() {
        return Err(bad("restore called twice"));
    }
    Ok(())
}

/// Replaces the database at `path` with the log's `state` (a `GET /state`
/// body). Returns the snapshot's batch number and the last one applied.
pub fn rebuild(path: &Path, state: &[u8]) -> io::Result<(u64, u64)> {
    let mut frames = frames(state)?.into_iter();
    let (snapshot_seq, snapshot) = frames.next().ok_or_else(|| bad("log state has no snapshot frame"))?;

    for suffix in ["", "-wal", "-shm"] {
        let mut p = path.as_os_str().to_owned();
        p.push(suffix);
        match std::fs::remove_file(&p) {
            Err(e) if e.kind() != io::ErrorKind::NotFound => return Err(e),
            _ => {}
        }
    }
    if !snapshot.is_empty() {
        std::fs::write(path, snapshot)?;
    }

    let conn = Connection::open(path).map_err(other)?;
    let mut seq = snapshot_seq;
    for (n, changes) in frames {
        if !msapi_core::rules::next_batch_ok(seq, n) {
            return Err(bad(&format!("log skips from changeset {seq} to {n}")));
        }
        let statements = decode_batch(changes)?;
        let tx = Logged::begin(&conn).map_err(other)?;
        for (sql, values) in &statements {
            let mut stmt = tx.conn().prepare_cached(sql).map_err(other)?;
            let mut rows = stmt.query(params_from_iter(values)).map_err(other)?;
            while rows.next().map_err(|e| bad(&format!("batch {n} does not apply: {e}")))?.is_some() {}
        }
        tx.commit().map_err(other)?;
        seq = n;
    }
    Ok((snapshot_seq, seq))
}

/// Snapshots now, after migrations, which change the schema outside any
/// [`Logged`] transaction.
pub fn checkpoint(conn: &Connection) -> io::Result<()> {
    let Some(log) = log() else { return Ok(()) };
    let mut pos = log.state.lock().unwrap_or_else(PoisonError::into_inner);
    snapshot(conn, &log.host, pos.seq)?;
    pos.snapshot = pos.seq;
    Ok(())
}

fn snapshot(conn: &Connection, host: &str, seq: u64) -> io::Result<()> {
    let path = std::env::temp_dir().join(format!("msapi-snapshot-{}.db", std::process::id()));
    let _ = std::fs::remove_file(&path);
    conn.execute("VACUUM INTO ?1", [path.to_string_lossy()]).map_err(other)?;
    let bytes = std::fs::read(&path)?;
    let _ = std::fs::remove_file(&path);
    send(host, "PUT", &format!("/snapshot?seq={seq}"), &bytes)?;
    Ok(())
}

fn fetch_state(host: &str) -> io::Result<Vec<u8>> {
    // The container's network can come up a moment after the process.
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        match send(host, "GET", "/state", &[]) {
            Ok(body) => return Ok(body),
            Err(err) if Instant::now() < deadline => {
                eprintln!("waiting for the log at {host}: {err}");
                std::thread::sleep(Duration::from_millis(500));
            }
            Err(err) => return Err(err),
        }
    }
}

/// The frames of a `GET /state` body, as sequence numbers and bodies. A body
/// with anything but whole frames is refused rather than replayed in part.
fn frames(state: &[u8]) -> io::Result<Vec<(u64, &[u8])>> {
    let frames = batch::frames(state).ok_or_else(|| bad("log state has a truncated frame"))?;
    Ok(frames.into_iter().map(|(seq, start, end)| (seq, &state[start..end])).collect())
}

/// A minimal HTTP/1.1 exchange: one request, `Connection: close`, and the body
/// of a 2xx response. The log is the only peer, so this is all that is needed.
fn send(host: &str, method: &str, path: &str, body: &[u8]) -> io::Result<Vec<u8>> {
    let addr = if host.contains(':') { host.to_owned() } else { format!("{host}:80") };
    let mut stream = TcpStream::connect(addr)?;
    stream.set_read_timeout(Some(Duration::from_secs(30)))?;
    stream.set_write_timeout(Some(Duration::from_secs(30)))?;
    let head = format!(
        "{method} {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()?;

    let mut response = Vec::new();
    stream.read_to_end(&mut response)?;
    let split = response.windows(4).position(|w| w == b"\r\n\r\n").ok_or_else(|| bad("no end of headers"))?;
    let head = std::str::from_utf8(&response[..split]).map_err(|_| bad("headers are not UTF-8"))?;
    let status: u16 = head.split(' ').nth(1).and_then(|s| s.parse().ok()).ok_or_else(|| bad("no status"))?;
    let mut payload = response[split + 4..].to_vec();
    if head.lines().any(|l| l.to_ascii_lowercase().starts_with("transfer-encoding:") && l.contains("chunked")) {
        payload = dechunk(&payload)?;
    }
    if !(200..300).contains(&status) {
        let text = String::from_utf8_lossy(&payload);
        return Err(bad(&format!("{method} {path}: {status} {}", text.trim())));
    }
    Ok(payload)
}

fn dechunk(mut data: &[u8]) -> io::Result<Vec<u8>> {
    let mut out = Vec::new();
    loop {
        let line_end = data.windows(2).position(|w| w == b"\r\n").ok_or_else(|| bad("bad chunk"))?;
        let size_text = std::str::from_utf8(&data[..line_end]).map_err(|_| bad("bad chunk size"))?;
        let size = usize::from_str_radix(size_text.split(';').next().unwrap_or("").trim(), 16)
            .map_err(|_| bad("bad chunk size"))?;
        data = &data[line_end + 2..];
        if size == 0 {
            return Ok(out);
        }
        let chunk = data.get(..size).ok_or_else(|| bad("short chunk"))?;
        out.extend_from_slice(chunk);
        data = data.get(size + 2..).ok_or_else(|| bad("short chunk"))?;
    }
}

fn bad(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.to_owned())
}

fn other(err: rusqlite::Error) -> io::Error {
    io::Error::other(err)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_round_trip() {
        let mut bytes = Vec::new();
        for (seq, body) in [(3_u64, &b"snap"[..]), (4, b""), (5, b"xy")] {
            bytes.extend_from_slice(&seq.to_be_bytes());
            bytes.extend_from_slice(&(body.len() as u64).to_be_bytes());
            bytes.extend_from_slice(body);
        }
        assert_eq!(frames(&bytes).unwrap(), vec![(3, &b"snap"[..]), (4, &b""[..]), (5, &b"xy"[..])]);
        assert!(frames(&bytes[..bytes.len() - 1]).is_err(), "a truncated tail is refused");
    }

    #[test]
    fn batches_round_trip() {
        let values = vec![
            Value::Null,
            Value::Integer(-7),
            Value::Real(1.5),
            Value::Text("héllo".into()),
            Value::Blob(vec![0, 255]),
        ];
        let mut batch = Vec::new();
        assert!(encode_statement(&mut batch, "INSERT INTO t VALUES (?1, ?2, ?3, ?4, ?5)", &values).is_some());
        assert!(encode_statement(&mut batch, "DELETE FROM t", &[]).is_some());
        let decoded = decode_batch(&batch).ok();
        assert_eq!(
            decoded,
            Some(vec![
                ("INSERT INTO t VALUES (?1, ?2, ?3, ?4, ?5)".to_owned(), values),
                ("DELETE FROM t".to_owned(), vec![]),
            ])
        );
        assert!(decode_batch(&batch[..batch.len() - 1]).is_err());
    }

    #[test]
    fn chunked_bodies_decode() {
        assert_eq!(dechunk(b"3\r\nabc\r\n2\r\nde\r\n0\r\n\r\n").ok(), Some(b"abcde".to_vec()));
    }
}
