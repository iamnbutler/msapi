//! Durability when the database lives on a disk that can vanish.
//!
//! On Cloudflare the server runs in a container whose disk is lost when it
//! stops. With a log host configured (`MSAPI_LOG`, passed to [`restore`]) (the Worker's log endpoint), every
//! write transaction is captured as a SQLite changeset and sent there **before**
//! it commits; if the log does not acknowledge it, the transaction rolls back.
//! An acknowledged write is therefore never lost. The log also keeps periodic
//! snapshots, and on boot [`restore`] rebuilds the database from the latest
//! snapshot plus the changesets after it.
//!
//! Without a log this module does nothing beyond plain transactions.
//!
//! The log speaks three requests:
//!
//! ```text
//! GET  /state            → frames: (seq u64, len u64, bytes) — the snapshot, then changesets
//! POST /changeset?seq=N  ← one changeset; refused unless N follows the last one
//! PUT  /snapshot?seq=N   ← the whole database after changeset N; older changesets are dropped
//! ```

use std::io::{self, Read, Write as _};
use std::net::TcpStream;
use std::path::Path;
use std::sync::{Mutex, OnceLock, PoisonError};
use std::time::{Duration, Instant};

use rusqlite::Connection;
use rusqlite::session::{ConflictAction, ConflictType, Session};

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

/// A write transaction whose changes are logged before they commit.
///
/// Dropping it without [`Logged::commit`] rolls back.
pub struct Logged<'c> {
    conn: &'c Connection,
    session: Option<Session<'c>>,
    open: bool,
}

impl<'c> Logged<'c> {
    /// `BEGIN IMMEDIATE`, and start capturing changes if a log is configured.
    pub fn begin(conn: &'c Connection) -> rusqlite::Result<Self> {
        conn.execute_batch("BEGIN IMMEDIATE")?;
        let mut this = Self { conn, session: None, open: true };
        if log().is_some() {
            let mut session = Session::new(conn)?;
            session.attach::<&str>(None)?;
            this.session = Some(session);
        }
        Ok(this)
    }

    /// The connection, for the transaction's statements.
    #[must_use]
    pub fn conn(&self) -> &'c Connection {
        self.conn
    }

    /// Logs the changes, then commits. If the log refuses or cannot be
    /// reached, rolls back and returns the error.
    pub fn commit(mut self) -> rusqlite::Result<()> {
        let (Some(log), Some(mut session)) = (log(), self.session.take()) else {
            self.open = false;
            return self.conn.execute_batch("COMMIT");
        };
        let mut changes = Vec::new();
        session.changeset_strm(&mut changes)?;
        drop(session);
        if changes.is_empty() {
            self.open = false;
            return self.conn.execute_batch("COMMIT");
        }

        // Hold the position across send and commit, so the log's order is the
        // commit order.
        let mut pos = log.state.lock().unwrap_or_else(PoisonError::into_inner);
        let seq = pos.seq + 1;
        if let Err(err) = send(&log.host, "POST", &format!("/changeset?seq={seq}"), &changes) {
            // `self` drops here and rolls back.
            return Err(rusqlite::Error::ToSqlConversionFailure(Box::new(err)));
        }
        self.open = false;
        if let Err(err) = self.conn.execute_batch("COMMIT") {
            // The log has a change the database does not. Restarting replays the
            // log, which is the state clients were told about.
            eprintln!("commit failed after logging changeset {seq}: {err}; exiting to restore from the log");
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
        self.session = None;
        if self.open {
            let _ = self.conn.execute_batch("ROLLBACK");
        }
    }
}

/// Starts logging to `host` and rebuilds the database at `path` from the log.
/// Call once, before opening the database. With no host, does nothing.
pub fn restore(path: &Path, host: Option<&str>) -> io::Result<()> {
    let Some(host) = host.map(str::to_owned) else { return Ok(()) };
    let state = fetch_state(&host)?;
    let (snapshot, seq) = rebuild(path, &state)?;
    eprintln!("restored snapshot {snapshot} and {} changesets from {host}", seq - snapshot);
    let log = Log { host, state: Mutex::new(Position { seq, snapshot }) };
    if LOG.set(log).is_err() {
        return Err(bad("restore called twice"));
    }
    Ok(())
}

/// Replaces the database at `path` with the log's `state` (a `GET /state`
/// body). Returns the snapshot's changeset number and the last one applied.
pub fn rebuild(path: &Path, state: &[u8]) -> io::Result<(u64, u64)> {
    let mut frames = Frames { bytes: state };
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
        if n != seq + 1 {
            return Err(bad(&format!("log skips from changeset {seq} to {n}")));
        }
        let mut input = changes;
        conn.apply_strm(&mut input, None::<fn(&str) -> bool>, |_: ConflictType, _| {
            ConflictAction::SQLITE_CHANGESET_ABORT
        })
        .map_err(|e| bad(&format!("changeset {n} does not apply: {e}")))?;
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

struct Frames<'a> {
    bytes: &'a [u8],
}

impl<'a> Iterator for Frames<'a> {
    type Item = (u64, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let (head, rest) = self.bytes.split_at_checked(16)?;
        let seq = u64::from_be_bytes(head[..8].try_into().ok()?);
        let len = usize::try_from(u64::from_be_bytes(head[8..].try_into().ok()?)).ok()?;
        let (body, rest) = rest.split_at_checked(len)?;
        self.bytes = rest;
        Some((seq, body))
    }
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
        let frames: Vec<_> = Frames { bytes: &bytes }.collect();
        assert_eq!(frames, vec![(3, &b"snap"[..]), (4, &b""[..]), (5, &b"xy"[..])]);
    }

    #[test]
    fn chunked_bodies_decode() {
        assert_eq!(dechunk(b"3\r\nabc\r\n2\r\nde\r\n0\r\n\r\n").ok(), Some(b"abcde".to_vec()));
    }
}
