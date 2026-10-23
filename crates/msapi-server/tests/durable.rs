//! The changeset log: writes reach it before they commit, a database rebuilt
//! from it matches the original, and a write the log refuses does not happen.

#![allow(clippy::unwrap_used, reason = "tests fail loudly by design")]

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use rusqlite::Connection;
use serde_json::json;

use msapi_server::http::{Method, Request};
use msapi_server::{auth, db, durable, routes};

/// An in-memory log speaking the same protocol as the Worker's.
#[derive(Default)]
struct FakeLog {
    snapshot: (u64, Vec<u8>),
    changes: Vec<(u64, Vec<u8>)>,
}

impl FakeLog {
    fn state(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for (seq, body) in std::iter::once(&self.snapshot).chain(&self.changes) {
            out.extend_from_slice(&seq.to_be_bytes());
            out.extend_from_slice(&(body.len() as u64).to_be_bytes());
            out.extend_from_slice(body);
        }
        out
    }
}

fn serve_log(log: &Arc<Mutex<FakeLog>>, refuse: &Arc<AtomicBool>) -> String {
    let (log, refuse) = (Arc::clone(log), Arc::clone(refuse));
    let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
    let addr = server.server_addr().to_ip().unwrap().to_string();
    thread::spawn(move || {
        for mut req in server.incoming_requests() {
            let mut body = Vec::new();
            req.as_reader().read_to_end(&mut body).unwrap();
            let url = req.url().to_owned();
            let seq: u64 = url.split("seq=").nth(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            let mut log = log.lock().unwrap();
            let status = match (req.method().as_str(), url.split('?').next().unwrap()) {
                ("GET", "/state") => {
                    let state = log.state();
                    req.respond(tiny_http::Response::from_data(state)).unwrap();
                    continue;
                }
                ("POST", "/changeset") if refuse.load(Ordering::SeqCst) => 503,
                ("POST", "/changeset") => {
                    let last = log.changes.last().map_or(log.snapshot.0, |c| c.0);
                    if seq == last + 1 {
                        log.changes.push((seq, body));
                        204
                    } else {
                        409
                    }
                }
                ("PUT", "/snapshot") => {
                    log.snapshot = (seq, body);
                    log.changes.retain(|c| c.0 > seq);
                    204
                }
                _ => 404,
            };
            req.respond(tiny_http::Response::empty(status)).unwrap();
        }
    });
    addr
}

fn call(conn: &mut Connection, token: &str, method: Method, target: &str, body: &serde_json::Value) -> u16 {
    let mut req = Request::new(method, target);
    req.headers.push(("authorization".into(), format!("Bearer {token}")));
    req.headers.push(("content-type".into(), "application/json".into()));
    req.body = serde_json::to_vec(body).unwrap();
    routes::handle(conn, &req).status
}

fn dump(path: &std::path::Path) -> Vec<String> {
    let conn = Connection::open(path).unwrap();
    // Token use times are bookkeeping, deliberately not logged.
    conn.execute("UPDATE tokens SET last_used_at = NULL", []).unwrap();
    let mut out = Vec::new();
    for table in ["users", "tokens", "accounts", "characters", "stat_snapshots", "audit_events"] {
        let mut stmt = conn.prepare(&format!("SELECT * FROM {table} ORDER BY id")).unwrap();
        let columns = stmt.column_count();
        let rows = stmt
            .query_map([], |r| {
                let values: Vec<String> = (0..columns).map(|i| format!("{:?}", r.get_ref(i).unwrap())).collect();
                Ok(format!("{table}: {}", values.join(" | ")))
            })
            .unwrap();
        out.extend(rows.map(Result::unwrap));
    }
    out
}

#[test]
fn the_log_rebuilds_every_acknowledged_write_and_refusals_roll_back() {
    let log = Arc::new(Mutex::new(FakeLog::default()));
    let refuse = Arc::new(AtomicBool::new(false));
    let host = serve_log(&log, &refuse);
    let dir = std::env::temp_dir().join(format!("msapi-durable-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let primary = dir.join("primary.db");

    durable::restore(&primary, Some(&host)).unwrap();
    let mut conn = db::open(&primary).unwrap();
    durable::checkpoint(&conn).unwrap();
    assert_eq!(log.lock().unwrap().snapshot.0, 0);
    assert!(!log.lock().unwrap().snapshot.1.is_empty(), "the migrated schema is snapshotted");

    let (_, token) = auth::create_user(&mut conn, "tester").unwrap();
    assert_eq!(
        call(&mut conn, &token, Method::Post, "/v1/accounts", &json!({ "region": "gms", "label": "main" })),
        201
    );
    let account: String = conn.query_row("SELECT id FROM accounts", [], |r| r.get(0)).unwrap();
    let character = json!({
        "character_name": "Lutoren", "world_name": "kronos", "character_class": "Night Walker",
        "character_level": 275, "character_exp_rate": 12.345,
    });
    assert_eq!(call(&mut conn, &token, Method::Post, &format!("/v1/accounts/{account}/characters"), &character), 201);
    let character_id: String = conn.query_row("SELECT id FROM characters", [], |r| r.get(0)).unwrap();
    let stat_body = json!({ "luk": 38120, "combat_power": 236_118 });
    assert_eq!(call(&mut conn, &token, Method::Put, &format!("/v1/characters/{character_id}/stat"), &stat_body), 200);
    assert_eq!(log.lock().unwrap().changes.len(), 4, "user, account, character, stats");

    // A write the log refuses is rolled back, and the API reports a failure.
    refuse.store(true, Ordering::SeqCst);
    let refused = call(&mut conn, &token, Method::Post, "/v1/accounts", &json!({ "region": "gms", "label": "alt" }));
    assert_eq!(refused, 500);
    let accounts: i64 = conn.query_row("SELECT COUNT(*) FROM accounts", [], |r| r.get(0)).unwrap();
    assert_eq!(accounts, 1);
    refuse.store(false, Ordering::SeqCst);
    drop(conn);

    let replica = dir.join("replica.db");
    let log_state = log.lock().unwrap().state();
    assert_eq!(durable::rebuild(&replica, &log_state).unwrap(), (0, 4));
    assert_eq!(dump(&replica), dump(&primary));
    std::fs::remove_dir_all(&dir).unwrap();
}
