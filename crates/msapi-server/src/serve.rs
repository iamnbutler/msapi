//! The socket layer: `tiny_http` in, [`routes::handle`] out.
//!
//! Each worker thread owns one SQLite connection. WAL lets readers run in
//! parallel while writes queue on SQLite's write lock.

use std::io::Read;
use std::path::PathBuf;
use std::sync::Arc;
use std::thread;

use tiny_http::{Header, Server};

use msapi_core::api;

use crate::error::ApiError;
use crate::http::{Method, Request, Response};
use crate::{db, durable, routes};

pub use msapi_core::api::MAX_BODY;

/// How to run the server.
#[derive(Clone, Debug)]
pub struct Config {
    /// The address to bind, e.g. `127.0.0.1:8080`.
    pub addr: String,
    /// The SQLite database file.
    pub db: PathBuf,
    /// Worker threads, each with its own connection.
    pub workers: usize,
    /// Take the client address from `X-Forwarded-For`. Only set this behind a
    /// proxy that overwrites the header, or clients can forge it.
    pub trust_proxy: bool,
    /// The changeset log's host, e.g. `msapi.log`; see [`durable`].
    pub log: Option<String>,
}

/// Binds and serves until the process exits.
///
/// # Errors
///
/// When the address cannot be bound or the database cannot be opened.
pub fn run(config: &Config) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Rebuild from the log if one is configured, then open once up front so
    // migrations run (and are snapshotted) before any worker starts.
    durable::restore(&config.db, config.log.as_deref())?;
    durable::checkpoint(&db::open(&config.db)?)?;
    let server = Arc::new(Server::http(&config.addr)?);
    eprintln!("msapi listening on http://{} (db {})", config.addr, config.db.display());

    let workers: Vec<_> = (0..config.workers.max(1))
        .map(|_| {
            let server = Arc::clone(&server);
            let config = config.clone();
            thread::spawn(move || worker(&server, &config))
        })
        .collect();
    for w in workers {
        if let Ok(Err(err)) = w.join() {
            return Err(err);
        }
    }
    Ok(())
}

fn worker(server: &Server, config: &Config) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut conn = db::open(&config.db)?;
    loop {
        let mut incoming = server.recv()?;
        let response = match read_request(&mut incoming, config.trust_proxy) {
            Ok(req) => routes::handle(&mut conn, &req),
            Err(err) => err.to_response(),
        };
        if let Err(err) = incoming.respond(to_tiny(response)) {
            eprintln!("could not send response: {err}");
        }
    }
}

fn read_request(incoming: &mut tiny_http::Request, trust_proxy: bool) -> Result<Request, ApiError> {
    let mut req = Request::new(Method::parse(incoming.method().as_str().as_bytes()), incoming.url());
    req.headers = incoming
        .headers()
        .iter()
        .map(|h| (h.field.as_str().as_str().to_ascii_lowercase(), h.value.as_str().to_owned()))
        .collect();
    req.client = if trust_proxy {
        // `forwarded` cuts at an ASCII comma and trims whole characters, so
        // the range always falls on character boundaries.
        req.header("x-forwarded-for")
            .and_then(|v| {
                let (a, b) = api::forwarded(v.as_bytes());
                v.get(a..b)
            })
            .map(str::to_owned)
    } else {
        None
    }
    .or_else(|| incoming.remote_addr().map(|a| a.ip().to_string()));

    if incoming.body_length().is_some_and(|n| !api::body_fits(n)) {
        return Err(ApiError::too_large(MAX_BODY));
    }
    let mut body = Vec::new();
    incoming
        .as_reader()
        .take(MAX_BODY as u64 + 1)
        .read_to_end(&mut body)
        .map_err(|e| ApiError::bad_request(format!("could not read body: {e}")))?;
    if !api::body_fits(body.len()) {
        return Err(ApiError::too_large(MAX_BODY));
    }
    req.body = body;
    Ok(req)
}

fn to_tiny(response: Response) -> tiny_http::Response<std::io::Cursor<Vec<u8>>> {
    let mut out = tiny_http::Response::from_data(response.body).with_status_code(response.status);
    let headers = std::iter::once(("content-type", response.content_type.to_owned())).chain(response.headers);
    for (name, value) in headers {
        if let Ok(header) = Header::from_bytes(name.as_bytes(), value.as_bytes()) {
            out.add_header(header);
        }
    }
    out
}
