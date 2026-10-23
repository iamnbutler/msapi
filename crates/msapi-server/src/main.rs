//! The `msapi` command.
//!
//! ```text
//! msapi serve [--addr 127.0.0.1:8080] [--db msapi.db] [--workers 8]
//! msapi user create <display name>     prints the user's root token, once
//! msapi migrate [--db msapi.db]
//! ```
//!
//! `MSAPI_ADDR` and `MSAPI_DB` set the defaults; `MSAPI_TRUST_PROXY=1` takes
//! client addresses from `X-Forwarded-For`.

use std::path::PathBuf;
use std::process::ExitCode;

use msapi_server::serve::{self, Config};
use msapi_server::{auth, db};

const USAGE: &str = "usage:
  msapi serve [--addr ADDR] [--db PATH] [--workers N]
  msapi user create <display name> [--db PATH]
  msapi migrate [--db PATH]

env: MSAPI_ADDR (default 127.0.0.1:8080), MSAPI_DB (default msapi.db), MSAPI_TRUST_PROXY=1";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let mut config = Config {
        addr: std::env::var("MSAPI_ADDR").unwrap_or_else(|_| "127.0.0.1:8080".to_owned()),
        db: std::env::var_os("MSAPI_DB").map_or_else(|| PathBuf::from("msapi.db"), PathBuf::from),
        workers: thread_count(),
        trust_proxy: std::env::var("MSAPI_TRUST_PROXY").is_ok_and(|v| v == "1" || v == "true"),
    };
    let mut positional = Vec::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        let mut value = || rest.next().cloned().ok_or_else(|| format!("{arg} needs a value\n\n{USAGE}"));
        match arg.as_str() {
            "--addr" => config.addr = value()?,
            "--db" => config.db = PathBuf::from(value()?),
            "--workers" => {
                config.workers = value()?.parse().map_err(|_| format!("--workers must be a number\n\n{USAGE}"))?;
            }
            "-h" | "--help" => return Err(USAGE.to_owned()),
            _ => positional.push(arg.as_str()),
        }
    }

    match positional.as_slice() {
        ["serve"] => serve::run(&config).map_err(|e| e.to_string()),
        ["migrate"] => {
            db::open(&config.db).map_err(|e| e.to_string())?;
            eprintln!("{} is up to date", config.db.display());
            Ok(())
        }
        ["user", "create", name @ ..] if !name.is_empty() => {
            let name = name.join(" ");
            let mut conn = db::open(&config.db).map_err(|e| e.to_string())?;
            let (user_id, token) = auth::create_user(&mut conn, &name).map_err(|e| e.to_string())?;
            eprintln!("created user {user_id} ({name}). Its root token, shown only once:");
            println!("{token}");
            Ok(())
        }
        _ => Err(USAGE.to_owned()),
    }
}

fn thread_count() -> usize {
    std::thread::available_parallelism().map_or(4, |n| n.get().clamp(2, 16))
}
