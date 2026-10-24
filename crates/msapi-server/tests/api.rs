//! End-to-end tests through [`routes::handle`], plus one over a real socket.

#![allow(clippy::unwrap_used, reason = "tests fail loudly by design")]

use std::io::{Read, Write as _};
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

use rusqlite::Connection;
use serde_json::{Value, json};

use msapi_server::http::{Method, Request};
use msapi_server::serve::{self, Config};
use msapi_server::{auth, db, routes};

struct Api {
    conn: Connection,
}

impl Api {
    fn new() -> (Self, String) {
        let mut conn = db::open_in_memory().unwrap();
        let (_, token) = auth::create_user(&mut conn, "tester").unwrap();
        (Self { conn }, token)
    }

    fn call(&mut self, token: &str, method: Method, target: &str, body: Option<Value>) -> (u16, Value) {
        let mut req = Request::new(method, target);
        req.headers.push(("authorization".into(), format!("Bearer {token}")));
        if let Some(body) = body {
            req.headers.push(("content-type".into(), "application/json".into()));
            req.body = serde_json::to_vec(&body).unwrap();
        }
        let res = routes::handle(&mut self.conn, &req);
        assert!(res.headers.iter().any(|(k, _)| *k == "x-request-id"));
        let value = if res.body.is_empty() { Value::Null } else { res.json_body().unwrap() };
        (res.status, value)
    }
}

fn account(api: &mut Api, token: &str) -> String {
    let (status, body) =
        api.call(token, Method::Post, "/v1/accounts", Some(json!({ "region": "gms", "label": "main" })));
    assert_eq!(status, 201, "{body}");
    body["id"].as_str().unwrap().to_owned()
}

fn character(api: &mut Api, token: &str, account: &str, name: &str) -> String {
    let (status, body) = api.call(
        token,
        Method::Post,
        &format!("/v1/accounts/{account}/characters"),
        Some(json!({
            "character_name": name,
            "world_name": "kronos",
            "character_class": "Night Walker",
            "character_level": 275,
            "character_exp_rate": 12.345,
        })),
    );
    assert_eq!(status, 201, "{body}");
    body["id"].as_str().unwrap().to_owned()
}

fn mint(api: &mut Api, token: &str, body: Value) -> String {
    let (status, res) = api.call(token, Method::Post, "/v1/tokens", Some(body));
    assert_eq!(status, 201, "{res}");
    res["token"].as_str().unwrap().to_owned()
}

#[test]
fn public_routes_need_no_token() {
    let (mut api, _) = Api::new();
    for path in ["/health", "/v1", "/v1/docs", "/v1/ref/worlds", "/v1/ref/classes", "/v1/ref/regions"] {
        let res = routes::handle(&mut api.conn, &Request::new(Method::Get, path));
        assert_eq!(res.status, 200, "{path}");
    }
    assert_eq!(api.call("msk_nope", Method::Get, "/v1/me", None).0, 401);
    assert_eq!(routes::handle(&mut api.conn, &Request::new(Method::Get, "/v1/accounts")).status, 401);
}

#[test]
fn account_and_character_lifecycle() {
    let (mut api, root) = Api::new();
    let acc = account(&mut api, &root);
    let chr = character(&mut api, &root, &acc, "Lutoren");

    let (status, body) = api.call(&root, Method::Get, &format!("/v1/characters/{chr}"), None);
    assert_eq!(status, 200);
    assert_eq!(body["world_name"], "Kronos");
    assert_eq!(body["world_type"], "heroic");
    assert_eq!(body["character_class"], "Night Walker");
    assert_eq!(body["character_exp_rate"], 12.345);
    assert_eq!(body["character_gender"], Value::Null, "absent stays absent");

    // Same name in the same world conflicts, case-insensitively.
    let (status, _) = api.call(
        &root,
        Method::Post,
        &format!("/v1/accounts/{acc}/characters"),
        Some(json!({ "character_name": "lutoren", "world_name": "Kronos", "character_class": "hero", "character_level": 200 })),
    );
    assert_eq!(status, 409);

    // Unknown world and class are 422 with a useful message.
    let (status, body) = api.call(
        &root,
        Method::Post,
        &format!("/v1/accounts/{acc}/characters"),
        Some(json!({ "character_name": "Other", "world_name": "Reboot", "character_class": "hero", "character_level": 200 })),
    );
    assert_eq!(status, 422);
    assert!(body["error"]["message"].as_str().unwrap().contains("Kronos"));

    // Merge patch: change level, clear exp rate.
    let (status, body) = api.call(
        &root,
        Method::Patch,
        &format!("/v1/characters/{chr}"),
        Some(json!({ "character_level": 276, "character_exp_rate": null })),
    );
    assert_eq!(status, 200, "{body}");
    assert_eq!(body["character_level"], 276);
    assert_eq!(body["character_exp_rate"], Value::Null);
    assert_eq!(body["character_name"], "Lutoren");

    let (_, body) = api.call(&root, Method::Get, &format!("/v1/accounts/{acc}"), None);
    assert_eq!(body["worlds"][0]["world_name"], "Kronos");
    assert_eq!(body["worlds"][0]["character_count"], 1);
    assert_eq!(body["character_list"][0]["id"], chr.as_str());

    // Region cannot change.
    let (status, _) = api.call(&root, Method::Patch, &format!("/v1/accounts/{acc}"), Some(json!({ "region": "kms" })));
    assert_eq!(status, 422);

    // Deleting the account takes its characters with it.
    assert_eq!(api.call(&root, Method::Delete, &format!("/v1/accounts/{acc}"), None).0, 204);
    assert_eq!(api.call(&root, Method::Get, &format!("/v1/characters/{chr}"), None).0, 404);
}

#[test]
fn stat_window_snapshots_and_validation() {
    let (mut api, root) = Api::new();
    let acc = account(&mut api, &root);
    let chr = character(&mut api, &root, &acc, "Lutoren");
    let stat = format!("/v1/characters/{chr}/stat");

    let (status, body) = api.call(&root, Method::Get, &stat, None);
    assert_eq!(status, 200);
    assert_eq!(body["stat"], Value::Null);

    let (status, body) = api.call(
        &root,
        Method::Put,
        &stat,
        Some(json!({ "combat_power": 123_456_789, "str": 1000, "final_damage": 162.27, "ignore_defense": 95.5 })),
    );
    assert_eq!(status, 200, "{body}");
    assert_eq!(body["snapshot"]["stat"]["final_damage"], 162.27);
    assert_eq!(body["snapshot"]["stat"]["dex"], Value::Null);

    // PATCH merges into the latest window.
    let (status, body) = api.call(&root, Method::Patch, &stat, Some(json!({ "dex": 500, "str": null })));
    assert_eq!(status, 200, "{body}");
    assert_eq!(body["snapshot"]["stat"]["dex"], 500);
    assert_eq!(body["snapshot"]["stat"]["str"], Value::Null);
    assert_eq!(body["snapshot"]["stat"]["combat_power"], 123_456_789);

    // Inconsistent windows are refused with the issues listed.
    let (status, body) = api.call(&root, Method::Put, &stat, Some(json!({ "ignore_defense": 100 })));
    assert_eq!(status, 422);
    assert_eq!(body["error"]["details"]["issues"][0]["field"], "ignore_defense");

    // Units are checked: too many decimals, unknown fields, strings for numbers.
    for bad in [json!({ "final_damage": 1.234 }), json!({ "strength": 1 }), json!({ "str": "1000" })] {
        assert_eq!(api.call(&root, Method::Put, &stat, Some(bad.clone())).0, 400, "{bad}");
    }

    let (_, body) = api.call(&root, Method::Get, &format!("{stat}/history?limit=1"), None);
    assert_eq!(body["history"].as_array().unwrap().len(), 1);
    assert_eq!(body["history"][0]["stat"]["dex"], 500);
    let cursor = body["next_before"].as_str().unwrap();
    let (_, body) = api.call(&root, Method::Get, &format!("{stat}/history?before={cursor}"), None);
    assert_eq!(body["history"].as_array().unwrap().len(), 1);
    assert_eq!(body["next_before"], Value::Null);
}

#[test]
fn delegated_tokens_narrow_and_are_audited() {
    let (mut api, root) = Api::new();
    let main = account(&mut api, &root);
    let other = account(&mut api, &root);
    let chr = character(&mut api, &root, &main, "Lutoren");
    let hidden = character(&mut api, &root, &other, "Hidden");

    let agent = mint(
        &mut api,
        &root,
        json!({
            "label": "chatgpt",
            "scopes": ["characters:read", "characters:write", "tokens:write"],
            "account_ids": [main],
            "expires_in_seconds": 3600,
        }),
    );

    // It reaches only its account, and only with its scopes.
    let (_, body) = api.call(&agent, Method::Get, "/v1/characters", None);
    assert_eq!(body["character_list"].as_array().unwrap().len(), 1);
    assert_eq!(api.call(&agent, Method::Get, &format!("/v1/characters/{hidden}"), None).0, 403);
    assert_eq!(api.call(&agent, Method::Get, "/v1/accounts", None).0, 403);
    assert_eq!(api.call(&agent, Method::Delete, &format!("/v1/characters/{chr}"), None).0, 403);
    let (status, _) =
        api.call(&agent, Method::Patch, &format!("/v1/characters/{chr}"), Some(json!({ "character_level": 280 })));
    assert_eq!(status, 200);

    // It cannot widen what it was given.
    let (status, _) = api.call(&agent, Method::Post, "/v1/tokens", Some(json!({ "label": "x", "scopes": ["delete"] })));
    assert_eq!(status, 403);
    let child =
        mint(&mut api, &agent, json!({ "label": "sub-agent", "scopes": ["characters:read"], "account_ids": [main] }));
    assert_eq!(api.call(&child, Method::Get, &format!("/v1/characters/{chr}"), None).0, 200);

    // The owner sees what the agent did, including the refused delete.
    let (_, me) = api.call(&agent, Method::Get, "/v1/me", None);
    let agent_id = me["token"]["id"].as_str().unwrap().to_owned();
    let (status, body) = api.call(&root, Method::Get, &format!("/v1/audit?token_id={agent_id}"), None);
    assert_eq!(status, 200);
    let actions: Vec<(&str, u64)> = body["events"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| (e["action"].as_str().unwrap(), e["status"].as_u64().unwrap()))
        .collect();
    assert_eq!(
        actions,
        [("token.mint", 200), ("token.mint", 403), ("character.update", 200), ("character.delete", 403)],
        "newest first; refused writes are recorded too"
    );
    let update = &body["events"][2];
    assert_eq!(update["before"]["character_level"], 275);
    assert_eq!(update["after"]["character_level"], 280);
    assert_eq!(update["token_label"], "chatgpt");

    // Revoking the agent cascades to everything it minted.
    let (status, body) = api.call(&root, Method::Delete, &format!("/v1/tokens/{agent_id}"), None);
    assert_eq!(status, 200);
    assert_eq!(body["revoked"].as_array().unwrap().len(), 2);
    assert_eq!(api.call(&agent, Method::Get, "/v1/me", None).0, 401);
    assert_eq!(api.call(&child, Method::Get, "/v1/me", None).0, 401);
}

#[test]
fn users_cannot_see_each_other() {
    let (mut api, alice) = Api::new();
    let (_, bob) = auth::create_user(&mut api.conn, "bob").unwrap();
    let acc = account(&mut api, &alice);
    let chr = character(&mut api, &alice, &acc, "Lutoren");
    assert_eq!(api.call(&bob, Method::Get, &format!("/v1/characters/{chr}"), None).0, 404);
    assert_eq!(api.call(&bob, Method::Get, &format!("/v1/accounts/{acc}"), None).0, 404);
    let (_, body) = api.call(&bob, Method::Get, "/v1/audit", None);
    assert_eq!(body["events"], json!([]));
    // A different user may use the same name in the same world: ownership is not verifiable.
    let bobs = account(&mut api, &bob);
    character(&mut api, &bob, &bobs, "Lutoren");
}

#[test]
fn item_equipment_snapshots_and_validation() {
    let (mut api, root) = Api::new();
    let acc = account(&mut api, &root);
    let chr = character(&mut api, &root, &acc, "Lutoren");
    let eq = format!("/v1/characters/{chr}/item-equipment");

    let (status, body) = api.call(&root, Method::Get, &eq, None);
    assert_eq!(status, 200);
    assert_eq!(body["equipment"], Value::Null);

    let belt = json!({
        "item_equipment_slot": "belt",
        "item_name": "Superior Engraved Gollux Belt",
        "starforce": 18, "starforce_max": 30,
        "item_total_option": { "str": 149, "all_stat": 4 },
        "item_base_option": { "str": 60, "base_equipment_level": 150 },
        "item_enhancement_option": { "str": 73 },
        "item_add_option": { "str": 15, "all_stat": 4 },
        "potential_option_grade": "unique",
        "potential_option_1": "STR: +9%"
    });
    let (status, body) = api.call(&root, Method::Put, &eq, Some(json!({ "item_equipment": [belt] })));
    assert_eq!(status, 200, "{body}");
    let item = &body["snapshot"]["equipment"]["item_equipment"][0];
    assert_eq!(item["item_total_option"]["all_stat"], 4.00);
    assert_eq!(item["item_total_option"].get("dex"), None, "absent stays absent");
    // A misread digit is recorded with a warning.
    assert_eq!(body["warnings"][0]["field"], "str");

    // Impossible windows are refused with the issues listed.
    let ring = json!({ "item_equipment_slot": "ring-1", "item_name": "Ring", "starforce": 18, "starforce_max": 17 });
    let (status, body) = api.call(&root, Method::Put, &eq, Some(json!({ "item_equipment": [ring, ring] })));
    assert_eq!(status, 422);
    assert_eq!(body["error"]["details"]["issues"][0]["field"], "starforce");
    for bad in [
        json!({ "item_equipment": [{ "item_equipment_slot": "ring-5", "item_name": "A" }] }),
        json!({ "item_equipment": [{ "item_equipment_slot": "hat", "item_name": "A", "stars": 1 }] }),
        json!({ "items": [] }),
    ] {
        assert_eq!(api.call(&root, Method::Put, &eq, Some(bad.clone())).0, 400, "{bad}");
    }

    let (status, _) = api.call(&root, Method::Put, &eq, Some(json!({ "item_equipment": [] })));
    assert_eq!(status, 200);
    let (_, body) = api.call(&root, Method::Get, &eq, None);
    assert_eq!(body["equipment"]["item_equipment"], json!([]));
    let (_, body) = api.call(&root, Method::Get, &format!("{eq}/history?limit=1"), None);
    let cursor = body["next_before"].as_str().unwrap();
    let (_, body) = api.call(&root, Method::Get, &format!("{eq}/history?before={cursor}"), None);
    assert_eq!(body["history"][0]["equipment"]["item_equipment"][0]["item_name"], "Superior Engraved Gollux Belt");

    let (_, body) = api.call(&root, Method::Get, "/v1/audit?action=equipment.replace", None);
    assert_eq!(body["events"].as_array().unwrap().len(), 2);
}

#[test]
fn planned_resources_answer_501() {
    let (mut api, root) = Api::new();
    let acc = account(&mut api, &root);
    let chr = character(&mut api, &root, &acc, "Lutoren");
    let (status, body) = api.call(&root, Method::Get, &format!("/v1/characters/{chr}/symbol-equipment"), None);
    assert_eq!(status, 501);
    assert_eq!(body["error"]["name"], "not_implemented");
}

#[test]
fn serves_over_a_real_socket() {
    let path = std::env::temp_dir().join(format!("msapi-test-{}.db", std::process::id()));
    let token = {
        let mut conn = db::open(&path).unwrap();
        auth::create_user(&mut conn, "socket").unwrap().1
    };
    let addr = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().to_string();
    let config = Config { addr: addr.clone(), db: path.clone(), workers: 2, trust_proxy: false, log: None };
    std::thread::spawn(move || serve::run(&config));

    let send = |request: &str| -> String {
        for _ in 0..50 {
            if let Ok(mut stream) = TcpStream::connect(&addr) {
                stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
                stream.write_all(request.as_bytes()).unwrap();
                let mut out = String::new();
                stream.read_to_string(&mut out).unwrap();
                return out;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        panic!("server did not start");
    };

    let body = r#"{"region":"gms"}"#;
    let res = send(&format!(
        "POST /v1/accounts HTTP/1.1\r\nHost: x\r\nAuthorization: Bearer {token}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    ));
    assert!(res.starts_with("HTTP/1.1 201"), "{res}");
    assert!(res.to_ascii_lowercase().contains("x-request-id: req_"), "{res}");

    let big = "x".repeat(serve::MAX_BODY + 1);
    let res = send(&format!(
        "POST /v1/accounts HTTP/1.1\r\nHost: x\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{big}",
        big.len()
    ));
    assert!(res.starts_with("HTTP/1.1 413"), "{res}");

    for suffix in ["", "-wal", "-shm"] {
        let _ = std::fs::remove_file(format!("{}{suffix}", path.display()));
    }
}

/// The JSON examples in the agent guide, in order.
fn doc_examples() -> Vec<Value> {
    include_str!("../../../docs/api.md")
        .split("```json\n")
        .skip(1)
        .map(|block| serde_json::from_str(block.split("```").next().unwrap()).unwrap())
        .collect()
}

#[test]
fn the_guide_examples_are_accepted() {
    let examples = doc_examples();
    let (mut api, root) = Api::new();
    let acc = account(&mut api, &root);

    let mint_example = &examples[0];
    let mut mint_body = mint_example.clone();
    mint_body["account_ids"] = json!([acc]);
    mint(&mut api, &root, mint_body);

    let (status, body) =
        api.call(&root, Method::Post, &format!("/v1/accounts/{acc}/characters"), Some(examples[1].clone()));
    assert_eq!(status, 201, "{body}");
    let chr = body["id"].as_str().unwrap().to_owned();

    let mut window = examples[2].clone();
    window["captured_at"] = Value::Null;
    let (status, body) = api.call(&root, Method::Put, &format!("/v1/characters/{chr}/stat"), Some(window));
    assert_eq!(status, 200, "{body}");
    assert_eq!(body["warnings"], json!([]), "the guide's example should be self-consistent");
}

#[test]
fn routing_statuses() {
    let (mut api, root) = Api::new();
    let cases: &[(Method, &str, &str, u16)] = &[
        (Method::Get, &root, "/health", 200),
        (Method::Post, &root, "/health", 405),
        (Method::Get, &root, "//v1//", 200),
        (Method::Get, &root, "/nope", 404),
        (Method::Put, &root, "/v1/characters", 405),
        (Method::Other, &root, "/v1/me", 405),
        (Method::Get, &root, "/v1/characters/chr_x/nope", 404),
        (Method::Post, &root, "/v1/characters/chr_x/hyper-stat", 405),
        (Method::Get, &root, "/v1/characters/chr_x/hyper-stat", 404),
        (Method::Get, &root, "/v1/auth/passkey/anything", 405),
        (Method::Post, &root, "/v1/auth/passkey/anything", 404),
        (Method::Get, "nope", "/v1/me", 401),
        (Method::Get, &root, "/v1/me", 200),
        (Method::Get, &root, "/v1/audit?limit=0", 400),
        (Method::Get, &root, "/v1/audit?limit=x", 400),
        (Method::Get, &root, "/v1/audit?limit=200", 200),
        (Method::Get, &root, "/v1/audit?token_id=x&include_descendants=maybe", 400),
    ];
    for &(method, token, target, want) in cases {
        let (status, body) = api.call(token, method, target, None);
        assert_eq!(status, want, "{method:?} {target}: {body}");
    }
}
