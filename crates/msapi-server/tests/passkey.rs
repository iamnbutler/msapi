//! Passkey sign-up and sign-in against a software authenticator.

#![allow(clippy::unwrap_used, reason = "tests fail loudly by design")]

use ring::digest::{SHA256, digest};
use ring::rand::SystemRandom;
use ring::signature::{ECDSA_P256_SHA256_ASN1_SIGNING, EcdsaKeyPair, KeyPair};
use rusqlite::Connection;
use serde_json::{Value, json};

use msapi_server::http::{Method, Request};
use msapi_server::passkey::{b64url, b64url_decode};
use msapi_server::{db, routes};

const ORIGIN: &str = "http://localhost:8080";
const RP_ID: &str = "localhost";

fn call(conn: &mut Connection, path: &str, body: &Value, token: Option<&str>) -> (u16, Value) {
    let mut req = Request::new(if body.is_null() { Method::Get } else { Method::Post }, path);
    if let Some(token) = token {
        req.headers.push(("authorization".into(), format!("Bearer {token}")));
    }
    if !body.is_null() {
        req.headers.push(("content-type".into(), "application/json".into()));
        req.body = serde_json::to_vec(body).unwrap();
    }
    let res = routes::handle(conn, &req);
    (res.status, if res.body.is_empty() { Value::Null } else { res.json_body().unwrap() })
}

/// A platform authenticator in software: one P-256 key and a counter.
struct Authenticator {
    key: EcdsaKeyPair,
    id: Vec<u8>,
    count: u32,
    rng: SystemRandom,
}

impl Authenticator {
    fn new() -> Self {
        let rng = SystemRandom::new();
        let pkcs8 = EcdsaKeyPair::generate_pkcs8(&ECDSA_P256_SHA256_ASN1_SIGNING, &rng).unwrap();
        let key = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_ASN1_SIGNING, pkcs8.as_ref(), &rng).unwrap();
        Self { key, id: vec![7; 20], count: 0, rng }
    }

    fn auth_data(&self, rp_id: &str, flags: u8, attested: bool) -> Vec<u8> {
        let mut data = digest(&SHA256, rp_id.as_bytes()).as_ref().to_vec();
        data.push(flags | if attested { 0x40 } else { 0 });
        data.extend(self.count.to_be_bytes());
        if attested {
            data.extend([0; 16]);
            data.extend(u16::try_from(self.id.len()).unwrap().to_be_bytes());
            data.extend(&self.id);
            let point = self.key.public_key().as_ref();
            // {1: 2, 3: -7, -1: 1, -2: x, -3: y}
            data.extend([0xa5, 0x01, 0x02, 0x03, 0x26, 0x20, 0x01, 0x21, 0x58, 0x20]);
            data.extend(&point[1..33]);
            data.extend([0x22, 0x58, 0x20]);
            data.extend(&point[33..65]);
        }
        data
    }

    fn client_data(kind: &str, options: &Value, origin: &str) -> Vec<u8> {
        serde_json::to_vec(&json!({
            "type": kind,
            "challenge": options["publicKey"]["challenge"],
            "origin": origin,
            "crossOrigin": false,
        }))
        .unwrap()
    }

    fn create(&self, options: &Value) -> Value {
        let auth_data = self.auth_data(RP_ID, 0x05, true);
        // {"fmt": "none", "attStmt": {}, "authData": h'…'}
        let mut object = vec![0xa3, 0x63];
        object.extend(b"fmt");
        object.push(0x64);
        object.extend(b"none");
        object.push(0x67);
        object.extend(b"attStmt");
        object.push(0xa0);
        object.push(0x68);
        object.extend(b"authData");
        object.extend([0x59]);
        object.extend(u16::try_from(auth_data.len()).unwrap().to_be_bytes());
        object.extend(&auth_data);
        json!({
            "id": b64url(&self.id),
            "rawId": b64url(&self.id),
            "type": "public-key",
            "response": {
                "clientDataJSON": b64url(&Self::client_data("webauthn.create", options, ORIGIN)),
                "attestationObject": b64url(&object),
            },
        })
    }

    fn get(&mut self, options: &Value, rp_id: &str, origin: &str) -> Value {
        self.count += 1;
        let auth_data = self.auth_data(rp_id, 0x05, false);
        let client = Self::client_data("webauthn.get", options, origin);
        let mut signed = auth_data.clone();
        signed.extend(digest(&SHA256, &client).as_ref());
        let sig = self.key.sign(&self.rng, &signed).unwrap();
        json!({
            "id": b64url(&self.id),
            "type": "public-key",
            "response": {
                "clientDataJSON": b64url(&client),
                "authenticatorData": b64url(&auth_data),
                "signature": b64url(sig.as_ref()),
                "userHandle": null,
            },
        })
    }
}

#[test]
fn sign_up_then_sign_in() {
    let mut conn = db::open_in_memory().unwrap();
    let mut device = Authenticator::new();

    let (status, options) =
        call(&mut conn, "/v1/auth/passkey/register/start", &json!({ "display_name": "Nate" }), None);
    assert_eq!(status, 200, "{options}");
    assert_eq!(options["publicKey"]["rp"]["id"], RP_ID);
    let user_handle = b64url_decode(options["publicKey"]["user"]["id"].as_str().unwrap()).unwrap();
    let credential = device.create(&options);
    let (status, session) =
        call(&mut conn, "/v1/auth/passkey/register/finish", &json!({ "credential": credential }), None);
    assert_eq!(status, 201, "{session}");
    assert_eq!(session["user_id"].as_str().unwrap().as_bytes(), user_handle);
    let token = session["token"].as_str().unwrap();

    // The session works like a root token.
    let (status, me) = call(&mut conn, "/v1/me", &Value::Null, Some(token));
    assert_eq!(status, 200, "{me}");
    let (status, account) = call(&mut conn, "/v1/accounts", &json!({ "region": "gms" }), Some(token));
    assert_eq!(status, 201, "{account}");

    // A challenge works once.
    let (status, _) = call(&mut conn, "/v1/auth/passkey/register/finish", &json!({ "credential": credential }), None);
    assert_eq!(status, 401);

    // Sign in.
    let (_, options) = call(&mut conn, "/v1/auth/passkey/login/start", &json!({}), None);
    let assertion = device.get(&options, RP_ID, ORIGIN);
    let (status, second) = call(&mut conn, "/v1/auth/passkey/login/finish", &json!({ "credential": assertion }), None);
    assert_eq!(status, 200, "{second}");
    assert_eq!(second["user_id"], session["user_id"]);
    assert_ne!(second["token"], session["token"]);

    // Replaying an old counter is refused even with a fresh challenge.
    device.count -= 1;
    let (_, options) = call(&mut conn, "/v1/auth/passkey/login/start", &json!({}), None);
    let replay = device.get(&options, RP_ID, ORIGIN);
    let (status, body) = call(&mut conn, "/v1/auth/passkey/login/finish", &json!({ "credential": replay }), None);
    assert_eq!(status, 401, "{body}");

    // Wrong origin, wrong relying party, and a tampered signature are refused.
    for (rp_id, origin) in [(RP_ID, "https://evil.example"), ("evil.example", ORIGIN)] {
        let (_, options) = call(&mut conn, "/v1/auth/passkey/login/start", &json!({}), None);
        let assertion = device.get(&options, rp_id, origin);
        let (status, body) =
            call(&mut conn, "/v1/auth/passkey/login/finish", &json!({ "credential": assertion }), None);
        assert_eq!(status, 401, "{body}");
    }
    let (_, options) = call(&mut conn, "/v1/auth/passkey/login/start", &json!({}), None);
    let mut assertion = device.get(&options, RP_ID, ORIGIN);
    let mut sig = b64url_decode(assertion["response"]["signature"].as_str().unwrap()).unwrap();
    let last = sig.len() - 1;
    sig[last] ^= 1;
    assertion["response"]["signature"] = b64url(&sig).into();
    let (status, _) = call(&mut conn, "/v1/auth/passkey/login/finish", &json!({ "credential": assertion }), None);
    assert_eq!(status, 401);

    // Sign-up and sign-in are in the audit log.
    let (status, audit) = call(&mut conn, "/v1/audit", &Value::Null, Some(token));
    assert_eq!(status, 200, "{audit}");
    let actions: Vec<&str> =
        audit["events"].as_array().unwrap().iter().map(|e| e["action"].as_str().unwrap()).collect();
    assert!(actions.contains(&"user.create") && actions.contains(&"session.create"), "{actions:?}");
}
