//! Signing up and signing in with a passkey (`WebAuthn`).
//!
//! ```text
//! POST /v1/auth/passkey/register/start   {"display_name"}       → {"publicKey": creation options}
//! POST /v1/auth/passkey/register/finish  {"credential"}         → session
//! POST /v1/auth/passkey/login/start      {}                     → {"publicKey": request options}
//! POST /v1/auth/passkey/login/finish     {"credential"}         → session
//! ```
//!
//! Options and credentials use the browser's JSON forms
//! (`PublicKeyCredential.parseCreationOptionsFromJSON`, `credential.toJSON()`):
//! binary fields are base64url. A session is a root token that expires after
//! thirty days ([`api::SESSION_MS`]); it can mint delegated tokens like any root token.
//!
//! Attestation is not requested, so registration trusts the key the browser
//! reports for this origin, as passkey sites generally do. Sign-in checks the
//! signature over the authenticator data and the client data hash, the
//! origin, the relying party, user presence and the signature counter (see
//! [`msapi_core::webauthn`] for the byte layouts and rules).

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_map,
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening or `Option` combinators"
)]

use std::sync::{Mutex, OnceLock, PoisonError};
use std::time::{Duration, Instant};

use foldhash::HashMap;
use ring::digest::{SHA256, digest};
use ring::signature::{self, RsaPublicKeyComponents, UnparsedPublicKey};
use rusqlite::{Connection, OptionalExtension, params};
use serde::Deserialize;
use serde_json::json;

use msapi_core::Timestamp;
use msapi_core::api::{self, Route};
use msapi_core::base64url;
use msapi_core::webauthn::{self, ALGORITHMS, Cbor, PublicKey};

use crate::audit::{Ctx, Target, Write};
use crate::auth::{Principal, Scopes};
use crate::error::ApiError;
use crate::http::{Request, Response, latin1};
use crate::ids;
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;

/// How long a ceremony may take, from start to finish.
const CEREMONY: Duration = Duration::from_secs(5 * 60);
/// Most ceremonies pending at once; starting more evicts expired ones first.
const MAX_PENDING: usize = 10_000;

/// The site passkeys are bound to.
#[derive(Clone, Debug)]
pub struct RelyingParty {
    /// The domain, e.g. `msapi.example.com`.
    pub id: String,
    /// The exact origin the browser reports, e.g. `https://msapi.example.com`.
    pub origin: String,
}

static RP: OnceLock<RelyingParty> = OnceLock::new();

/// Sets the relying party. Without this, passkeys are bound to
/// `localhost` and `http://localhost:8080`, for local development.
pub fn configure(rp: RelyingParty) {
    let _ = RP.set(rp);
}

fn rp() -> &'static RelyingParty {
    RP.get_or_init(|| RelyingParty { id: "localhost".to_owned(), origin: "http://localhost:8080".to_owned() })
}

enum Pending {
    Register { user_id: String, display_name: String },
    Login,
}

/// Ceremonies in progress, keyed by their challenge.
type Ceremonies = HashMap<Vec<u8>, (Pending, Instant)>;
static PENDING: OnceLock<Mutex<Ceremonies>> = OnceLock::new();

fn pending() -> std::sync::MutexGuard<'static, Ceremonies> {
    PENDING.get_or_init(Mutex::default).lock().unwrap_or_else(PoisonError::into_inner)
}

fn begin(ceremony: Pending) -> Result<Vec<u8>, ApiError> {
    let challenge = ids::random::<32>().to_vec();
    let mut pending = pending();
    if pending.len() >= MAX_PENDING {
        pending.retain(|_, (_, at)| at.elapsed() < CEREMONY);
        if pending.len() >= MAX_PENDING {
            return Err(ApiError::unavailable("too many sign-ins in progress; try again shortly"));
        }
    }
    pending.insert(challenge.clone(), (ceremony, Instant::now()));
    Ok(challenge)
}

/// Takes the ceremony a challenge belongs to. Each challenge works once.
fn finish(challenge: &[u8]) -> Result<Pending, ApiError> {
    match pending().remove(challenge) {
        Some((ceremony, at)) if at.elapsed() < CEREMONY => Ok(ceremony),
        _ => Err(ApiError::unauthorized("unknown or expired challenge; start again")),
    }
}

/// Answers a passkey route, or `None` if the path is not one.
pub fn handle(
    conn: &mut Connection,
    req: &Request,
    request_id: &str,
    route: Route,
) -> Option<Result<Response, ApiError>> {
    Some(match route {
        Route::RegisterStart => register_start(req),
        Route::RegisterFinish => register_finish(conn, req, request_id),
        Route::LoginStart => login_start(),
        Route::LoginFinish => login_finish(conn, req, request_id),
        _ => return None,
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RegisterStart {
    display_name: String,
}

fn register_start(req: &Request) -> Result<Response, ApiError> {
    let body: RegisterStart = req.json()?;
    let display_name = api::name_in(body.display_name.as_bytes(), 1, 64)
        .and_then(|(a, b)| body.display_name.get(a..b))
        .ok_or_else(|| ApiError::invalid("display_name must be 1-64 characters"))?
        .to_owned();
    let user_id = ids::new_id("usr");
    let options = json!({
        "rp": { "id": rp().id, "name": "msapi" },
        "user": { "id": b64url(user_id.as_bytes()), "name": display_name, "displayName": display_name },
        "pubKeyCredParams": ALGORITHMS.map(|alg| json!({ "type": "public-key", "alg": alg })),
        "authenticatorSelection": { "residentKey": "required", "requireResidentKey": true, "userVerification": "preferred" },
        "attestation": "none",
        "timeout": CEREMONY.as_millis(),
        "excludeCredentials": [],
    });
    let challenge = begin(Pending::Register { user_id, display_name })?;
    let mut options = options;
    options["challenge"] = b64url(&challenge).into();
    Ok(Response::json(200, &json!({ "publicKey": options })))
}

fn login_start() -> Result<Response, ApiError> {
    let challenge = begin(Pending::Login)?;
    Ok(Response::json(
        200,
        &json!({ "publicKey": {
            "challenge": b64url(&challenge),
            "rpId": rp().id,
            "userVerification": "preferred",
            "timeout": CEREMONY.as_millis(),
            "allowCredentials": [],
        }}),
    ))
}

/// `credential.toJSON()` from the browser.
#[derive(Deserialize)]
struct Credential {
    id: String,
    response: AuthenticatorResponse,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AuthenticatorResponse {
    #[serde(rename = "clientDataJSON")]
    client_data_json: String,
    #[serde(default)]
    attestation_object: Option<String>,
    #[serde(default)]
    authenticator_data: Option<String>,
    #[serde(default)]
    signature: Option<String>,
}

#[derive(Deserialize)]
struct Finish {
    credential: Credential,
}

#[derive(Deserialize)]
struct ClientData {
    #[serde(rename = "type")]
    kind: String,
    challenge: String,
    origin: String,
    #[serde(default, rename = "crossOrigin")]
    cross_origin: bool,
}

/// Checks the client data and returns it with the ceremony it finishes.
fn client_data(json: &[u8], kind: &str) -> Result<Pending, ApiError> {
    let data: ClientData =
        serde_json::from_slice(json).map_err(|e| ApiError::bad_request(format!("clientDataJSON: {e}")))?;
    if !webauthn::bytes_eq(data.kind.as_bytes(), kind.as_bytes()) {
        return Err(ApiError::bad_request(format!("clientDataJSON type is `{}`, expected `{kind}`", data.kind)));
    }
    let ceremony = finish(&b64url_decode(&data.challenge)?)?;
    if !webauthn::origin_ok(data.origin.as_bytes(), rp().origin.as_bytes(), data.cross_origin) {
        return Err(ApiError::unauthorized(format!("passkeys here are for {}, not {}", rp().origin, data.origin)));
    }
    Ok(ceremony)
}

/// The checks both ceremonies make on authenticator data, against this
/// site's relying-party ID hash.
fn check_auth_data(auth_data: &[u8]) -> Result<webauthn::AuthDataLayout, ApiError> {
    check_layout(auth_data, digest(&SHA256, rp().id.as_bytes()).as_ref())
}

/// The proven [`webauthn`] layout, RP-ID-hash and presence checks on
/// `auth_data`, with their refusals worded.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Err(e) ==> e.status == 400 || e.status == 401,
))]
fn check_layout(auth_data: &[u8], rp_id_hash: &[u8]) -> Result<webauthn::AuthDataLayout, ApiError> {
    let Some(layout) = webauthn::auth_data_layout(auth_data) else {
        return Err(ApiError::bad_request("authenticator data is truncated"));
    };
    if !webauthn::rp_id_hash_ok(auth_data, rp_id_hash) {
        return Err(ApiError::unauthorized("the passkey is for a different site"));
    }
    if !webauthn::presence_ok(layout.flags) {
        return Err(ApiError::unauthorized("the authenticator did not confirm user presence"));
    }
    Ok(layout)
}

fn register_finish(conn: &mut Connection, req: &Request, request_id: &str) -> Result<Response, ApiError> {
    let Finish { credential } = req.json()?;
    let Pending::Register { user_id, display_name } =
        client_data(&b64url_decode(&credential.response.client_data_json)?, "webauthn.create")?
    else {
        return Err(ApiError::bad_request("that challenge is for signing in, not signing up"));
    };

    let attestation = b64url_decode(credential.response.attestation_object.as_deref().unwrap_or_default())?;
    let (object, _) =
        Cbor::decode(&attestation).ok_or_else(|| ApiError::bad_request("attestationObject is not CBOR"))?;
    let auth_data = object
        .get_text(&attestation, b"authData")
        .and_then(|v| v.as_bytes(&attestation))
        .ok_or_else(|| ApiError::bad_request("attestationObject has no authData"))?;
    let layout = check_auth_data(&auth_data)?;
    if !webauthn::attested(layout.flags) {
        return Err(ApiError::bad_request("authenticator data has no credential"));
    }
    let id = &auth_data[layout.id_start..layout.id_end];
    if !webauthn::bytes_eq(&base64url::encode(id), credential.id.as_bytes()) {
        return Err(ApiError::bad_request("credential id does not match the authenticator data"));
    }
    let key_bytes = &auth_data[layout.id_end..];
    let (key, end) =
        Cbor::decode(key_bytes).ok_or_else(|| ApiError::bad_request("credential public key is not CBOR"))?;
    PublicKey::from_cose(&key, key_bytes)
        .ok_or_else(|| ApiError::invalid("unsupported key type; use ES256, Ed25519 or RS256"))?;
    let cose = &key_bytes[..end];

    let now = Timestamp::now().millis();
    let session = Session::new(user_id, now);
    let ctx = session.ctx(req, request_id, Route::RegisterFinish);
    let write = Write::begin(conn, &ctx)?;
    write.execute(
        "INSERT INTO users (id, display_name, created_at) VALUES (?1, ?2, ?3)",
        params![session.user_id, display_name, now],
    )?;
    write
        .execute(
            "INSERT INTO passkeys (id, user_id, public_key, sign_count, created_at) VALUES (?1, ?2, ?3, ?4, ?5)",
            params![credential.id, session.user_id, cose, layout.sign_count, now],
        )
        .map_err(|e| {
            if is_primary_key_violation(&e) {
                ApiError::conflict("this passkey is already registered")
            } else {
                e.into()
            }
        })?;
    session.insert(&write)?;
    let after = json!({ "user_id": session.user_id, "display_name": display_name, "passkey": credential.id });
    write.commit(None, Target { kind: "user", id: &session.user_id }, None::<&()>, Some(&after))?;
    Ok(session.response(201, &display_name))
}

fn login_finish(conn: &mut Connection, req: &Request, request_id: &str) -> Result<Response, ApiError> {
    let Finish { credential } = req.json()?;
    let client_json = b64url_decode(&credential.response.client_data_json)?;
    let Pending::Login = client_data(&client_json, "webauthn.get")? else {
        return Err(ApiError::bad_request("that challenge is for signing up, not signing in"));
    };
    let auth_data = b64url_decode(credential.response.authenticator_data.as_deref().unwrap_or_default())?;
    let sig = b64url_decode(credential.response.signature.as_deref().unwrap_or_default())?;
    let layout = check_auth_data(&auth_data)?;

    let row: Option<(String, Vec<u8>, i64, String)> = conn
        .query_row(
            "SELECT p.user_id, p.public_key, p.sign_count, u.display_name
             FROM passkeys p JOIN users u ON u.id = p.user_id WHERE p.id = ?1",
            [&credential.id],
            |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?)),
        )
        .optional()?;
    let Some((user_id, cose, stored_count, display_name)) = row else {
        return Err(ApiError::unauthorized("unknown passkey"));
    };

    let mut signed = auth_data.clone();
    signed.extend_from_slice(digest(&SHA256, &client_json).as_ref());
    let (key, _) = Cbor::decode(&cose).ok_or_else(ApiError::internal)?;
    let key = PublicKey::from_cose(&key, &cose).ok_or_else(ApiError::internal)?;
    if !verify(&key, &signed, &sig) {
        return Err(ApiError::unauthorized("the passkey's signature does not verify"));
    }
    let stored_count = u32::try_from(stored_count).unwrap_or(u32::MAX);
    if !webauthn::counter_ok(stored_count, layout.sign_count) {
        return Err(ApiError::unauthorized("the passkey's signature counter went backwards; it may have been cloned"));
    }

    let now = Timestamp::now().millis();
    let session = Session::new(user_id, now);
    let ctx = session.ctx(req, request_id, Route::LoginFinish);
    let write = Write::begin(conn, &ctx)?;
    write.execute(
        "UPDATE passkeys SET sign_count = ?2, last_used_at = ?3 WHERE id = ?1",
        params![credential.id, layout.sign_count, now],
    )?;
    session.insert(&write)?;
    let after = json!({ "token_id": session.token_id, "passkey": credential.id });
    write.commit(None, Target { kind: "token", id: &session.token_id }, None::<&()>, Some(&after))?;
    Ok(session.response(200, &display_name))
}

fn verify(key: &PublicKey, message: &[u8], sig: &[u8]) -> bool {
    match key {
        PublicKey::Es256 { x, y } => {
            let point = webauthn::es256_point(x, y);
            UnparsedPublicKey::new(&signature::ECDSA_P256_SHA256_ASN1, point).verify(message, sig).is_ok()
        }
        PublicKey::Ed25519 { x } => UnparsedPublicKey::new(&signature::ED25519, x).verify(message, sig).is_ok(),
        PublicKey::Rs256 { n, e } => {
            RsaPublicKeyComponents { n, e }.verify(&signature::RSA_PKCS1_2048_8192_SHA256, message, sig).is_ok()
        }
    }
}

/// A new root token for a user who just proved who they are.
struct Session {
    user_id: String,
    token_id: String,
    secret: String,
    created_at: i64,
    expires_at: i64,
}

impl Session {
    fn new(user_id: String, now: i64) -> Self {
        Self {
            user_id,
            token_id: ids::new_id("tok"),
            secret: ids::new_token_secret(),
            created_at: now,
            expires_at: api::session_expiry(now),
        }
    }

    fn ctx(&self, req: &Request, request_id: &str, route: Route) -> Ctx {
        Ctx {
            principal: Principal {
                user_id: self.user_id.clone(),
                token_id: self.token_id.clone(),
                label: "passkey session".to_owned(),
                root: true,
                scopes: Scopes::all(),
                account_ids: None,
                expires_at: Some(Timestamp::from_millis(self.expires_at)),
            },
            request_id: request_id.to_owned(),
            method: req.method,
            path: req.path.clone(),
            client: req.client.clone(),
            user_agent: req.header("user-agent").map(str::to_owned),
            action: api::action(route).map_or("", crate::http::word),
        }
    }

    fn insert(&self, write: &Write<'_>) -> rusqlite::Result<()> {
        write.execute(
            "INSERT INTO tokens (id, user_id, parent_id, label, scopes, account_ids, secret_hash, created_at, expires_at)
             VALUES (?1, ?2, NULL, 'passkey session', ?3, NULL, ?4, ?5, ?6)",
            params![
                self.token_id,
                self.user_id,
                Scopes::all().to_string(),
                ids::hash_token(&self.secret),
                self.created_at,
                self.expires_at
            ],
        )?;
        Ok(())
    }

    fn response(&self, status: u16, display_name: &str) -> Response {
        Response::json(
            status,
            &json!({
                "user_id": self.user_id,
                "display_name": display_name,
                "token": self.secret,
                "token_id": self.token_id,
                "expires_at": Timestamp::from_millis(self.expires_at),
            }),
        )
    }
}

fn is_primary_key_violation(err: &rusqlite::Error) -> bool {
    matches!(err, rusqlite::Error::SqliteFailure(e, _) if e.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_PRIMARYKEY)
}

/// Base64url without padding.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@.len() == base64url::encode_spec(bytes@).len(),
        forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] == (base64url::encode_spec(bytes@)[i] as char),
))]
#[must_use]
pub fn b64url(bytes: &[u8]) -> String {
    latin1(&base64url::encode(bytes))
}

/// Decodes base64url, with or without padding.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Ok(b) => base64url::encode_spec(b@) == base64url::unpadded(text.spec_bytes()),
            Err(e) => e.status == 400 && forall|b: Seq<u8>| base64url::encode_spec(b) != base64url::unpadded(text.spec_bytes()),
        }
))]
pub fn b64url_decode(text: &str) -> Result<Vec<u8>, ApiError> {
    match base64url::decode(text.as_bytes()) {
        Some(bytes) => Ok(bytes),
        None => Err(ApiError::bad_request("expected base64url")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64url_round_trips() {
        for len in 0..40u8 {
            let bytes: Vec<u8> = (0..len).map(|i| i.wrapping_mul(37).wrapping_add(250)).collect();
            assert_eq!(b64url_decode(&b64url(&bytes)).ok(), Some(bytes));
        }
        assert_eq!(b64url(b"hello?>"), "aGVsbG8_Pg");
        assert!(b64url_decode("a").is_err());
        assert!(b64url_decode("a+b/").is_err());
    }
}
