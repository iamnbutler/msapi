//! API errors, shaped like the Nexon Open API's: `{"error": {"name", "message"}}`.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    reason = "Verus checks plain casts and `push_str`; it has no spec for `From` widening or `String::push` of a literal"
)]

use std::fmt;

use serde::Serialize;

use msapi_core::Issue;
use msapi_core::msg::push_uint;
#[cfg(feature = "verus")]
use msapi_core::msg::uint_chars;
#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::http::Response;

/// An error that becomes an HTTP response.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, Clone)]
pub struct ApiError {
    /// HTTP status.
    pub status: u16,
    /// Stable machine-readable name, e.g. `"not_found"`.
    pub name: &'static str,
    /// Human-readable explanation.
    pub message: String,
    /// The validation issues behind a 422, if any.
    pub details: Option<Vec<Issue>>,
}

#[derive(Serialize)]
struct Envelope<'a> {
    error: Body<'a>,
}

#[derive(Serialize)]
struct Body<'a> {
    name: &'a str,
    message: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    details: Option<Details<'a>>,
}

#[derive(Serialize)]
struct Details<'a> {
    issues: &'a [Issue],
}

#[cfg_attr(feature = "verus", verus_verify)]
impl ApiError {
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == status, r.name == name, r.details is None))]
    fn new(status: u16, name: &'static str, message: impl Into<String>) -> Self {
        Self { status, name, message: message.into(), details: None }
    }

    /// 503: try again shortly.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 503, r.name == "unavailable", r.details is None))]
    pub fn unavailable(message: impl Into<String>) -> Self {
        Self::new(503, "unavailable", message)
    }

    /// Attaches the validation issues behind the error.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == self.status, r.name == self.name, r.message == self.message, r.details == Some(issues)))]
    #[must_use]
    pub fn with_details(mut self, issues: Vec<Issue>) -> Self {
        self.details = Some(issues);
        self
    }

    /// 400: the request is malformed.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 400, r.name == "bad_request", r.details is None))]
    pub fn bad_request(message: impl Into<String>) -> Self {
        Self::new(400, "bad_request", message)
    }

    /// 401: no usable credential.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 401, r.name == "unauthorized", r.details is None))]
    pub fn unauthorized(message: impl Into<String>) -> Self {
        Self::new(401, "unauthorized", message)
    }

    /// 403: the credential lacks a scope or cannot reach the resource.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 403, r.name == "forbidden", r.details is None))]
    pub fn forbidden(message: impl Into<String>) -> Self {
        Self::new(403, "forbidden", message)
    }

    /// 405.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 405, r.name == "method_not_allowed", r.details is None))]
    #[must_use]
    pub fn method_not_allowed() -> Self {
        Self::new(405, "method_not_allowed", "method not allowed on this path")
    }

    /// 409: conflicts with existing data.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 409, r.name == "conflict", r.details is None))]
    pub fn conflict(message: impl Into<String>) -> Self {
        Self::new(409, "conflict", message)
    }

    /// 422: well-formed but invalid.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 422, r.name == "invalid", r.details is None))]
    pub fn invalid(message: impl Into<String>) -> Self {
        Self::new(422, "invalid", message)
    }

    /// 501: a planned resource that does not exist yet.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 501, r.name == "not_implemented", r.details is None))]
    pub fn not_implemented(message: impl Into<String>) -> Self {
        Self::new(501, "not_implemented", message)
    }

    /// 500. The message is generic; the cause is logged, not returned.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.status == 500, r.name == "internal", r.details is None))]
    #[must_use]
    pub fn internal() -> Self {
        Self::new(500, "internal", "internal error; see the server log with this request's x-request-id")
    }

    /// 404: `what` names the missing thing, e.g. ``account `acc_1` ``.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r.status == 404, r.name == "not_found", r.details is None, r.message@ == what@ + " not found"@
    ))]
    #[must_use]
    pub fn not_found(what: &str) -> Self {
        let mut m = String::new();
        m.push_str(what);
        m.push_str(" not found");
        proof! { assert(Seq::<char>::empty() + what@ =~= what@); }
        Self { status: 404, name: "not_found", message: m, details: None }
    }

    /// 404 for a resource of kind `kind` with ID `id`: ``account `acc_1` not found``.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r.status == 404, r.name == "not_found", r.details is None,
            r.message@ == kind@ + " `"@ + id@ + "` not found"@,
    ))]
    #[must_use]
    pub fn not_found_id(kind: &str, id: &str) -> Self {
        let mut m = String::new();
        m.push_str(kind);
        m.push_str(" `");
        m.push_str(id);
        m.push_str("` not found");
        proof! { assert(Seq::<char>::empty() + kind@ =~= kind@); }
        Self { status: 404, name: "not_found", message: m, details: None }
    }

    /// 404 for a path no route answers: `route /v1/nope not found`.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r.status == 404, r.name == "not_found", r.details is None, r.message@ == "route "@ + path@ + " not found"@
    ))]
    #[must_use]
    pub fn not_found_route(path: &str) -> Self {
        let mut m = String::new();
        m.push_str("route ");
        m.push_str(path);
        m.push_str(" not found");
        Self { status: 404, name: "not_found", message: m, details: None }
    }

    /// 413.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r.status == 413, r.name == "payload_too_large", r.details is None,
            r.message@ == "body exceeds "@ + uint_chars(limit as nat) + " bytes"@,
    ))]
    #[must_use]
    pub fn too_large(limit: usize) -> Self {
        let mut m = String::new();
        m.push_str("body exceeds ");
        push_uint(&mut m, limit as u128);
        m.push_str(" bytes");
        Self { status: 413, name: "payload_too_large", message: m, details: None }
    }

    /// 415.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r.status == 415, r.name == "unsupported_media_type", r.details is None,
            r.message@ == "expected application/json, got `"@ + ct@ + "`"@,
    ))]
    #[must_use]
    pub fn unsupported_media_type(ct: &str) -> Self {
        let mut m = String::new();
        m.push_str("expected application/json, got `");
        m.push_str(ct);
        m.push_str("`");
        Self { status: 415, name: "unsupported_media_type", message: m, details: None }
    }

    /// The one-line description `Display` writes: `404 not_found: ...`.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r@ == uint_chars(self.status as nat) + " "@ + self.name@ + ": "@ + self.message@
    ))]
    #[must_use]
    pub fn describe(&self) -> String {
        let mut m = String::new();
        push_uint(&mut m, self.status as u128);
        m.push_str(" ");
        m.push_str(self.name);
        m.push_str(": ");
        m.push_str(self.message.as_str());
        proof! { assert(Seq::<char>::empty() + uint_chars(self.status as nat) =~= uint_chars(self.status as nat)); }
        m
    }
}

impl ApiError {
    /// 400: the body is not valid JSON for this route. Serde's message names
    /// the offending field, which is what an agent needs to fix it.
    #[must_use]
    pub fn invalid_json(err: &serde_json::Error) -> Self {
        Self::new(400, "invalid_body", err.to_string())
    }

    /// The response.
    #[must_use]
    pub fn to_response(&self) -> Response {
        let envelope = Envelope {
            error: Body {
                name: self.name,
                message: &self.message,
                details: self.details.as_deref().map(|issues| Details { issues }),
            },
        };
        Response::json(self.status, &envelope)
    }
}

impl fmt::Display for ApiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.describe())
    }
}

impl std::error::Error for ApiError {}

impl From<rusqlite::Error> for ApiError {
    fn from(err: rusqlite::Error) -> Self {
        eprintln!("database error: {err}");
        Self::internal()
    }
}

// The conversion is checked, but claims no spec beyond what `invalid` ensures.
#[cfg(feature = "verus")]
verus! {

impl vstd::std_specs::convert::FromSpecImpl<String> for ApiError {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    uninterp spec fn from_spec(message: String) -> Self;
}

} // verus!

/// Converts a validation message from `msapi-core` into a 422.
#[cfg_attr(feature = "verus", verus_verify)]
impl From<String> for ApiError {
    fn from(message: String) -> Self {
        Self::invalid(message)
    }
}
