//! API errors, shaped like the Nexon Open API's: `{"error": {"name", "message"}}`.

use std::fmt;

use serde::Serialize;

use msapi_core::Issue;
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
}

impl ApiError {
    /// 400: the body is not valid JSON for this route. Serde's message names
    /// the offending field, which is what an agent needs to fix it.
    #[must_use]
    pub fn invalid_json(err: &serde_json::Error) -> Self {
        Self::new(400, "invalid_body", err.to_string())
    }

    /// 404.
    pub fn not_found(what: impl fmt::Display) -> Self {
        Self::new(404, "not_found", format!("{what} not found"))
    }

    /// 413.
    #[must_use]
    pub fn too_large(limit: usize) -> Self {
        Self::new(413, "payload_too_large", format!("body exceeds {limit} bytes"))
    }

    /// 415.
    #[must_use]
    pub fn unsupported_media_type(ct: &str) -> Self {
        Self::new(415, "unsupported_media_type", format!("expected application/json, got `{ct}`"))
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
        write!(f, "{} {}: {}", self.status, self.name, self.message)
    }
}

impl std::error::Error for ApiError {}

impl From<rusqlite::Error> for ApiError {
    fn from(err: rusqlite::Error) -> Self {
        eprintln!("database error: {err}");
        Self::internal()
    }
}

/// Converts a validation message from `msapi-core` into a 422.
impl From<String> for ApiError {
    fn from(message: String) -> Self {
        Self::invalid(message)
    }
}
