//! API errors, shaped like the Nexon Open API's: `{"error": {"name", "message"}}`.

use std::fmt;

use serde::Serialize;
use serde_json::Value;

use crate::http::Response;

/// An error that becomes an HTTP response.
#[derive(Debug, Clone)]
pub struct ApiError {
    /// HTTP status.
    pub status: u16,
    /// Stable machine-readable name, e.g. `"not_found"`.
    pub name: &'static str,
    /// Human-readable explanation.
    pub message: String,
    /// Structured detail, such as validation issues.
    pub details: Option<Value>,
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
    details: Option<&'a Value>,
}

impl ApiError {
    fn new(status: u16, name: &'static str, message: impl Into<String>) -> Self {
        Self { status, name, message: message.into(), details: None }
    }

    /// Attaches structured detail.
    #[must_use]
    pub fn with_details(mut self, details: Value) -> Self {
        self.details = Some(details);
        self
    }

    /// 400: the request is malformed.
    pub fn bad_request(message: impl Into<String>) -> Self {
        Self::new(400, "bad_request", message)
    }

    /// 400: the body is not valid JSON for this route. Serde's message names
    /// the offending field, which is what an agent needs to fix it.
    #[must_use]
    pub fn invalid_json(err: &serde_json::Error) -> Self {
        Self::new(400, "invalid_body", err.to_string())
    }

    /// 401: no usable credential.
    pub fn unauthorized(message: impl Into<String>) -> Self {
        Self::new(401, "unauthorized", message)
    }

    /// 403: the credential lacks a scope or cannot reach the resource.
    pub fn forbidden(message: impl Into<String>) -> Self {
        Self::new(403, "forbidden", message)
    }

    /// 404.
    pub fn not_found(what: impl fmt::Display) -> Self {
        Self::new(404, "not_found", format!("{what} not found"))
    }

    /// 405.
    #[must_use]
    pub fn method_not_allowed() -> Self {
        Self::new(405, "method_not_allowed", "method not allowed on this path")
    }

    /// 409: conflicts with existing data.
    pub fn conflict(message: impl Into<String>) -> Self {
        Self::new(409, "conflict", message)
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

    /// 422: well-formed but invalid.
    pub fn invalid(message: impl Into<String>) -> Self {
        Self::new(422, "invalid", message)
    }

    /// 501: a planned resource that does not exist yet.
    pub fn not_implemented(message: impl Into<String>) -> Self {
        Self::new(501, "not_implemented", message)
    }

    /// 500. The message is generic; the cause is logged, not returned.
    #[must_use]
    pub fn internal() -> Self {
        Self::new(500, "internal", "internal error; see the server log with this request's x-request-id")
    }

    /// The response.
    #[must_use]
    pub fn to_response(&self) -> Response {
        let envelope =
            Envelope { error: Body { name: self.name, message: &self.message, details: self.details.as_ref() } };
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
