//! Transport-independent request and response types.

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::error::ApiError;

/// HTTP methods the API distinguishes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Method {
    /// GET.
    Get,
    /// POST.
    Post,
    /// PUT.
    Put,
    /// PATCH.
    Patch,
    /// DELETE.
    Delete,
    /// Anything else.
    Other,
}

impl Method {
    /// Parses a method name.
    #[must_use]
    pub fn parse(s: &str) -> Self {
        match s {
            "GET" | "HEAD" => Self::Get,
            "POST" => Self::Post,
            "PUT" => Self::Put,
            "PATCH" => Self::Patch,
            "DELETE" => Self::Delete,
            _ => Self::Other,
        }
    }

    /// The method name.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Get => "GET",
            Self::Post => "POST",
            Self::Put => "PUT",
            Self::Patch => "PATCH",
            Self::Delete => "DELETE",
            Self::Other => "OTHER",
        }
    }

    /// Whether the method can change data.
    #[must_use]
    pub const fn is_write(self) -> bool {
        matches!(self, Self::Post | Self::Put | Self::Patch | Self::Delete)
    }
}

/// An incoming request, already read off the socket.
#[derive(Clone, Debug)]
pub struct Request {
    /// The method.
    pub method: Method,
    /// The path, without the query string.
    pub path: String,
    /// Decoded query parameters, in order.
    pub query: Vec<(String, String)>,
    /// Headers, names lowercased.
    pub headers: Vec<(String, String)>,
    /// The body.
    pub body: Vec<u8>,
    /// The client address, when known.
    pub client: Option<String>,
}

impl Request {
    /// A request with no headers, query or body.
    #[must_use]
    pub fn new(method: Method, target: &str) -> Self {
        let (path, query) = target.split_once('?').unwrap_or((target, ""));
        Self {
            method,
            path: path.to_owned(),
            query: parse_query(query),
            headers: Vec::new(),
            body: Vec::new(),
            client: None,
        }
    }

    /// The first header with this (lowercase) name.
    #[must_use]
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers.iter().find(|(k, _)| k == name).map(|(_, v)| v.as_str())
    }

    /// The first query parameter with this name.
    #[must_use]
    pub fn query(&self, name: &str) -> Option<&str> {
        self.query.iter().find(|(k, _)| k == name).map(|(_, v)| v.as_str())
    }

    /// Deserializes the body as JSON.
    pub fn json<T: DeserializeOwned>(&self) -> Result<T, ApiError> {
        if self.body.is_empty() {
            return Err(ApiError::bad_request("expected a JSON body"));
        }
        if let Some(ct) = self.header("content-type")
            && !ct.starts_with("application/json")
            && !ct.starts_with("application/merge-patch+json")
        {
            return Err(ApiError::unsupported_media_type(ct));
        }
        serde_json::from_slice(&self.body).map_err(|e| ApiError::invalid_json(&e))
    }
}

/// Splits and percent-decodes a query string.
#[must_use]
pub fn parse_query(query: &str) -> Vec<(String, String)> {
    query
        .split('&')
        .filter(|p| !p.is_empty())
        .map(|pair| {
            let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
            (percent_decode(k), percent_decode(v))
        })
        .collect()
}

fn hex(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => out.push(b' '),
            b'%' => match (bytes.get(i + 1).copied().and_then(hex), bytes.get(i + 2).copied().and_then(hex)) {
                (Some(hi), Some(lo)) => {
                    out.push(hi << 4 | lo);
                    i += 2;
                }
                _ => out.push(b'%'),
            },
            b => out.push(b),
        }
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// An outgoing response.
#[derive(Clone, Debug)]
pub struct Response {
    /// Status code.
    pub status: u16,
    /// Headers beyond `content-type`.
    pub headers: Vec<(&'static str, String)>,
    /// `content-type`.
    pub content_type: &'static str,
    /// The body.
    pub body: Vec<u8>,
}

impl Response {
    /// A JSON response.
    #[must_use]
    pub fn json(status: u16, value: &impl Serialize) -> Self {
        // Serializing our own response types cannot fail: they contain no maps
        // with non-string keys and no custom serializers that error.
        let body = serde_json::to_vec_pretty(value).unwrap_or_else(|_| b"{}".to_vec());
        Self { status, headers: Vec::new(), content_type: "application/json", body }
    }

    /// A plain-text or markdown response.
    #[must_use]
    pub fn text(status: u16, content_type: &'static str, body: impl Into<Vec<u8>>) -> Self {
        Self { status, headers: Vec::new(), content_type, body: body.into() }
    }

    /// `204 No Content`.
    #[must_use]
    pub fn no_content() -> Self {
        Self { status: 204, headers: Vec::new(), content_type: "application/json", body: Vec::new() }
    }

    /// Adds a header.
    #[must_use]
    pub fn with_header(mut self, name: &'static str, value: impl Into<String>) -> Self {
        self.headers.push((name, value.into()));
        self
    }

    /// The body parsed as JSON, for tests.
    pub fn json_body(&self) -> serde_json::Result<serde_json::Value> {
        serde_json::from_slice(&self.body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_decoding() {
        let q = parse_query("a=1&b=hello%20world&c=x+y&d&e=%zz&f=%4");
        assert_eq!(
            q,
            vec![
                ("a".into(), "1".into()),
                ("b".into(), "hello world".into()),
                ("c".into(), "x y".into()),
                ("d".into(), String::new()),
                ("e".into(), "%zz".into()),
                ("f".into(), "%4".into()),
            ]
        );
    }
}
