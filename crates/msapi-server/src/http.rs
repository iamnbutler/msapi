//! Transport-independent request and response types.

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::error::ApiError;

pub use msapi_core::api::Method;
use msapi_core::api::{self, Word};
use msapi_core::webauthn::bytes_eq;
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(feature = "verus")]
use vstd::utf8::encode_utf8;

/// A word of the API's vocabulary (a method, an action name) as text.
#[must_use]
pub fn word(w: Word) -> &'static str {
    // Every word is ASCII, which the core tests check.
    std::str::from_utf8(api::word_bytes(w)).unwrap_or("")
}

/// The method name.
#[must_use]
pub fn method_name(m: Method) -> &'static str {
    word(m.word())
}

/// An incoming request, already read off the socket.
#[cfg_attr(feature = "verus", verus_verify)]
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

    /// Deserializes the body as JSON.
    pub fn json<T: DeserializeOwned>(&self) -> Result<T, ApiError> {
        if self.body.is_empty() {
            return Err(ApiError::bad_request("expected a JSON body"));
        }
        if let Some(ct) = self.header("content-type")
            && !api::json_type(ct.as_bytes())
        {
            return Err(ApiError::unsupported_media_type(ct));
        }
        serde_json::from_slice(&self.body).map_err(|e| ApiError::invalid_json(&e))
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Request {
    /// The first header with this (lowercase) name.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures chars(r) == first(self.headers@, name.spec_bytes())))]
    #[must_use]
    pub fn header(&self, name: &str) -> Option<&str> {
        lookup(&self.headers, name)
    }

    /// The first query parameter with this name.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures chars(r) == first(self.query@, name.spec_bytes())))]
    #[must_use]
    pub fn query(&self, name: &str) -> Option<&str> {
        lookup(&self.query, name)
    }
}

#[cfg(feature = "verus")]
verus! {

/// The index of the first pair whose name's UTF-8 bytes are `name`, if any.
pub open spec fn first_index(pairs: Seq<(String, String)>, name: Seq<u8>) -> Option<int>
    decreases pairs.len()
{
    if pairs.len() == 0 {
        None
    } else if encode_utf8(pairs[0].0@) == name {
        Some(0)
    } else {
        match first_index(pairs.drop_first(), name) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// The value of the first pair named `name`, as its characters.
pub open spec fn first(pairs: Seq<(String, String)>, name: Seq<u8>) -> Option<Seq<char>> {
    match first_index(pairs, name) {
        Some(i) => Some(pairs[i].1@),
        None => None,
    }
}

/// The characters of an optional `&str`.
pub open spec fn chars(o: Option<&str>) -> Option<Seq<char>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// The UTF-8 bytes of optional characters.
pub open spec fn utf8(o: Option<Seq<char>>) -> Option<Seq<u8>> {
    match o {
        Some(c) => Some(encode_utf8(c)),
        None => None,
    }
}

/// `first_index` once the pairs before `i` are known not to match.
proof fn lemma_first_index_from(pairs: Seq<(String, String)>, name: Seq<u8>, i: int)
    requires
        0 <= i <= pairs.len(),
        forall|j: int| 0 <= j < i ==> encode_utf8(#[trigger] pairs[j].0@) != name,
    ensures
        i == pairs.len() ==> first_index(pairs, name) is None,
        i < pairs.len() && encode_utf8(pairs[i].0@) == name ==> first_index(pairs, name) == Some(i),
    decreases i
{
    if i > 0 {
        assert(encode_utf8(pairs[0].0@) != name);
        let rest = pairs.drop_first();
        assert forall|j: int| 0 <= j < i - 1 implies encode_utf8(#[trigger] rest[j].0@) != name by {
            assert(rest[j] == pairs[j + 1]);
        }
        if i < pairs.len() {
            assert(rest[i - 1] == pairs[i]);
        }
        lemma_first_index_from(rest, name, i - 1);
    }
}

} // verus!

/// The value of the first pair named `name`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures chars(r) == first(pairs@, name.spec_bytes())))]
fn lookup<'a>(pairs: &'a [(String, String)], name: &str) -> Option<&'a str> {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= pairs@.len(),
            forall|j: int| 0 <= j < i ==> encode_utf8(#[trigger] pairs@[j].0@) != name.spec_bytes(),
        decreases pairs@.len() - i
    ))]
    while i < pairs.len() {
        // vstd specifies `str::as_bytes`, not `String::as_bytes`.
        #[allow(clippy::redundant_as_str, reason = "Verus needs the `&str` step")]
        if bytes_eq(pairs[i].0.as_str().as_bytes(), name.as_bytes()) {
            proof! { lemma_first_index_from(pairs@, name.spec_bytes(), i as int); }
            return Some(pairs[i].1.as_str());
        }
        i += 1;
    }
    proof! { lemma_first_index_from(pairs@, name.spec_bytes(), i as int); }
    None
}

/// Bytes as the characters with those code points; the encoders' ASCII output
/// as text.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@.len() == bytes@.len(),
        forall|i: int| 0 <= i < bytes@.len() ==> #[trigger] r@[i] == (bytes@[i] as char),
))]
#[must_use]
pub fn latin1(bytes: &[u8]) -> String {
    let mut out = String::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= bytes@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == (bytes@[j] as char),
        decreases bytes@.len() - i
    ))]
    while i < bytes.len() {
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

/// Splits and percent-decodes a query string.
#[must_use]
pub fn parse_query(query: &str) -> Vec<(String, String)> {
    let text = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
    msapi_core::query::parse_query(query.as_bytes()).into_iter().map(|p| (text(&p.name), text(&p.value))).collect()
}

/// An outgoing response.
#[cfg_attr(feature = "verus", verus_verify)]
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

#[cfg_attr(feature = "verus", verus_verify)]
impl Response {
    /// A plain-text or markdown response.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r.status == status, r.headers@.len() == 0, r.content_type == content_type
    ))]
    #[must_use]
    pub fn text(status: u16, content_type: &'static str, body: impl Into<Vec<u8>>) -> Self {
        Self { status, headers: Vec::new(), content_type, body: body.into() }
    }

    /// `204 No Content`.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r.status == 204, r.headers@.len() == 0, r.content_type == "application/json", r.body@.len() == 0
    ))]
    #[must_use]
    pub fn no_content() -> Self {
        Self { status: 204, headers: Vec::new(), content_type: "application/json", body: Vec::new() }
    }

    /// Adds a header.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r.status == self.status,
            r.content_type == self.content_type,
            r.body == self.body,
            r.headers@.len() == self.headers@.len() + 1,
            r.headers@.take(self.headers@.len() as int) == self.headers@,
            r.headers@.last().0 == name,
    ))]
    #[must_use]
    pub fn with_header(mut self, name: &'static str, value: impl Into<String>) -> Self {
        self.headers.push((name, value.into()));
        self
    }
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
