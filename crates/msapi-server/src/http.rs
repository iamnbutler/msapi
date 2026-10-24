//! Transport-independent request and response types.

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::error::ApiError;

pub use msapi_core::api::Method;
use msapi_core::api::{self, Word};
use msapi_core::msg;
#[cfg(feature = "verus")]
use msapi_core::msg::lemma_boundary_after_ascii;
use msapi_core::webauthn::bytes_eq;
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(feature = "verus")]
use vstd::utf8::{
    encode_utf8, encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, valid_utf8,
};

/// A word of the API's vocabulary (a method, an action name) as text: the
/// characters of the proven [`api::word_bytes`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == msapi_core::msg::chars(api::word(w))))]
#[cfg_attr(feature = "verus", verifier::rlimit(400))]
#[allow(clippy::too_many_lines, reason = "one arm per word, each with its proof")]
#[must_use]
pub fn word(w: Word) -> &'static str {
    match w {
        Word::V1 => {
            proof! {
                reveal_strlit("v1");
                assert("v1"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "v1"
        }
        Word::Me => {
            proof! {
                reveal_strlit("me");
                assert("me"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "me"
        }
        Word::Tokens => {
            proof! {
                reveal_strlit("tokens");
                assert("tokens"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "tokens"
        }
        Word::Audit => {
            proof! {
                reveal_strlit("audit");
                assert("audit"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "audit"
        }
        Word::Accounts => {
            proof! {
                reveal_strlit("accounts");
                assert("accounts"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "accounts"
        }
        Word::Characters => {
            proof! {
                reveal_strlit("characters");
                assert("characters"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "characters"
        }
        Word::Stat => {
            proof! {
                reveal_strlit("stat");
                assert("stat"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "stat"
        }
        Word::History => {
            proof! {
                reveal_strlit("history");
                assert("history"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "history"
        }
        Word::Health => {
            proof! {
                reveal_strlit("health");
                assert("health"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "health"
        }
        Word::Docs => {
            proof! {
                reveal_strlit("docs");
                assert("docs"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "docs"
        }
        Word::Ref => {
            proof! {
                reveal_strlit("ref");
                assert("ref"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "ref"
        }
        Word::Regions => {
            proof! {
                reveal_strlit("regions");
                assert("regions"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "regions"
        }
        Word::Worlds => {
            proof! {
                reveal_strlit("worlds");
                assert("worlds"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "worlds"
        }
        Word::Classes => {
            proof! {
                reveal_strlit("classes");
                assert("classes"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "classes"
        }
        Word::Auth => {
            proof! {
                reveal_strlit("auth");
                assert("auth"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "auth"
        }
        Word::Passkey => {
            proof! {
                reveal_strlit("passkey");
                assert("passkey"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "passkey"
        }
        Word::Register => {
            proof! {
                reveal_strlit("register");
                assert("register"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "register"
        }
        Word::Login => {
            proof! {
                reveal_strlit("login");
                assert("login"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "login"
        }
        Word::Start => {
            proof! {
                reveal_strlit("start");
                assert("start"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "start"
        }
        Word::Finish => {
            proof! {
                reveal_strlit("finish");
                assert("finish"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "finish"
        }
        Word::ItemEquipment => {
            proof! {
                reveal_strlit("item-equipment");
                assert("item-equipment"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "item-equipment"
        }
        Word::SymbolEquipment => {
            proof! {
                reveal_strlit("symbol-equipment");
                assert("symbol-equipment"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "symbol-equipment"
        }
        Word::HyperStat => {
            proof! {
                reveal_strlit("hyper-stat");
                assert("hyper-stat"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "hyper-stat"
        }
        Word::Ability => {
            proof! {
                reveal_strlit("ability");
                assert("ability"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "ability"
        }
        Word::LinkSkill => {
            proof! {
                reveal_strlit("link-skill");
                assert("link-skill"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "link-skill"
        }
        Word::Vmatrix => {
            proof! {
                reveal_strlit("vmatrix");
                assert("vmatrix"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "vmatrix"
        }
        Word::Hexamatrix => {
            proof! {
                reveal_strlit("hexamatrix");
                assert("hexamatrix"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "hexamatrix"
        }
        Word::Get => {
            proof! {
                reveal_strlit("GET");
                assert("GET"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "GET"
        }
        Word::Head => {
            proof! {
                reveal_strlit("HEAD");
                assert("HEAD"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "HEAD"
        }
        Word::Post => {
            proof! {
                reveal_strlit("POST");
                assert("POST"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "POST"
        }
        Word::Put => {
            proof! {
                reveal_strlit("PUT");
                assert("PUT"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "PUT"
        }
        Word::Patch => {
            proof! {
                reveal_strlit("PATCH");
                assert("PATCH"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "PATCH"
        }
        Word::Delete => {
            proof! {
                reveal_strlit("DELETE");
                assert("DELETE"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "DELETE"
        }
        Word::Other => {
            proof! {
                reveal_strlit("OTHER");
                assert("OTHER"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "OTHER"
        }
        Word::MeRead => {
            proof! {
                reveal_strlit("me.read");
                assert("me.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "me.read"
        }
        Word::TokenRead => {
            proof! {
                reveal_strlit("token.read");
                assert("token.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "token.read"
        }
        Word::TokenMint => {
            proof! {
                reveal_strlit("token.mint");
                assert("token.mint"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "token.mint"
        }
        Word::TokenRevoke => {
            proof! {
                reveal_strlit("token.revoke");
                assert("token.revoke"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "token.revoke"
        }
        Word::AuditRead => {
            proof! {
                reveal_strlit("audit.read");
                assert("audit.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "audit.read"
        }
        Word::AccountRead => {
            proof! {
                reveal_strlit("account.read");
                assert("account.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "account.read"
        }
        Word::AccountCreate => {
            proof! {
                reveal_strlit("account.create");
                assert("account.create"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "account.create"
        }
        Word::AccountUpdate => {
            proof! {
                reveal_strlit("account.update");
                assert("account.update"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "account.update"
        }
        Word::AccountDelete => {
            proof! {
                reveal_strlit("account.delete");
                assert("account.delete"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "account.delete"
        }
        Word::CharacterRead => {
            proof! {
                reveal_strlit("character.read");
                assert("character.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "character.read"
        }
        Word::CharacterCreate => {
            proof! {
                reveal_strlit("character.create");
                assert("character.create"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "character.create"
        }
        Word::CharacterUpdate => {
            proof! {
                reveal_strlit("character.update");
                assert("character.update"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "character.update"
        }
        Word::CharacterDelete => {
            proof! {
                reveal_strlit("character.delete");
                assert("character.delete"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "character.delete"
        }
        Word::StatRead => {
            proof! {
                reveal_strlit("stat.read");
                assert("stat.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "stat.read"
        }
        Word::StatReplace => {
            proof! {
                reveal_strlit("stat.replace");
                assert("stat.replace"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "stat.replace"
        }
        Word::StatUpdate => {
            proof! {
                reveal_strlit("stat.update");
                assert("stat.update"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "stat.update"
        }
        Word::EquipmentRead => {
            proof! {
                reveal_strlit("equipment.read");
                assert("equipment.read"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "equipment.read"
        }
        Word::EquipmentReplace => {
            proof! {
                reveal_strlit("equipment.replace");
                assert("equipment.replace"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "equipment.replace"
        }
        Word::UserCreate => {
            proof! {
                reveal_strlit("user.create");
                assert("user.create"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "user.create"
        }
        Word::SessionCreate => {
            proof! {
                reveal_strlit("session.create");
                assert("session.create"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "session.create"
        }
        Word::Json => {
            proof! {
                reveal_strlit("application/json");
                assert("application/json"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "application/json"
        }
        Word::MergePatch => {
            proof! {
                reveal_strlit("application/merge-patch+json");
                assert("application/merge-patch+json"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "application/merge-patch+json"
        }
        Word::BearerUpper => {
            proof! {
                reveal_strlit("Bearer ");
                assert("Bearer "@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "Bearer "
        }
        Word::BearerLower => {
            proof! {
                reveal_strlit("bearer ");
                assert("bearer "@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "bearer "
        }
        Word::Https => {
            proof! {
                reveal_strlit("https://");
                assert("https://"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "https://"
        }
        Word::True => {
            proof! {
                reveal_strlit("true");
                assert("true"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "true"
        }
        Word::False => {
            proof! {
                reveal_strlit("false");
                assert("false"@ =~= msapi_core::msg::chars(api::word(w)));
            }
            "false"
        }
    }
}

/// The method name.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == msapi_core::msg::chars(api::word(api::method_word(m)))))]
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
        let (path, query) = split_target(target);
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

/// `target` split at its first `?` into path and query, as
/// `split_once('?')` gives (the query is empty when there is no `?`).
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match first_question(target.spec_bytes()) {
            Some(i) => r.0.spec_bytes() == target.spec_bytes().subrange(0, i)
                && r.1.spec_bytes() == target.spec_bytes().subrange(i + 1, target.spec_bytes().len() as int),
            None => r.0 == target && r.1@.len() == 0,
        },
))]
#[must_use]
pub fn split_target(target: &str) -> (&str, &str) {
    let b = target.as_bytes();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= b@.len(),
            b@ == target.spec_bytes(),
            forall|j: int| 0 <= j < i ==> b@[j] != 63u8,
        decreases b@.len() - i
    ))]
    while i < b.len() {
        if b[i] == b'?' {
            proof! {
                let t = target.spec_bytes();
                encode_utf8_valid_utf8(target@);
                is_char_boundary_start_end_of_seq(t);
                is_char_boundary_iff_not_is_continuation_byte(t, i as int);
                lemma_boundary_after_ascii(t, i as int);
                lemma_first_question(t, i as int);
            }
            return (msg::cut(target, 0, i), msg::cut(target, i + 1, b.len()));
        }
        i += 1;
    }
    proof! {
        lemma_no_question(target.spec_bytes());
        reveal_strlit("");
    }
    (target, "")
}

/// The non-empty `/`-separated segments of `path`, as
/// `path.split('/').filter(|s| !s.is_empty())` gives.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r@.map_values(|x: &str| x.spec_bytes()) == segments_spec(path.spec_bytes(), seq![]),
))]
#[allow(clippy::needless_else, reason = "the `else` branches hold proof blocks, which compile away")]
#[must_use]
pub fn segments(path: &str) -> Vec<&str> {
    let b = path.as_bytes();
    let mut out: Vec<&str> = Vec::new();
    let mut start: usize = 0;
    let mut i: usize = 0;
    proof! {
        encode_utf8_valid_utf8(path@);
        is_char_boundary_start_end_of_seq(path.spec_bytes());
        assert(b@.skip(0) =~= b@);
        assert(b@.subrange(0, 0) =~= seq![]);
        assert(out@.map_values(|x: &str| x.spec_bytes()) + segments_spec(b@, seq![]) =~= segments_spec(b@, seq![]));
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            start <= i <= b@.len(),
            b@ == path.spec_bytes(),
            valid_utf8(b@),
            is_char_boundary(b@, start as int),
            forall|j: int| start <= j < i ==> b@[j] != 47u8,
            segments_spec(b@, seq![]) == out@.map_values(|x: &str| x.spec_bytes())
                + segments_spec(b@.skip(i as int), b@.subrange(start as int, i as int)),
        decreases b@.len() - i
    ))]
    while i < b.len() {
        proof! {
            assert(b@.skip(i as int).drop_first() =~= b@.skip(i + 1));
            assert(b@.skip(i as int)[0] == b@[i as int]);
            assert(b@.skip(i as int).len() > 0);
        }
        if b[i] == b'/' {
            proof! {
                is_char_boundary_iff_not_is_continuation_byte(b@, i as int);
                lemma_boundary_after_ascii(b@, i as int);
            }
            if start < i {
                let seg = msg::cut(path, start, i);
                proof_decl! {
                    let ghost before = out@;
                }
                out.push(seg);
                proof! {
                    let o = before.map_values(|x: &str| x.spec_bytes());
                    let rest = segments_spec(b@.skip(i + 1), seq![]);
                    assert(out@.map_values(|x: &str| x.spec_bytes()) =~= o.push(seg.spec_bytes()));
                    assert(o + (seq![seg.spec_bytes()] + rest) =~= o.push(seg.spec_bytes()) + rest);
                }
            } else {
                proof! {
                    assert(Seq::<Seq<u8>>::empty() + segments_spec(b@.skip(i + 1), seq![])
                        =~= segments_spec(b@.skip(i + 1), seq![]));
                }
            }
            start = i + 1;
            proof! {
                assert(b@.subrange(start as int, start as int) =~= seq![]);
            }
        } else {
            proof! {
                assert(b@.subrange(start as int, i as int).push(b@[i as int]) =~= b@.subrange(start as int, i + 1));
            }
        }
        i += 1;
    }
    proof! {
        assert(b@.skip(i as int) =~= seq![]);
    }
    if start < i {
        let seg = msg::cut(path, start, i);
        proof_decl! {
            let ghost before = out@;
        }
        out.push(seg);
        proof! {
            let o = before.map_values(|x: &str| x.spec_bytes());
            assert(out@.map_values(|x: &str| x.spec_bytes()) =~= o.push(seg.spec_bytes()));
            assert(o + seq![seg.spec_bytes()] =~= o.push(seg.spec_bytes()));
        }
    } else {
        proof! {
            let o = out@.map_values(|x: &str| x.spec_bytes());
            assert(o + Seq::<Seq<u8>>::empty() =~= o);
        }
    }
    proof! {
        assert(out@.map_values(|x: &str| x.spec_bytes()) =~= segments_spec(b@, seq![]));
    }
    out
}

/// The bytes of each of `segments`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@.len() == segments@.len(),
        forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i]@ == segments@[i].spec_bytes(),
))]
#[must_use]
pub fn words<'a>(segments: &[&'a str]) -> Vec<&'a [u8]> {
    let mut out: Vec<&'a [u8]> = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= segments@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j]@ == segments@[j].spec_bytes(),
        decreases segments@.len() - i
    ))]
    while i < segments.len() {
        out.push(segments[i].as_bytes());
        i += 1;
    }
    out
}

#[cfg(feature = "verus")]
verus! {

/// The bytes of each of `w`.
pub open spec fn views(w: Seq<&[u8]>) -> Seq<Seq<u8>> {
    w.map_values(|x: &[u8]| x@)
}

/// What is left of the segments of a path once `t` remains and the segment
/// being read so far is `cur`: each `/` ends a segment, and empty ones drop.
pub open spec fn segments_spec(t: Seq<u8>, cur: Seq<u8>) -> Seq<Seq<u8>>
    decreases t.len(),
{
    let done = if cur.len() == 0 { Seq::<Seq<u8>>::empty() } else { seq![cur] };
    if t.len() == 0 {
        done
    } else if t[0] == 47u8 {
        done + segments_spec(t.drop_first(), seq![])
    } else {
        segments_spec(t.drop_first(), cur.push(t[0]))
    }
}

/// The index of the first `?` in `t`, if any.
pub open spec fn first_question(t: Seq<u8>) -> Option<int> {
    if exists|i: int| 0 <= i < t.len() && t[i] == 63u8 {
        Some(choose|i: int| 0 <= i < t.len() && t[i] == 63u8 && forall|j: int| 0 <= j < i ==> t[j] != 63u8)
    } else {
        None
    }
}

proof fn lemma_first_question(t: Seq<u8>, i: int)
    requires 0 <= i < t.len(), t[i] == 63u8, forall|j: int| 0 <= j < i ==> t[j] != 63u8,
    ensures first_question(t) == Some(i),
{
    assert(exists|k: int| 0 <= k < t.len() && t[k] == 63u8 && forall|j: int| 0 <= j < k ==> t[j] != 63u8);
    let k = choose|k: int| 0 <= k < t.len() && t[k] == 63u8 && forall|j: int| 0 <= j < k ==> t[j] != 63u8;
    if k < i {
        assert(t[k] != 63u8);
    } else if k > i {
        assert(t[i] != 63u8);
    }
}

proof fn lemma_no_question(t: Seq<u8>)
    requires forall|j: int| 0 <= j < t.len() ==> t[j] != 63u8,
    ensures first_question(t) is None,
{
}

} // verus!

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
    #[test]
    fn segments_match_split_and_filter() {
        for path in ["", "/", "//", "/v1", "/v1/", "v1/characters", "/v1//characters///chr_1/stat", "/é/ü//ß", "a"] {
            let std: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
            assert_eq!(super::segments(path), std, "{path}");
            let bytes: Vec<&[u8]> = std.iter().map(|s| s.as_bytes()).collect();
            assert_eq!(super::words(&std), bytes);
        }
    }

    #[test]
    fn words_and_targets_match_std() {
        use msapi_core::api::{Word, word_bytes};
        for w in [
            Word::V1,
            Word::Me,
            Word::Tokens,
            Word::Audit,
            Word::Accounts,
            Word::Characters,
            Word::Stat,
            Word::History,
            Word::Health,
            Word::Docs,
            Word::Ref,
            Word::Regions,
            Word::Worlds,
            Word::Classes,
            Word::Auth,
            Word::Passkey,
            Word::Register,
            Word::Login,
            Word::Start,
            Word::Finish,
            Word::ItemEquipment,
            Word::SymbolEquipment,
            Word::HyperStat,
            Word::Ability,
            Word::LinkSkill,
            Word::Vmatrix,
            Word::Hexamatrix,
            Word::Get,
            Word::Head,
            Word::Post,
            Word::Put,
            Word::Patch,
            Word::Delete,
            Word::Other,
            Word::MeRead,
            Word::TokenRead,
            Word::TokenMint,
            Word::TokenRevoke,
            Word::AuditRead,
            Word::AccountRead,
            Word::AccountCreate,
            Word::AccountUpdate,
            Word::AccountDelete,
            Word::CharacterRead,
            Word::CharacterCreate,
            Word::CharacterUpdate,
            Word::CharacterDelete,
            Word::StatRead,
            Word::StatReplace,
            Word::StatUpdate,
            Word::EquipmentRead,
            Word::EquipmentReplace,
            Word::UserCreate,
            Word::SessionCreate,
            Word::Json,
            Word::MergePatch,
            Word::BearerUpper,
            Word::BearerLower,
            Word::Https,
            Word::True,
            Word::False,
        ] {
            assert_eq!(super::word(w).as_bytes(), word_bytes(w));
        }
        for t in ["/v1/a?b=c?d", "/v1/é", "/x?", "?q", ""] {
            assert_eq!(super::split_target(t), t.split_once('?').unwrap_or((t, "")));
        }
    }

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
