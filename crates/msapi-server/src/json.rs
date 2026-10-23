//! JSON Merge Patch (RFC 7396).
//!
//! The merge is `msapi_core::json::merge`, proven by Verus; this file only
//! converts `serde_json` values to its model and back.

use msapi_core::json::{self, Json};
use serde_json::{Map, Number, Value};

/// Applies `patch` to `target` in place.
///
/// Objects merge key by key, `null` removes a key, and anything else replaces
/// the target wholesale.
///
/// ```
/// use serde_json::json;
/// let mut doc = json!({"a": 1, "b": {"c": 2, "d": 3}});
/// msapi_server::json::merge_patch(&mut doc, &json!({"a": null, "b": {"c": 9}}));
/// assert_eq!(doc, json!({"b": {"c": 9, "d": 3}}));
/// ```
pub fn merge_patch(target: &mut Value, patch: &Value) {
    // `serde_json` objects never repeat a key, so the merge always succeeds.
    if let Some(merged) = json::merge(to_model(target.take()), to_model(patch.clone())) {
        *target = from_model(merged);
    }
}

fn to_model(value: Value) -> Json {
    match value {
        Value::Null => Json::Null,
        Value::Bool(b) => Json::Bool(b),
        Value::Number(n) => Json::Number(n.to_string().into_bytes()),
        Value::String(s) => Json::Str(s.into_bytes()),
        Value::Array(items) => Json::Array(items.into_iter().map(to_model).collect()),
        Value::Object(members) => {
            let (keys, values) = members.into_iter().map(|(k, v)| (k.into_bytes(), to_model(v))).unzip();
            Json::Object(keys, values)
        }
    }
}

fn from_model(value: Json) -> Value {
    let text = |bytes: Vec<u8>| {
        String::from_utf8(bytes).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
    };
    match value {
        Json::Null => Value::Null,
        Json::Bool(b) => Value::Bool(b),
        Json::Number(n) => serde_json::from_slice::<Number>(&n).map_or(Value::Null, Value::Number),
        Json::Str(s) => Value::String(text(s)),
        Json::Array(items) => Value::Array(items.into_iter().map(from_model).collect()),
        Json::Object(keys, values) => {
            Value::Object(keys.into_iter().map(text).zip(values.into_iter().map(from_model)).collect::<Map<_, _>>())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    /// The examples from RFC 7396 §3.
    #[test]
    fn rfc_7396_examples() {
        let cases = [
            (json!({"a":"b"}), json!({"a":"c"}), json!({"a":"c"})),
            (json!({"a":"b"}), json!({"b":"c"}), json!({"a":"b","b":"c"})),
            (json!({"a":"b"}), json!({"a":null}), json!({})),
            (json!({"a":"b","b":"c"}), json!({"a":null}), json!({"b":"c"})),
            (json!({"a":["b"]}), json!({"a":"c"}), json!({"a":"c"})),
            (json!({"a":"c"}), json!({"a":["b"]}), json!({"a":["b"]})),
            (json!({"a":{"b":"c"}}), json!({"a":{"b":"d","c":null}}), json!({"a":{"b":"d"}})),
            (json!({"a":[{"b":"c"}]}), json!({"a":[1]}), json!({"a":[1]})),
            (json!(["a", "b"]), json!(["c", "d"]), json!(["c", "d"])),
            (json!({"a":"b"}), json!(["c"]), json!(["c"])),
            (json!({"a":"foo"}), json!(null), json!(null)),
            (json!({"a":"foo"}), json!("bar"), json!("bar")),
            (json!({"e":null}), json!({"a":1}), json!({"e":null,"a":1})),
            (json!([1, 2]), json!({"a":"b","c":null}), json!({"a":"b"})),
            (json!({}), json!({"a":{"bb":{"ccc":null}}}), json!({"a":{"bb":{}}})),
        ];
        let numbers = (
            json!({"a": 1, "b": -2.5, "c": 1e300}),
            json!({"d": u64::MAX}),
            json!({"a": 1, "b": -2.5, "c": 1e300, "d": u64::MAX}),
        );
        for (mut target, patch, expected) in cases.into_iter().chain([numbers]) {
            merge_patch(&mut target, &patch);
            assert_eq!(target, expected, "patch {patch}");
        }
    }
}
