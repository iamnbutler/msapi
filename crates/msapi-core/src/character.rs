//! Validated scalar fields of a character's Character Info window.

#![allow(
    clippy::cast_lossless,
    clippy::single_char_add_str,
    clippy::manual_unwrap_or_default,
    clippy::manual_map,
    clippy::single_match,
    clippy::collapsible_if,
    clippy::manual_unwrap_or,
    clippy::single_match_else,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening, `Option` combinators or `if let` chains"
)]

use std::fmt;

use serde::de;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::utf8::encode_utf8;

#[cfg(feature = "verus")]
use crate::msg::{int_chars, uint_chars};
use crate::msg::{push_int, push_uint};
use crate::region::Region;
#[cfg(feature = "verus")]
use crate::rules::NAME_MAX_CHARS;
use crate::rules::{self, NameCheck};
use crate::text::{char_count, has_control, trim};
#[cfg(feature = "verus")]
use crate::text::{chars, control_at, trimmed};

/// An in-game character name.
///
/// Construction only rejects what is never a name (empty, too long, control
/// characters, surrounding whitespace). The per-region spelling rules live in
/// [`CharacterName::check_region`], because KMS names are Hangul and GMS names
/// are ASCII.
///
/// ```
/// use msapi_core::{CharacterName, Region};
///
/// let name = CharacterName::new("Lutoren")?;
/// assert!(name.check_region(Region::Gms).is_ok());
/// assert!(CharacterName::new("Bad Name")?.check_region(Region::Gms).is_err());
/// assert!(CharacterName::new(" padded").is_err());
/// # Ok::<(), String>(())
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CharacterName(String);

#[cfg(feature = "verus")]
verus! {

// The conversions are checked, but claim no spec beyond what
// `CharacterName::from_string` and `into_string` ensure.
impl vstd::std_specs::convert::TryFromSpecImpl<String> for CharacterName {
    open spec fn obeys_try_from_spec() -> bool {
        false
    }

    uninterp spec fn try_from_spec(v: String) -> Result<Self, String>;
}

impl vstd::std_specs::convert::FromSpecImpl<CharacterName> for String {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    uninterp spec fn from_spec(v: CharacterName) -> Self;
}

impl CharacterName {
    /// The name's characters, for specs.
    pub closed spec fn text(&self) -> Seq<char> {
        self.0@
    }

    /// The name's UTF-8 bytes, for specs.
    pub closed spec fn bytes(&self) -> Seq<u8> {
        encode_utf8(self.0@)
    }
}

/// `name` has no surrounding whitespace and no control character.
pub open spec fn tidy(name: Seq<u8>) -> bool {
    trimmed(name) == name && !exists|i: int| 0 <= i < name.len() && #[trigger] control_at(name, i)
}

/// `name` is a GMS name, as `rules::gms_name_ok` decides.
pub open spec fn gms_name(name: Seq<u8>) -> bool {
    name.len() <= rules::GMS_NAME_MAX && forall|i: int| 0 <= i < name.len() ==> crate::ascii::is_alnum(#[trigger] name[i])
}

/// The verdict `CharacterName::new` gives `name`, as `rules::name_check` does.
pub open spec fn name_verdict(name: Seq<u8>) -> NameCheck {
    if chars(name) == 0 { NameCheck::Empty }
    else if chars(name) > NAME_MAX_CHARS { NameCheck::TooLong }
    else if !tidy(name) { NameCheck::Untidy }
    else { NameCheck::Ok }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl CharacterName {
    /// Longest name any region allows, in characters.
    pub const MAX_CHARS: usize = rules::NAME_MAX_CHARS;

    /// Validates a name: the verdict is [`rules::name_check`]'s.
    ///
    /// # Errors
    ///
    /// The name is empty, too long, or has surrounding whitespace or control
    /// characters; the message says which.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(n) => name_verdict(n.bytes()) == NameCheck::Ok,
                Err(m) => match name_verdict(encode_utf8(name@)) {
                    NameCheck::Empty => m@ == "character name is empty"@,
                    NameCheck::TooLong => m@ == "character name `"@ + name@ + "` is longer than "@
                        + uint_chars(NAME_MAX_CHARS as nat) + " characters"@,
                    NameCheck::Untidy => m@ == "character name `"@ + name@
                        + "` has surrounding whitespace or control characters"@,
                    NameCheck::Ok => false,
                },
            },
    ))]
    pub fn from_string(name: String) -> Result<Self, String> {
        #[allow(clippy::redundant_as_str, reason = "Verus has a spec for `str::as_bytes`, not `String::as_bytes`")]
        let bytes = name.as_str().as_bytes();
        let (lo, hi) = trim(bytes);
        let tidy = lo == 0 && hi == bytes.len() && !has_control(bytes);
        proof! {
            if lo == 0 && hi == bytes.len() {
                assert(bytes@.subrange(0, bytes@.len() as int) =~= bytes@);
            }
            if trimmed(bytes@) == bytes@ {
                // The kept range has the whole length, so it is the whole of `s`.
                assert(bytes@.subrange(lo as int, hi as int).len() == bytes@.len());
            }
        }
        match rules::name_check(char_count(bytes), tidy) {
            NameCheck::Ok => Ok(Self(name)),
            NameCheck::Empty => {
                let mut m = String::new();
                m.push_str("character name is empty");
                Err(m)
            }
            NameCheck::TooLong => {
                let mut m = String::new();
                m.push_str("character name `");
                m.push_str(name.as_str());
                m.push_str("` is longer than ");
                push_uint(&mut m, Self::MAX_CHARS as u128);
                m.push_str(" characters");
                Err(m)
            }
            NameCheck::Untidy => {
                let mut m = String::new();
                m.push_str("character name `");
                m.push_str(name.as_str());
                m.push_str("` has surrounding whitespace or control characters");
                Err(m)
            }
        }
    }

    /// Applies the region's naming rules.
    ///
    /// GMS names are ASCII letters and digits, at most 12 of them. No minimum
    /// is enforced, since older characters predate the current one.
    ///
    /// # Errors
    ///
    /// The name breaks the region's rules; the message says how.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(()) => region == Region::Gms ==> gms_name(self.bytes()),
                Err(m) => region == Region::Gms && !gms_name(self.bytes())
                    && m@ == "`"@ + self.text() + "` is not a GMS name: GMS names are 1-12 ASCII letters and digits"@,
            },
    ))]
    pub fn check_region(&self, region: Region) -> Result<(), String> {
        #[allow(clippy::redundant_as_str, reason = "Verus has a spec for `str::as_bytes`, not `String::as_bytes`")]
        if matches!(region, Region::Gms) && !rules::gms_name_ok(self.0.as_str().as_bytes()) {
            let mut m = String::new();
            m.push_str("`");
            m.push_str(self.0.as_str());
            m.push_str("` is not a GMS name: GMS names are 1-12 ASCII letters and digits");
            return Err(m);
        }
        Ok(())
    }

    /// The name as a string slice.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == self.text()))]
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// The name as a `String`.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == self.text()))]
    #[must_use]
    pub fn into_string(self) -> String {
        self.0
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl CharacterName {
    /// Validates a name: [`CharacterName::from_string`] on `name.into()`.
    ///
    /// # Errors
    ///
    /// As [`CharacterName::from_string`].
    pub fn new(name: impl Into<String>) -> Result<Self, String> {
        Self::from_string(name.into())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl TryFrom<String> for CharacterName {
    type Error = String;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::from_string(s)
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl From<CharacterName> for String {
    fn from(n: CharacterName) -> Self {
        n.into_string()
    }
}

impl fmt::Display for CharacterName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// As serde's derive with `into = "String"`: the name as a JSON string.
impl Serialize for CharacterName {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

/// As serde's derive with `try_from = "String"`: a string, validated, with
/// the validation message as the error.
impl<'de> Deserialize<'de> for CharacterName {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::from_string(String::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

macro_rules! bounded_int {
    ($(#[$doc:meta])* $name:ident, $ty:ty, $bounded:ident, $min:expr, $max:expr, $what:literal) => {
        $(#[$doc])*
        #[cfg_attr(feature = "verus", verus_verify)]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name($ty);

        #[cfg(feature = "verus")]
        verus! {

        impl $name {
            /// The value, for specs.
            pub closed spec fn value(self) -> int {
                self.0 as int
            }
        }

        // Validation is checked, but claims no spec beyond what `new` ensures.
        impl vstd::std_specs::convert::TryFromSpecImpl<i64> for $name {
            open spec fn obeys_try_from_spec() -> bool {
                false
            }

            uninterp spec fn try_from_spec(v: i64) -> Result<Self, String>;
        }

        impl vstd::std_specs::convert::FromSpecImpl<$name> for i64 {
            open spec fn obeys_from_spec() -> bool {
                true
            }

            open spec fn from_spec(v: $name) -> Self {
                v.value() as i64
            }
        }

        } // verus!

        #[cfg_attr(feature = "verus", verus_verify)]
        impl $name {
            /// Smallest allowed value.
            pub const MIN: $ty = $min;
            /// Largest allowed value.
            pub const MAX: $ty = $max;

            /// Validates a value.
            ///
            /// # Errors
            ///
            /// `v` is out of range; the message gives the range.
            #[cfg_attr(feature = "verus", verus_spec(r =>
                ensures
                    match r {
                        Ok(x) => x.value() == v && $min <= v <= $max,
                        Err(m) => !($min <= v <= $max) && m@ == $what@ + " must be between "@
                            + uint_chars($min as nat) + " and "@ + uint_chars($max as nat)
                            + ", got "@ + int_chars(v as int),
                    },
            ))]
            pub fn new(v: i64) -> Result<Self, String> {
                match rules::$bounded(v, Self::MIN as i64, Self::MAX as i64) {
                    Some(x) => Ok(Self(x)),
                    None => {
                        let mut m = String::new();
                        m.push_str($what);
                        m.push_str(" must be between ");
                        push_uint(&mut m, Self::MIN as u128);
                        m.push_str(" and ");
                        push_uint(&mut m, Self::MAX as u128);
                        m.push_str(", got ");
                        push_int(&mut m, v);
                        Err(m)
                    }
                }
            }

            /// The value.
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.value()))]
            #[must_use]
            pub const fn get(self) -> $ty {
                self.0
            }

            /// The value, widened.
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.value()))]
            #[must_use]
            pub const fn wide(self) -> i64 {
                self.0 as i64
            }
        }

        #[cfg_attr(feature = "verus", verus_verify)]
        impl TryFrom<i64> for $name {
            type Error = String;
            fn try_from(v: i64) -> Result<Self, Self::Error> {
                Self::new(v)
            }
        }

        #[cfg_attr(feature = "verus", verus_verify)]
        impl From<$name> for i64 {
            fn from(v: $name) -> Self {
                v.wide()
            }
        }

        /// As serde's derive with `into = "i64"`.
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.serialize_i64(self.wide())
            }
        }

        /// As serde's derive with `try_from = "i64"`: an integer, validated,
        /// with the validation message as the error.
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                Self::new(i64::deserialize(deserializer)?).map_err(de::Error::custom)
            }
        }
    };
}

bounded_int!(
    /// Character level, 1 to 300.
    ///
    /// ```
    /// use msapi_core::Level;
    /// assert_eq!(Level::new(287).unwrap().get(), 287);
    /// assert!(Level::new(0).is_err());
    /// assert!(Level::new(301).is_err());
    /// ```
    Level, u16, bounded_u16, 1, 300, "level"
);

bounded_int!(
    /// Job advancement: 0 for a beginner, then 1st through 6th job.
    ///
    /// Nexon's API calls this `character_class_level`.
    ClassLevel, u8, bounded_u8, 0, 6, "class level (job advancement)"
);

/// Character gender as the game records it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Gender {
    /// Male.
    Male,
    /// Female.
    Female,
}

/// How far the character has taken the weapon liberation questlines.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Liberation {
    /// Not liberated.
    None,
    /// Genesis weapon liberated.
    Genesis,
    /// Destiny weapon liberated.
    Destiny,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The validation as it was written with `format!` and serde's derive.
    fn reference_new(name: &str) -> Result<(), String> {
        let tidy = name.trim() == name && !name.chars().any(char::is_control);
        match rules::name_check(name.chars().count(), tidy) {
            NameCheck::Ok => Ok(()),
            NameCheck::Empty => Err("character name is empty".into()),
            NameCheck::TooLong => {
                Err(format!("character name `{name}` is longer than {} characters", CharacterName::MAX_CHARS))
            }
            NameCheck::Untidy => {
                Err(format!("character name `{name}` has surrounding whitespace or control characters"))
            }
        }
    }

    #[test]
    fn messages_match_format() {
        for name in [
            "",
            "Lutoren",
            " padded",
            "padded ",
            "tab\there",
            "\u{85}x",
            "x\u{a0}",
            "a\u{9f}b",
            "\u{3000}",
            "Fourteenchars!",
            "한글이름",
            "Bad Name",
            "abcdefghijklm",
            "abcdefghijklmn",
        ] {
            assert_eq!(CharacterName::new(name).map(|_| ()), reference_new(name), "{name:?}");
            if let Ok(n) = CharacterName::new(name) {
                let gms = rules::gms_name_ok(name.as_bytes());
                let want = if gms {
                    Ok(())
                } else {
                    Err(format!("`{name}` is not a GMS name: GMS names are 1-12 ASCII letters and digits"))
                };
                assert_eq!(n.check_region(Region::Gms), want);
                assert_eq!(n.check_region(Region::Kms), Ok(()));
            }
        }
        for v in [i64::MIN, -1, 0, 1, 6, 7, 300, 301, i64::MAX] {
            assert_eq!(
                Level::new(v).map(Level::get),
                if (1..=300).contains(&v) {
                    Ok(u16::try_from(v).unwrap())
                } else {
                    Err(format!("level must be between 1 and 300, got {v}"))
                }
            );
            assert_eq!(
                ClassLevel::new(v).map(ClassLevel::get),
                if (0..=6).contains(&v) {
                    Ok(u8::try_from(v).unwrap())
                } else {
                    Err(format!("class level (job advancement) must be between 0 and 6, got {v}"))
                }
            );
        }
    }

    #[test]
    fn serde_matches_the_derive() {
        #[derive(Serialize, Deserialize, Debug, Clone)]
        #[serde(try_from = "String", into = "String")]
        struct DName(String);
        impl TryFrom<String> for DName {
            type Error = String;
            fn try_from(s: String) -> Result<Self, String> {
                reference_new(&s).map(|()| Self(s))
            }
        }
        impl From<DName> for String {
            fn from(n: DName) -> Self {
                n.0
            }
        }
        #[derive(Serialize, Deserialize, Debug, Clone)]
        #[serde(try_from = "i64", into = "i64")]
        struct DLevel(u16);
        impl TryFrom<i64> for DLevel {
            type Error = String;
            fn try_from(v: i64) -> Result<Self, String> {
                Level::new(v).map(|l| Self(l.get()))
            }
        }
        impl From<DLevel> for i64 {
            fn from(v: DLevel) -> Self {
                Self::from(v.0)
            }
        }
        for j in ["\"Lutoren\"", "\" x\"", "\"\"", "5", "null", "[]", "\"abcdefghijklmn\""] {
            let ours = serde_json::from_str::<CharacterName>(j)
                .map(|n| serde_json::to_string(&n).unwrap())
                .map_err(|e| e.to_string());
            let theirs =
                serde_json::from_str::<DName>(j).map(|n| serde_json::to_string(&n).unwrap()).map_err(|e| e.to_string());
            assert_eq!(ours, theirs, "{j}");
        }
        for j in ["1", "300", "0", "301", "-5", "1.5", "\"7\"", "null", "99999999999999999999"] {
            let ours =
                serde_json::from_str::<Level>(j).map(|n| serde_json::to_string(&n).unwrap()).map_err(|e| e.to_string());
            let theirs = serde_json::from_str::<DLevel>(j)
                .map(|n| serde_json::to_string(&n).unwrap())
                .map_err(|e| e.to_string());
            assert_eq!(ours, theirs, "{j}");
        }
    }
}
