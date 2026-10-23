//! Validated scalar fields of a character's Character Info window.

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::region::Region;

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
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub struct CharacterName(String);

impl CharacterName {
    /// Longest name any region allows, in characters.
    pub const MAX_CHARS: usize = 13;

    /// Validates a name.
    pub fn new(name: impl Into<String>) -> Result<Self, String> {
        let name = name.into();
        let chars = name.chars().count();
        if chars == 0 {
            return Err("character name is empty".into());
        }
        if chars > Self::MAX_CHARS {
            return Err(format!("character name `{name}` is longer than {} characters", Self::MAX_CHARS));
        }
        if name.trim() != name || name.chars().any(char::is_control) {
            return Err(format!("character name `{name}` has surrounding whitespace or control characters"));
        }
        Ok(Self(name))
    }

    /// Applies the region's naming rules.
    ///
    /// GMS names are ASCII letters and digits, at most 12 of them. No minimum
    /// is enforced, since older characters predate the current one.
    pub fn check_region(&self, region: Region) -> Result<(), String> {
        match region {
            Region::Gms if self.0.len() > 12 || !self.0.bytes().all(|b| b.is_ascii_alphanumeric()) => {
                Err(format!("`{}` is not a GMS name: GMS names are 1-12 ASCII letters and digits", self.0))
            }
            _ => Ok(()),
        }
    }

    /// The name as a string slice.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl TryFrom<String> for CharacterName {
    type Error = String;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl From<CharacterName> for String {
    fn from(n: CharacterName) -> Self {
        n.0
    }
}

impl fmt::Display for CharacterName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

macro_rules! bounded_int {
    ($(#[$doc:meta])* $name:ident, $ty:ty, $min:expr, $max:expr, $what:literal) => {
        $(#[$doc])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
        #[serde(try_from = "i64", into = "i64")]
        pub struct $name($ty);

        impl $name {
            /// Smallest allowed value.
            pub const MIN: $ty = $min;
            /// Largest allowed value.
            pub const MAX: $ty = $max;

            /// Validates a value.
            pub fn new(v: i64) -> Result<Self, String> {
                <$ty>::try_from(v)
                    .ok()
                    .filter(|v| (Self::MIN..=Self::MAX).contains(v))
                    .map(Self)
                    .ok_or_else(|| format!(concat!($what, " must be between {} and {}, got {}"), Self::MIN, Self::MAX, v))
            }

            /// The value.
            #[must_use]
            pub const fn get(self) -> $ty {
                self.0
            }
        }

        impl TryFrom<i64> for $name {
            type Error = String;
            fn try_from(v: i64) -> Result<Self, Self::Error> {
                Self::new(v)
            }
        }

        impl From<$name> for i64 {
            fn from(v: $name) -> Self {
                i64::from(v.0)
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
    Level, u16, 1, 300, "level"
);

bounded_int!(
    /// Job advancement: 0 for a beginner, then 1st through 6th job.
    ///
    /// Nexon's API calls this `character_class_level`.
    ClassLevel, u8, 0, 6, "class level (job advancement)"
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
