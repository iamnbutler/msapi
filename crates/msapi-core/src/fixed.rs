//! Exact decimals with a fixed number of fractional digits.

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
use std::str::FromStr;

use serde::de::{self, Visitor};

use crate::decimal::{DecimalError, format_decimal, parse_decimal};
#[cfg(feature = "verus")]
use crate::decimal::{decimal_text, decimal_value, frac_len, splits_at};
#[cfg(feature = "verus")]
use crate::msg::{chars, uint_chars};
use crate::msg::{push_uint, text};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;

/// A decimal with exactly `DP` fractional digits, stored as an integer count
/// of `10^-DP` units.
///
/// The game shows percentages like `93.14%` and EXP like `12.345%`. Storing
/// them as `f64` would turn sums and comparisons into rounding questions, so
/// they are kept as integers and only become floats at the JSON boundary.
///
/// A value with more fractional digits than `DP` is rejected rather than
/// rounded, because a silent rounding is exactly the kind of guess this API
/// refuses to make.
///
/// ```
/// use msapi_core::Pct;
///
/// let ied: Pct = "93.14".parse()?;
/// assert_eq!(ied.raw(), 9314);
/// assert_eq!(ied.to_string(), "93.14");
/// assert!("93.145".parse::<Pct>().is_err());
/// # Ok::<(), msapi_core::FixedError>(())
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Fixed<const DP: u32>(i64);

#[cfg(feature = "verus")]
verus! {

impl<const DP: u32> Fixed<DP> {
    /// The raw integer, for specs: `93.14%` is `9314`.
    pub closed spec fn value(self) -> int {
        self.0 as int
    }

    /// The value with raw integer `raw`, for specs.
    pub closed spec fn of_raw(raw: i64) -> Self {
        Self(raw)
    }

    /// `of_raw` keeps the raw integer.
    pub proof fn lemma_of_raw(raw: i64)
        ensures Self::of_raw(raw).value() == raw as int,
    {
    }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl<const DP: u32> Fixed<DP> {
    /// Builds a value from its raw integer representation (`9314` is `93.14` for [`Pct`]).
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == raw as int, r == Self::of_raw(raw)))]
    pub const fn from_raw(raw: i64) -> Self {
        Self(raw)
    }

    /// The raw integer representation.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.value()))]
    pub const fn raw(self) -> i64 {
        self.0
    }
}

/// A displayed percentage with two decimal places (`380.00`, `93.14`).
pub type Pct = Fixed<2>;

/// The EXP bar percentage, which the game shows with three decimal places.
pub type ExpRate = Fixed<3>;

/// Why a value could not become a [`Fixed`].
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixedError {
    /// The input was not a decimal number.
    Invalid(String),
    /// The input had more fractional digits than the type keeps.
    TooPrecise {
        /// The fractional digits the type keeps.
        max_decimals: u32,
    },
    /// The input does not fit.
    OutOfRange,
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FixedError {
    /// The message [`Display`](fmt::Display) writes.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r@ == match self {
                Self::Invalid(s) => "`"@ + s@ + "` is not a decimal number"@,
                Self::TooPrecise { max_decimals } => "more than "@ + uint_chars(*max_decimals as nat)
                    + " decimal places; send the value exactly as displayed"@,
                Self::OutOfRange => "number out of range"@,
            },
    ))]
    #[must_use]
    pub fn message(&self) -> String {
        let mut m = String::new();
        match self {
            Self::Invalid(s) => {
                m.push_str("`");
                m.push_str(s.as_str());
                m.push_str("` is not a decimal number");
            }
            Self::TooPrecise { max_decimals } => {
                m.push_str("more than ");
                push_uint(&mut m, *max_decimals as u128);
                m.push_str(" decimal places; send the value exactly as displayed");
            }
            Self::OutOfRange => m.push_str("number out of range"),
        }
        m
    }
}

impl fmt::Display for FixedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message())
    }
}

impl std::error::Error for FixedError {}

impl<const DP: u32> Fixed<DP> {
    /// Number of raw units in `1`.
    pub const SCALE: i64 = 10_i64.pow(DP);

    /// Zero.
    pub const ZERO: Self = Self(0);
}

#[cfg(feature = "verus")]
verus! {

/// `t` limited to the range of `i64`, as saturating arithmetic leaves it.
pub open spec fn saturate(t: int) -> int {
    if t > i64::MAX { i64::MAX as int } else if t < i64::MIN { i64::MIN as int } else { t }
}

// `+` and `-` saturate, which is what vstd's operator specs say.
impl<const DP: u32> vstd::std_specs::ops::AddSpecImpl for Fixed<DP> {
    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_req(self, rhs: Self) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: Self) -> Self {
        Self::of_raw(saturate(self.value() + rhs.value()) as i64)
    }
}

impl<const DP: u32> vstd::std_specs::ops::SubSpecImpl for Fixed<DP> {
    open spec fn obeys_sub_spec() -> bool {
        true
    }

    open spec fn sub_req(self, rhs: Self) -> bool {
        true
    }

    open spec fn sub_spec(self, rhs: Self) -> Self {
        Self::of_raw(saturate(self.value() - rhs.value()) as i64)
    }
}

} // verus!

/// `a + b` saturating at the ends of `i64`, written out so Verus can check it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == saturate(a as int + b as int)))]
const fn saturating_add(a: i64, b: i64) -> i64 {
    let sum = a as i128 + b as i128;
    if sum > i64::MAX as i128 {
        i64::MAX
    } else if sum < i64::MIN as i128 {
        i64::MIN
    } else {
        #[allow(clippy::cast_possible_truncation, reason = "in range: the branches above cut off the rest")]
        let r = sum as i64;
        r
    }
}

/// `a - b` saturating at the ends of `i64`, written out so Verus can check it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == saturate(a as int - b as int)))]
const fn saturating_sub(a: i64, b: i64) -> i64 {
    let diff = a as i128 - b as i128;
    if diff > i64::MAX as i128 {
        i64::MAX
    } else if diff < i64::MIN as i128 {
        i64::MIN
    } else {
        #[allow(clippy::cast_possible_truncation, reason = "in range: the branches above cut off the rest")]
        let r = diff as i64;
        r
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl<const DP: u32> std::ops::Add for Fixed<DP> {
    type Output = Self;
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == saturate(self.value() + rhs.value())))]
    fn add(self, rhs: Self) -> Self {
        let r = Self(saturating_add(self.0, rhs.0));
        proof! { assert(r == Self::of_raw(r.0)); }
        r
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl<const DP: u32> std::ops::Sub for Fixed<DP> {
    type Output = Self;
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == saturate(self.value() - rhs.value())))]
    fn sub(self, rhs: Self) -> Self {
        let r = Self(saturating_sub(self.0, rhs.0));
        proof! { assert(r == Self::of_raw(r.0)); }
        r
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl<const DP: u32> Fixed<DP> {
    /// Parses `s` with the proven [`parse_decimal`], naming the error.
    ///
    /// # Errors
    ///
    /// As [`parse_decimal`] reports it.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(v) => exists|k: int| #[trigger] splits_at(s.spec_bytes(), k) && frac_len(s.spec_bytes(), k) <= DP
                    && v.value() == decimal_value(s.spec_bytes(), k, DP as nat),
                Err(FixedError::Invalid(t)) => t@ == s@ && forall|k: int| !(#[trigger] splits_at(s.spec_bytes(), k)),
                Err(FixedError::TooPrecise { max_decimals }) => max_decimals == DP
                    && exists|k: int| #[trigger] splits_at(s.spec_bytes(), k) && frac_len(s.spec_bytes(), k) > DP,
                Err(FixedError::OutOfRange) => exists|k: int| #[trigger] splits_at(s.spec_bytes(), k)
                    && frac_len(s.spec_bytes(), k) <= DP
                    && !(i64::MIN <= decimal_value(s.spec_bytes(), k, DP as nat)
                        && decimal_value(s.spec_bytes(), k, DP as nat) <= i64::MAX),
            },
    ))]
    pub fn parse(s: &str) -> Result<Self, FixedError> {
        match parse_decimal(s.as_bytes(), DP) {
            Ok(v) => Ok(Self(v)),
            Err(DecimalError::Invalid) => Err(FixedError::Invalid(s.to_owned())),
            Err(DecimalError::TooPrecise) => Err(FixedError::TooPrecise { max_decimals: DP }),
            Err(DecimalError::OutOfRange) => Err(FixedError::OutOfRange),
        }
    }

    /// The exact digits the proven [`format_decimal`] writes, as text.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires DP <= 18,
        ensures r@ == chars(decimal_text(self.value(), DP as nat)),
    ))]
    #[must_use]
    pub fn text(self) -> String {
        let d = format_decimal(self.0, DP);
        text(d.as_slice())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl<const DP: u32> FromStr for Fixed<DP> {
    type Err = FixedError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl<const DP: u32> fmt::Display for Fixed<DP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `SCALE` is `10^DP` in an `i64`, which only compiles for `DP <= 18`,
        // the precondition of `text`.
        let _ = Self::SCALE;
        f.write_str(&self.text())
    }
}

impl<const DP: u32> fmt::Debug for Fixed<DP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The struct name and field `serde_json` (with `arbitrary_precision`) uses
/// for a number kept as its exact text.
const NUMBER_TOKEN: &str = "$serde_json::private::Number";

impl<const DP: u32> Fixed<DP> {
    /// Parses a JSON number's text with the proven [`parse_decimal`].
    fn from_number_text<E: de::Error>(text: &str) -> Result<Self, E> {
        text.parse().map_err(E::custom)
    }
}

/// JSON carries the exact digits from the proven `format_decimal`, as a
/// number: `93.14`, `100.00`.
impl<const DP: u32> Serialize for Fixed<DP> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let _ = Self::SCALE; // `DP <= 18`, as `format_decimal` requires.
        let text: String = format_decimal(self.0, DP).into_iter().map(char::from).collect();
        let mut s = serializer.serialize_struct(NUMBER_TOKEN, 1)?;
        s.serialize_field(NUMBER_TOKEN, &text)?;
        s.end()
    }
}

/// Every JSON number is read from its text by the proven `parse_decimal`; no
/// float arithmetic is involved.
impl<'de, const DP: u32> Deserialize<'de> for Fixed<DP> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FixedVisitor<const DP: u32>;

        impl<'de, const DP: u32> Visitor<'de> for FixedVisitor<DP> {
            type Value = Fixed<DP>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "a number with at most {DP} decimal places")
            }

            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Self::Value, E> {
                Fixed::from_number_text(&v.to_string())
            }

            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Self::Value, E> {
                Fixed::from_number_text(&v.to_string())
            }

            // `serde_json` parsing text hands over any non-integer number as
            // its exact text, as a one-entry map.
            fn visit_map<A: de::MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                match map.next_key::<String>()? {
                    Some(key) if key == NUMBER_TOKEN => {
                        let text: String = map.next_value()?;
                        Fixed::from_number_text(&text)
                    }
                    _ => Err(de::Error::invalid_type(de::Unexpected::Map, &self)),
                }
            }
        }

        deserializer.deserialize_any(FixedVisitor::<DP>)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_prints_exactly() {
        for (input, raw, shown) in [
            ("0", 0, "0.00"),
            ("380", 38_000, "380.00"),
            ("93.14", 9314, "93.14"),
            ("93.1", 9310, "93.10"),
            ("-5.5", -550, "-5.50"),
        ] {
            let p: Pct = input.parse().unwrap();
            assert_eq!(p.raw(), raw, "{input}");
            assert_eq!(p.to_string(), shown, "{input}");
        }
    }

    #[test]
    fn rejects_malformed_strings() {
        for bad in ["", ".5", "5.", "1e3", "abc", "1.2.3", "--1", "+1", "93.14%"] {
            assert!(bad.parse::<Pct>().is_err(), "{bad:?} should be rejected");
        }
    }

    #[test]
    fn json_round_trip_does_not_drift() {
        for raw in [0, 1, 9314, 12_345, 38_000, 99_999, 1_234_567] {
            let p = Pct::from_raw(raw);
            let json = serde_json::to_string(&p).unwrap();
            let back: Pct = serde_json::from_str(&json).unwrap();
            assert_eq!(back, p, "{json}");
        }
    }

    #[test]
    fn json_rejects_extra_precision_and_non_numbers() {
        assert!(serde_json::from_str::<Pct>("93.145").is_err());
        assert!(serde_json::from_str::<Pct>("\"93.14\"").is_err());
        assert_eq!(serde_json::from_str::<ExpRate>("12.345").unwrap().raw(), 12_345);
        assert_eq!(serde_json::from_str::<Pct>("40").unwrap().raw(), 4000);
    }

    #[test]
    fn json_numbers_are_exact() {
        assert_eq!(serde_json::to_string(&Pct::from_raw(9314)).unwrap(), "93.14");
        assert_eq!(serde_json::to_string(&Pct::from_raw(10_000)).unwrap(), "100.00");
        assert_eq!(serde_json::to_string(&Pct::from_raw(-5)).unwrap(), "-0.05");
        assert_eq!(serde_json::from_str::<Pct>("-0").unwrap().raw(), 0);
        assert!(serde_json::from_str::<Pct>("1e2").is_err(), "exponents are refused");
        assert!(serde_json::from_str::<Pct>("93.140").is_err(), "digits beyond the precision are refused");
        // Through a `Value` and back to text, as PATCH bodies are, every value survives.
        for raw in (-100_000..100_000).step_by(7) {
            let v = serde_json::to_value(Pct::from_raw(raw)).unwrap();
            assert_eq!(serde_json::from_str::<Pct>(&v.to_string()).unwrap().raw(), raw);
        }
        let big = i64::MAX;
        let json = serde_json::to_string(&Pct::from_raw(big)).unwrap();
        assert_eq!(serde_json::from_str::<Pct>(&json).unwrap().raw(), big);
    }
}
