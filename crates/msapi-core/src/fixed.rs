//! Exact decimals with a fixed number of fractional digits.

use std::fmt::{self, Write as _};
use std::str::FromStr;

use serde::de::{self, Visitor};

use crate::decimal::{DecimalError, format_decimal, parse_decimal};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "verus")]
use vstd::prelude::*;

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

impl fmt::Display for FixedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "`{s}` is not a decimal number"),
            Self::TooPrecise { max_decimals } => {
                write!(f, "more than {max_decimals} decimal places; send the value exactly as displayed")
            }
            Self::OutOfRange => f.write_str("number out of range"),
        }
    }
}

impl std::error::Error for FixedError {}

/// Largest magnitude accepted from a float: beyond 2^53 an `f64` is no longer exact.
const MAX_EXACT_F64: f64 = 9_007_199_254_740_992.0;

impl<const DP: u32> Fixed<DP> {
    /// Number of raw units in `1`.
    pub const SCALE: i64 = 10_i64.pow(DP);

    /// Zero.
    pub const ZERO: Self = Self(0);

    /// Builds a value from a whole number.
    ///
    /// ```
    /// assert_eq!(msapi_core::Pct::from_int(40).to_string(), "40.00");
    /// ```
    #[must_use]
    pub const fn from_int(n: i64) -> Self {
        Self(n * Self::SCALE)
    }

    /// The value as a float, for display or for JSON.
    #[must_use]
    #[allow(
        clippy::cast_precision_loss,
        reason = "raw is bounded by MAX_EXACT_F64 on every constructor that takes input"
    )]
    pub fn to_f64(self) -> f64 {
        self.0 as f64 / Self::SCALE as f64
    }

    /// Converts a float, rejecting values with more than `DP` decimals.
    ///
    /// JSON numbers arrive as `f64`, so `93.14` is really `93.1400000000000005`.
    /// The check allows for that representation error and nothing more.
    ///
    /// ```
    /// use msapi_core::Pct;
    /// assert_eq!(Pct::from_f64(93.14).unwrap().raw(), 9314);
    /// assert!(Pct::from_f64(0.125).is_err());
    /// assert!(Pct::from_f64(f64::NAN).is_err());
    /// ```
    pub fn from_f64(x: f64) -> Result<Self, FixedError> {
        if !x.is_finite() {
            return Err(FixedError::Invalid(x.to_string()));
        }
        #[allow(clippy::cast_precision_loss, reason = "SCALE is at most 10^DP, far below 2^53")]
        let scaled = x * Self::SCALE as f64;
        if scaled.abs() >= MAX_EXACT_F64 {
            return Err(FixedError::OutOfRange);
        }
        let rounded = scaled.round();
        // Relative tolerance: representation error grows with magnitude.
        let tolerance = 1e-9 * scaled.abs().max(1.0);
        if (scaled - rounded).abs() > tolerance {
            return Err(FixedError::TooPrecise { max_decimals: DP });
        }
        #[allow(clippy::cast_possible_truncation, reason = "bounded by MAX_EXACT_F64 above")]
        Ok(Self(rounded as i64))
    }
}

impl<const DP: u32> std::ops::Add for Fixed<DP> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0.saturating_add(rhs.0))
    }
}

impl<const DP: u32> std::ops::Sub for Fixed<DP> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0.saturating_sub(rhs.0))
    }
}

impl<const DP: u32> FromStr for Fixed<DP> {
    type Err = FixedError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_decimal(s.as_bytes(), DP).map(Self).map_err(|e| match e {
            DecimalError::Invalid => FixedError::Invalid(s.to_owned()),
            DecimalError::TooPrecise => FixedError::TooPrecise { max_decimals: DP },
            DecimalError::OutOfRange => FixedError::OutOfRange,
        })
    }
}

impl<const DP: u32> fmt::Display for Fixed<DP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `SCALE` is `10^DP` in an `i64`, which only compiles for `DP <= 18`,
        // the precondition of the proven `format_decimal`.
        let _ = Self::SCALE;
        format_decimal(self.0, DP).into_iter().try_for_each(|b| f.write_char(char::from(b)))
    }
}

impl<const DP: u32> fmt::Debug for Fixed<DP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const DP: u32> Serialize for Fixed<DP> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_f64(self.to_f64())
    }
}

impl<'de, const DP: u32> Deserialize<'de> for Fixed<DP> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FixedVisitor<const DP: u32>;

        impl<const DP: u32> Visitor<'_> for FixedVisitor<DP> {
            type Value = Fixed<DP>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "a number with at most {DP} decimal places")
            }

            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Self::Value, E> {
                v.checked_mul(Fixed::<DP>::SCALE).map(Fixed).ok_or_else(|| E::custom(FixedError::OutOfRange))
            }

            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Self::Value, E> {
                let v = i64::try_from(v).map_err(|_| E::custom(FixedError::OutOfRange))?;
                self.visit_i64(v)
            }

            fn visit_f64<E: de::Error>(self, v: f64) -> Result<Self::Value, E> {
                Fixed::from_f64(v).map_err(E::custom)
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
    fn every_two_decimal_value_survives_float_conversion() {
        // Exhaustive over 0.00..=1000.00: the tolerance must accept every
        // exactly representable display value and nothing between them.
        for raw in 0..=100_000 {
            let f = Pct::from_raw(raw).to_f64();
            assert_eq!(Pct::from_f64(f).unwrap().raw(), raw);
        }
        assert!(Pct::from_f64(10.005).is_err());
    }
}
