//! Exact dimensionless ratios for damage formulas.

use std::cmp::Ordering;
use std::fmt;

use crate::fixed::Fixed;

/// An exact, non-negative rational number with no unit.
///
/// Damage formulas multiply a dozen factors and floor at specific steps. Doing
/// that in `f64` makes "is it 236,118 or 236,117?" depend on evaluation order;
/// doing it in exact fractions makes it depend only on the formula.
///
/// Every operation is checked: a result that would overflow `u128` returns
/// `None` rather than wrapping.
///
/// ```
/// use msapi_core::Ratio;
///
/// let r = Ratio::new(3, 4).unwrap().checked_mul(Ratio::new(2, 3).unwrap()).unwrap();
/// assert_eq!(r.to_string(), "1/2");
/// assert_eq!(Ratio::new(7, 2).unwrap().floor(), 3);
/// assert_eq!(Ratio::new(7, 2).unwrap().round_half_up(), 4);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ratio {
    num: u128,
    den: u128,
}

const fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Ratio {
    /// Zero.
    pub const ZERO: Self = Self { num: 0, den: 1 };
    /// One.
    pub const ONE: Self = Self { num: 1, den: 1 };

    /// `num / den` in lowest terms. `None` if `den` is zero.
    #[must_use]
    pub const fn new(num: u128, den: u128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let g = gcd(num, den);
        let g = if g == 0 { 1 } else { g };
        Some(Self { num: num / g, den: den / g })
    }

    /// A whole number.
    #[must_use]
    pub const fn from_int(n: u64) -> Self {
        Self { num: n as u128, den: 1 }
    }

    /// `value / per`, where `value` is a [`Fixed`]. Negative values clamp to zero,
    /// since no factor in a damage formula is negative.
    #[must_use]
    pub fn from_fixed<const DP: u32>(value: Fixed<DP>, per: u64) -> Self {
        let num = u128::try_from(value.raw()).unwrap_or(0);
        let scale = u128::try_from(Fixed::<DP>::SCALE).unwrap_or(1);
        Self::new(num, scale * u128::from(per.max(1))).unwrap_or(Self::ZERO)
    }

    /// Numerator in lowest terms.
    #[must_use]
    pub const fn numer(self) -> u128 {
        self.num
    }

    /// Denominator in lowest terms.
    #[must_use]
    pub const fn denom(self) -> u128 {
        self.den
    }

    /// `self × rhs`, or `None` on overflow.
    #[must_use]
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        // Cross-reduce first so intermediate products stay small.
        let g1 = gcd(self.num, rhs.den).max(1);
        let g2 = gcd(rhs.num, self.den).max(1);
        let num = (self.num / g1).checked_mul(rhs.num / g2)?;
        let den = (self.den / g2).checked_mul(rhs.den / g1)?;
        Self::new(num, den)
    }

    /// `self ÷ rhs`, or `None` on overflow or division by zero.
    #[must_use]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        self.checked_mul(Self::new(rhs.den, rhs.num)?)
    }

    /// `self + rhs`, or `None` on overflow.
    #[must_use]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        let g = gcd(self.den, rhs.den).max(1);
        let den = (self.den / g).checked_mul(rhs.den)?;
        let num = self.num.checked_mul(rhs.den / g)?.checked_add(rhs.num.checked_mul(self.den / g)?)?;
        Self::new(num, den)
    }

    /// `max(0, self - rhs)`, or `None` on overflow.
    #[must_use]
    pub fn checked_saturating_sub(self, rhs: Self) -> Option<Self> {
        let g = gcd(self.den, rhs.den).max(1);
        let den = (self.den / g).checked_mul(rhs.den)?;
        let a = self.num.checked_mul(rhs.den / g)?;
        let b = rhs.num.checked_mul(self.den / g)?;
        Self::new(a.saturating_sub(b), den)
    }

    /// The product of several ratios, or `None` on overflow.
    pub fn product(factors: impl IntoIterator<Item = Self>) -> Option<Self> {
        factors.into_iter().try_fold(Self::ONE, Self::checked_mul)
    }

    /// Rounds down.
    #[must_use]
    pub const fn floor(self) -> u128 {
        self.num / self.den
    }

    /// Rounds to nearest, halves up.
    #[must_use]
    pub const fn round_half_up(self) -> u128 {
        (2 * (self.num % self.den) >= self.den) as u128 + self.num / self.den
    }

    /// An approximate float, for display only.
    #[must_use]
    #[allow(clippy::cast_precision_loss, reason = "display approximation by definition")]
    pub fn to_f64(self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ratio {
    fn cmp(&self, other: &Self) -> Ordering {
        // a/b vs c/d  ⇔  a·d vs c·b; widen through checked math, falling back to
        // floats only if the cross products overflow u128.
        match (self.num.checked_mul(other.den), other.num.checked_mul(self.den)) {
            (Some(l), Some(r)) => l.cmp(&r),
            _ => self.to_f64().total_cmp(&other.to_f64()),
        }
    }
}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 { write!(f, "{}", self.num) } else { write!(f, "{}/{}", self.num, self.den) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_is_exact_and_reduced() {
        let a = Ratio::new(10, 4).unwrap();
        assert_eq!((a.numer(), a.denom()), (5, 2));
        assert_eq!(a.checked_add(Ratio::new(1, 2).unwrap()).unwrap(), Ratio::from_int(3));
        assert_eq!(Ratio::ONE.checked_saturating_sub(a).unwrap(), Ratio::ZERO);
        assert_eq!(a.checked_div(a).unwrap(), Ratio::ONE);
        assert!(a.checked_div(Ratio::ZERO).is_none());
    }

    #[test]
    fn overflow_is_reported_not_wrapped() {
        let big = Ratio::new(u128::MAX, 1).unwrap();
        assert!(big.checked_mul(Ratio::from_int(2)).is_none());
        assert!(Ratio::product([big, big]).is_none());
    }

    #[test]
    fn rounding_at_the_boundaries() {
        assert_eq!(Ratio::new(5, 2).unwrap().round_half_up(), 3);
        assert_eq!(Ratio::new(49, 20).unwrap().round_half_up(), 2);
        assert_eq!(Ratio::new(1, 3).unwrap().floor(), 0);
    }
}
