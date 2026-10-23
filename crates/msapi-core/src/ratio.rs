//! Exact dimensionless ratios for damage formulas.

use std::cmp::Ordering;
use std::fmt::{self, Write as _};

use crate::decimal::format_uint;

#[cfg(feature = "verus")]
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::arith::{
    gcd_spec, lemma_divides_exact, lemma_gcd_one, lemma_reduced_coprime, lemma_same_value, lemma_same_value_scaled,
};

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
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ratio {
    num: u128,
    den: u128,
}

#[cfg(feature = "verus")]
verus! {

impl Ratio {
    /// The numerator, for specs.
    pub closed spec fn n(self) -> int {
        self.num as int
    }

    /// The denominator, for specs.
    pub closed spec fn d(self) -> int {
        self.den as int
    }

    /// Positive denominator, lowest terms. Every constructor ensures it.
    pub open spec fn wf(self) -> bool {
        &&& self.d() > 0
        &&& self.n() >= 0
        &&& gcd_spec(self.n() as nat, self.d() as nat) == 1
    }

    /// `self` is the fraction `n / d`.
    pub open spec fn is(self, n: int, d: int) -> bool {
        self.n() * d == n * self.d()
    }

    /// The numerator and denominator fit in `u128`.
    pub proof fn lemma_bounds(self)
        ensures 0 <= self.n() <= u128::MAX, 0 <= self.d() <= u128::MAX,
    {
    }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r as nat == gcd_spec(a as nat, b as nat)))]
const fn gcd(a: u128, b: u128) -> u128 {
    let (mut x, mut y) = (a, b);
    #[cfg_attr(feature = "verus", verus_spec(
        invariant gcd_spec(x as nat, y as nat) == gcd_spec(a as nat, b as nat)
        decreases y
    ))]
    while y != 0 {
        let rem = x % y;
        x = y;
        y = rem;
    }
    x
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Ratio {
    /// Zero.
    #[cfg_attr(feature = "verus", verus_spec(ensures Self::ZERO.wf(), Self::ZERO.is(0, 1), Self::ZERO.n() == 0, Self::ZERO.d() == 1))]
    pub const ZERO: Self = Self::from_int(0);
    /// One.
    #[cfg_attr(feature = "verus", verus_spec(ensures Self::ONE.wf(), Self::ONE.is(1, 1), Self::ONE.n() == 1, Self::ONE.d() == 1))]
    pub const ONE: Self = Self::from_int(1);

    /// `num / den` in lowest terms. `None` if `den` is zero.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            den == 0 <==> r is None,
            r matches Some(r) ==> r.wf() && r.is(num as int, den as int) && r.n() <= num && r.d() <= den,
    ))]
    pub const fn new(num: u128, den: u128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let g = gcd(num, den);
        proof! {
            lemma_reduced_coprime(num as nat, den as nat);
            lemma_divides_exact(g as nat, num as nat);
            lemma_divides_exact(g as nat, den as nat);
            let (x, y) = (num as nat / g as nat, den as nat / g as nat);
            assert(x * den == num * y) by (nonlinear_arith)
                requires num == g * x, den == g * y;
            assert(x <= num && y <= den) by (nonlinear_arith)
                requires num == g * x, den == g * y, g >= 1;
        }
        Some(Self { num: num / g, den: den / g })
    }

    /// A whole number.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(n as int, 1), r.n() == n, r.d() == 1))]
    pub const fn from_int(n: u64) -> Self {
        proof! { lemma_gcd_one(n as nat); }
        Self { num: n as u128, den: 1 }
    }

    /// Numerator in lowest terms.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.n()))]
    pub const fn numer(self) -> u128 {
        self.num
    }

    /// Denominator in lowest terms.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.d()))]
    pub const fn denom(self) -> u128 {
        self.den
    }

    /// `self × rhs`, or `None` on overflow.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(), rhs.wf(),
        ensures
            r matches Some(r) ==> r.wf() && r.is(self.n() * rhs.n(), self.d() * rhs.d()),
            self.n() * rhs.n() <= u128::MAX && self.d() * rhs.d() <= u128::MAX ==> r is Some,
    ))]
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        // Cross-reduce first so intermediate products stay small.
        let g1 = gcd(self.num, rhs.den);
        let g2 = gcd(rhs.num, self.den);
        proof! {
            lemma_reduced_coprime(self.num as nat, rhs.den as nat);
            lemma_reduced_coprime(rhs.num as nat, self.den as nat);
            lemma_divides_exact(g1 as nat, self.num as nat);
            lemma_divides_exact(g1 as nat, rhs.den as nat);
            lemma_divides_exact(g2 as nat, rhs.num as nat);
            lemma_divides_exact(g2 as nat, self.den as nat);
        }
        proof! {
            // Cross-reducing only shrinks the products, so it adds no overflow.
            let (a, b, c, d) = (self.num as int, self.den as int, rhs.num as int, rhs.den as int);
            let (ka, kb, kc, kd) = (a / g1 as int, b / g2 as int, c / g2 as int, d / g1 as int);
            assert(ka * kc <= a * c && kb * kd <= b * d) by (nonlinear_arith)
                requires a == g1 * ka, d == g1 * kd, c == g2 * kc, b == g2 * kb, g1 >= 1, g2 >= 1,
                    ka >= 0, kb >= 0, kc >= 0, kd >= 0;
        }
        let num = (self.num / g1).checked_mul(rhs.num / g2)?;
        let den = (self.den / g2).checked_mul(rhs.den / g1)?;
        proof! {
            let (a, b, c, d) = (self.num as int, self.den as int, rhs.num as int, rhs.den as int);
            let (ka, kb, kc, kd) = (a / g1 as int, b / g2 as int, c / g2 as int, d / g1 as int);
            assert(den > 0) by (nonlinear_arith) requires den == kb * kd, kb > 0, kd > 0;
            assert(num * (b * d) == (a * c) * den) by (nonlinear_arith)
                requires a == g1 * ka, d == g1 * kd, c == g2 * kc, b == g2 * kb,
                    num == ka * kc, den == kb * kd;
        }
        let r = Self::new(num, den);
        proof! {
            if let Some(r) = r {
                lemma_same_value(r.n(), r.d(), num as int, den as int,
                    self.n() * rhs.n(), self.d() * rhs.d());
            }
        }
        r
    }

    /// `self ÷ rhs`, or `None` on overflow or division by zero.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(), rhs.wf(),
        ensures
            rhs.n() == 0 ==> r is None,
            r matches Some(r) ==> r.wf() && r.is(self.n() * rhs.d(), self.d() * rhs.n()),
    ))]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let inv = Self::new(rhs.den, rhs.num)?;
        let r = self.checked_mul(inv);
        proof! {
            if let Some(r) = r {
                assert(r.n() * (inv.d() * self.d()) == (inv.n() * self.n()) * r.d()) by (nonlinear_arith)
                    requires r.n() * (self.d() * inv.d()) == (self.n() * inv.n()) * r.d();
                lemma_same_value_scaled(r.n(), r.d(), inv.n(), inv.d(), self.n(), self.d(),
                    rhs.d(), rhs.n());
                assert(r.n() * (self.d() * rhs.n()) == (self.n() * rhs.d()) * r.d()) by (nonlinear_arith)
                    requires r.n() * (rhs.n() * self.d()) == (rhs.d() * self.n()) * r.d();
            }
        }
        r
    }

    /// `self + rhs`, or `None` on overflow.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(), rhs.wf(),
        ensures
            r matches Some(r) ==> r.wf()
                && r.is(self.n() * rhs.d() + rhs.n() * self.d(), self.d() * rhs.d()),
    ))]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        let g = gcd(self.den, rhs.den);
        proof! {
            lemma_reduced_coprime(self.den as nat, rhs.den as nat);
            lemma_divides_exact(g as nat, self.den as nat);
            lemma_divides_exact(g as nat, rhs.den as nat);
        }
        let den = (self.den / g).checked_mul(rhs.den)?;
        let num = self.num.checked_mul(rhs.den / g)?.checked_add(rhs.num.checked_mul(self.den / g)?)?;
        proof! {
            let (a, b, c, d) = (self.num as int, self.den as int, rhs.num as int, rhs.den as int);
            let (x, y) = (b / g as int, d / g as int);
            assert(x > 0) by (nonlinear_arith) requires b == g * x, b > 0;
            assert(den > 0) by (nonlinear_arith) requires den == x * d, x > 0, d > 0;
            assert(num * (b * d) == (a * d + c * b) * den) by (nonlinear_arith)
                requires b == g * x, d == g * y, den == x * d, num == a * y + c * x;
        }
        let r = Self::new(num, den);
        proof! {
            if let Some(r) = r {
                lemma_same_value(r.n(), r.d(), num as int, den as int,
                    self.n() * rhs.d() + rhs.n() * self.d(), self.d() * rhs.d());
            }
        }
        r
    }

    /// `max(0, self - rhs)`, or `None` on overflow.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(), rhs.wf(),
        ensures
            r matches Some(r) ==> r.wf() && if self.n() * rhs.d() >= rhs.n() * self.d() {
                r.is(self.n() * rhs.d() - rhs.n() * self.d(), self.d() * rhs.d())
            } else {
                r.n() == 0
            },
    ))]
    pub fn checked_saturating_sub(self, rhs: Self) -> Option<Self> {
        let g = gcd(self.den, rhs.den);
        proof! {
            lemma_reduced_coprime(self.den as nat, rhs.den as nat);
            lemma_divides_exact(g as nat, self.den as nat);
            lemma_divides_exact(g as nat, rhs.den as nat);
        }
        let den = (self.den / g).checked_mul(rhs.den)?;
        let a = self.num.checked_mul(rhs.den / g)?;
        let b = rhs.num.checked_mul(self.den / g)?;
        let diff = a.saturating_sub(b);
        proof! {
            let (an, ad, bn, bd) = (self.num as int, self.den as int, rhs.num as int, rhs.den as int);
            let (x, y) = (ad / g as int, bd / g as int);
            assert(x > 0) by (nonlinear_arith) requires ad == g * x, ad > 0;
            assert(den > 0) by (nonlinear_arith) requires den == x * bd, x > 0, bd > 0;
            assert(a * g == an * bd && b * g == bn * ad) by (nonlinear_arith)
                requires ad == g * x, bd == g * y, a == an * y, b == bn * x;
            assert((a >= b) == (an * bd >= bn * ad)) by (nonlinear_arith)
                requires a * g == an * bd, b * g == bn * ad, g > 0;
            if a >= b {
                assert(diff * (ad * bd) == (an * bd - bn * ad) * den) by (nonlinear_arith)
                    requires ad == g * x, bd == g * y, den == x * bd, diff == a - b,
                        a == an * y, b == bn * x;
            }
        }
        let r = Self::new(diff, den);
        proof! {
            if let Some(r) = r {
                if a >= b {
                    lemma_same_value(r.n(), r.d(), diff as int, den as int,
                        self.n() * rhs.d() - rhs.n() * self.d(), self.d() * rhs.d());
                } else {
                    assert(r.n() * den == 0);
                    assert(r.n() == 0) by (nonlinear_arith) requires r.n() * den == 0, den > 0;
                }
            }
        }
        r
    }

    /// Rounds down.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(),
        ensures r * self.d() <= self.n() < (r + 1) * self.d(),
    ))]
    pub const fn floor(self) -> u128 {
        let q = self.num / self.den;
        proof! {
            lemma_fundamental_div_mod(self.num as int, self.den as int);
            let (n, d) = (self.num as int, self.den as int);
            assert(q * d <= n < (q + 1) * d) by (nonlinear_arith)
                requires n == d * q + n % d, 0 <= n % d < d;
        }
        q
    }

    /// Rounds to nearest, halves up.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(),
        ensures r * 2 * self.d() <= 2 * self.n() + self.d() < (r + 1) * 2 * self.d(),
    ))]
    pub const fn round_half_up(self) -> u128 {
        let (q, rem) = (self.num / self.den, self.num % self.den);
        proof! {
            lemma_fundamental_div_mod(self.num as int, self.den as int);
            let (n, d) = (self.num as int, self.den as int);
            if rem >= d - rem {
                assert(q * 2 <= n) by (nonlinear_arith) requires n == d * q + rem, rem >= d - rem, rem < d, q >= 0;
                assert((q + 1) * 2 * d <= 2 * n + d < (q + 2) * 2 * d) by (nonlinear_arith)
                    requires n == d * q + rem, rem >= d - rem, rem < d;
            } else {
                assert(q * 2 * d <= 2 * n + d < (q + 1) * 2 * d) by (nonlinear_arith)
                    requires n == d * q + rem, rem < d - rem, rem >= 0;
            }
        }
        // `rem >= den - rem` is `2·rem >= den` without the overflow.
        if rem >= self.den - rem { q + 1 } else { q }
    }

    /// Compares `self` and `other` exactly, without overflow.
    ///
    /// Equal integer parts decide nothing, so compare the fractional parts by
    /// their reciprocals: `r1/b < r2/d` exactly when `d/r2 < b/r1`. The cross
    /// difference `a·d - c·b` is unchanged at every step, and the denominators
    /// shrink, as in Euclid's algorithm.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        requires self.wf(), other.wf(),
        ensures
            (r == Ordering::Less) == (self.n() * other.d() < other.n() * self.d()),
            (r == Ordering::Equal) == (self.n() * other.d() == other.n() * self.d()),
            (r == Ordering::Greater) == (self.n() * other.d() > other.n() * self.d()),
    ))]
    fn compare(self, other: Self) -> Ordering {
        let (mut a, mut b, mut c, mut d) = (self.num, self.den, other.num, other.den);
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                b > 0, d > 0,
                a * d - c * b == self.n() * other.d() - other.n() * self.d(),
            decreases b + d
        ))]
        loop {
            let (q1, q2) = (a / b, c / d);
            let (r1, r2) = (a % b, c % d);
            proof! {
                lemma_fundamental_div_mod(a as int, b as int);
                lemma_fundamental_div_mod(c as int, d as int);
            }
            if q1 != q2 {
                proof! {
                    let (a, b, c, d) = (a as int, b as int, c as int, d as int);
                    if q1 < q2 {
                        assert(a * d < c * b) by (nonlinear_arith)
                            requires a == b * q1 + r1, c == d * q2 + r2, r1 < b, q1 + 1 <= q2,
                                b > 0, d > 0, r2 >= 0;
                    } else {
                        assert(a * d > c * b) by (nonlinear_arith)
                            requires a == b * q1 + r1, c == d * q2 + r2, r2 < d, q2 + 1 <= q1,
                                b > 0, d > 0, r1 >= 0;
                    }
                }
                return if q1 < q2 { Ordering::Less } else { Ordering::Greater };
            }
            proof! {
                let (a, b, c, d) = (a as int, b as int, c as int, d as int);
                assert(a * d - c * b == r1 * d - r2 * b) by (nonlinear_arith)
                    requires a == b * q1 + r1, c == d * q1 + r2;
            }
            if r1 == 0 || r2 == 0 {
                proof! {
                    assert(r1 * d >= 0 && r2 * b >= 0) by (nonlinear_arith) requires b > 0, d > 0;
                    assert(r1 > 0 ==> r1 * d > 0) by (nonlinear_arith) requires d > 0;
                    assert(r2 > 0 ==> r2 * b > 0) by (nonlinear_arith) requires b > 0;
                    assert(r1 == 0 ==> r1 * d == 0) by (nonlinear_arith);
                    assert(r2 == 0 ==> r2 * b == 0) by (nonlinear_arith);
                }
                return if r1 == r2 {
                    Ordering::Equal
                } else if r1 == 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            }
            // (a, b, c, d) ← (d, r2, b, r1)
            a = d;
            c = b;
            b = r2;
            d = r1;
            proof! {
                assert(a * d - c * b == r1 * a - r2 * c) by (nonlinear_arith)
                    requires b == r2, d == r1;
            }
        }
    }
}

impl PartialOrd for Ratio {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ratio {
    fn cmp(&self, other: &Self) -> Ordering {
        self.compare(*other)
    }
}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = format_uint(self.num);
        if self.den != 1 {
            text.push(b'/');
            text.extend(format_uint(self.den));
        }
        text.into_iter().try_for_each(|b| f.write_char(char::from(b)))
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
        assert!(big.checked_mul(big).is_none());
    }

    #[test]
    fn ordering_is_exact_where_cross_products_overflow() {
        // Floats round both of these to 1.0.
        let below = Ratio::new(u128::MAX - 1, u128::MAX).unwrap();
        let above = Ratio::new(u128::MAX, u128::MAX - 1).unwrap();
        assert!(below < Ratio::ONE && Ratio::ONE < above);
        let a = Ratio::new(u128::MAX - 2, u128::MAX - 1).unwrap();
        assert!(a < below);
        assert_eq!(below.cmp(&below), Ordering::Equal);
    }

    #[test]
    fn rounding_at_the_boundaries() {
        // `2 × rem` overflowed here before rounding was verified.
        assert_eq!(Ratio::new(u128::MAX, u128::MAX - 1).unwrap().round_half_up(), 1);
        assert_eq!(Ratio::new(u128::MAX, 2).unwrap().round_half_up(), u128::MAX / 2 + 1);
        assert_eq!(Ratio::new(5, 2).unwrap().round_half_up(), 3);
        assert_eq!(Ratio::new(49, 20).unwrap().round_half_up(), 2);
        assert_eq!(Ratio::new(1, 3).unwrap().floor(), 0);
    }
}
