//! Number theory for the Verus proofs: greatest common divisors.
//!
//! Only compiled with the `verus` feature. `vstd` proves facts about `%` and
//! `/` but has no gcd, so the three facts [`crate::Ratio`] needs live here.

use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;

verus! {

/// Euclid's gcd, the spec the exec `gcd` in `ratio.rs` is checked against.
pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd_spec(b, a % b) }
}

/// `n` is a multiple of `d`, for `d > 0`.
pub open spec fn divides(d: nat, n: nat) -> bool {
    n % d == 0
}

/// `n == d × (n / d)` when `d` divides `n`.
pub proof fn lemma_divides_exact(d: nat, n: nat)
    requires d > 0, divides(d, n),
    ensures n == d * (n / d),
{
    lemma_fundamental_div_mod(n as int, d as int);
}

/// `d` divides `d × k`.
pub proof fn lemma_divides_multiple(d: nat, k: nat)
    requires d > 0,
    ensures divides(d, d * k),
{
    lemma_mod_multiples_basic(k as int, d as int);
    assert(k * d == d * k) by (nonlinear_arith);
}

/// The gcd of two numbers, not both zero, is positive.
pub proof fn lemma_gcd_pos(a: nat, b: nat)
    requires a > 0 || b > 0,
    ensures gcd_spec(a, b) > 0,
    decreases b,
{
    if b > 0 {
        lemma_gcd_pos(b, a % b);
    }
}

/// The gcd divides both arguments.
pub proof fn lemma_gcd_divides(a: nat, b: nat)
    requires gcd_spec(a, b) > 0,
    ensures divides(gcd_spec(a, b), a), divides(gcd_spec(a, b), b),
    decreases b,
{
    let g = gcd_spec(a, b);
    if b == 0 {
        lemma_divides_multiple(g, 1);
        lemma_divides_multiple(g, 0);
    } else {
        lemma_gcd_divides(b, a % b);
        let r = a % b;
        let q = a / b;
        lemma_fundamental_div_mod(a as int, b as int);
        lemma_divides_exact(g, b);
        lemma_divides_exact(g, r);
        let kb = b / g;
        let kr = r / g;
        assert(a == g * (kb * q + kr)) by (nonlinear_arith)
            requires a == b * q + r, b == g * kb, r == g * kr;
        lemma_divides_multiple(g, kb * q + kr);
    }
}

/// Every common divisor of `a` and `b` divides their gcd.
pub proof fn lemma_common_divisor_divides_gcd(a: nat, b: nat, d: nat)
    requires d > 0, divides(d, a), divides(d, b),
    ensures divides(d, gcd_spec(a, b)),
    decreases b,
{
    if b > 0 {
        let r = a % b;
        let q = a / b;
        lemma_fundamental_div_mod(a as int, b as int);
        lemma_divides_exact(d, a);
        lemma_divides_exact(d, b);
        let ka = a / d;
        let kb = b / d;
        assert(r as int == d * (ka - kb * q)) by (nonlinear_arith)
            requires a == b * q + r, a == d * ka, b == d * kb;
        lemma_mod_multiples_basic(ka - kb * q, d as int);
        assert((ka - kb * q) * d == d * (ka - kb * q)) by (nonlinear_arith);
        lemma_common_divisor_divides_gcd(b, r, d);
    }
}

/// Dividing two numbers by their gcd leaves them coprime.
pub proof fn lemma_reduced_coprime(a: nat, b: nat)
    requires b > 0,
    ensures
        gcd_spec(a, b) > 0,
        divides(gcd_spec(a, b), a),
        divides(gcd_spec(a, b), b),
        b / gcd_spec(a, b) > 0,
        gcd_spec(a / gcd_spec(a, b), b / gcd_spec(a, b)) == 1,
{
    let g = gcd_spec(a, b);
    lemma_gcd_pos(a, b);
    lemma_gcd_divides(a, b);
    lemma_divides_exact(g, a);
    lemma_divides_exact(g, b);
    let (x, y) = (a / g, b / g);
    assert(y > 0) by (nonlinear_arith) requires b == g * y, b > 0;
    let h = gcd_spec(x, y);
    lemma_gcd_pos(x, y);
    lemma_gcd_divides(x, y);
    lemma_divides_exact(h, x);
    lemma_divides_exact(h, y);
    let (hx, hy) = (x / h, y / h);
    assert(a == (g * h) * hx && b == (g * h) * hy) by (nonlinear_arith)
        requires a == g * x, b == g * y, x == h * hx, y == h * hy;
    assert(g * h > 0) by (nonlinear_arith) requires g > 0, h > 0;
    lemma_divides_multiple(g * h, hx);
    lemma_divides_multiple(g * h, hy);
    lemma_common_divisor_divides_gcd(a, b, g * h);
    lemma_divides_exact(g * h, g);
    let m = g / (g * h);
    assert(h == 1) by (nonlinear_arith) requires g == (g * h) * m, g > 0, h > 0;
}

/// `gcd(n, 1) == 1`, so whole numbers are already in lowest terms.
pub proof fn lemma_gcd_one(n: nat)
    ensures gcd_spec(n, 1) == 1,
{
    assert(n % 1 == 0);
    reveal_with_fuel(gcd_spec, 2);
}

} // verus!
