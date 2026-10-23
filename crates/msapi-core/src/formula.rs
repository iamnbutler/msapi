//! The game's formulas as integer code, each checked by Verus against an
//! integer specification.
//!
//! The typed functions in [`crate::units`], [`crate::calc`] and
//! [`crate::stat`] unwrap their units and call these. Percentages arrive as raw
//! hundredths ([`crate::Pct::raw`], so `93.14%` is `9314`), and a factor
//! `1 + p` is `(10_000 + raw) / 10_000`.
//!
//! Each function's spec says what it returns when it returns `Some`. Where the
//! spec also says when it returns `None`, the function never reports overflow
//! for a result that fits.

#![allow(
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::manual_clamp,
    clippy::bool_to_int_with_if,
    reason = "plain branches and casts are what Verus checks; it has no specs for `clamp` or `From<bool>`"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::arith::{lemma_quotient_unique, lemma_rounding_agrees, lemma_same_value_scaled};
use crate::ratio::Ratio;

#[cfg(feature = "verus")]
verus! {

/// `max(0, x)`.
pub open spec fn clamp0(x: int) -> int {
    if x < 0 { 0 } else { x }
}

/// `n / d` rounded to nearest, halves up.
pub open spec fn round_div(n: int, d: int) -> int {
    (2 * n + d) / (2 * d)
}

/// `10_000 × (1 + p)` for a raw percentage, never negative.
pub open spec fn one_plus(raw: int) -> int {
    clamp0(10_000 + raw)
}

/// `10_000 × (1 - p)` for a raw percentage, never negative.
pub open spec fn one_minus(raw: int) -> int {
    clamp0(10_000 - raw)
}

/// `10_000^k`.
pub open spec fn whole_pow(k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { 10_000 * whole_pow((k - 1) as nat) }
}

/// `Π (10_000 + raw)` over Final Damage sources.
pub open spec fn stack_plus(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 1 } else { stack_plus(s.drop_last()) * one_plus(s.last() as int) }
}

/// `Π (10_000 - raw)` over Ignore Defense sources.
pub open spec fn stack_minus(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 1 } else { stack_minus(s.drop_last()) * one_minus(s.last() as int) }
}

/// The sum of a sequence.
pub open spec fn sum(s: Seq<u64>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

/// `4 × Σ primary + Σ secondary`.
pub open spec fn stat_value_spec(primary: Seq<u64>, secondary: Seq<u64>) -> int {
    4 * sum(primary) + sum(secondary)
}

/// `floor(base × (1 + p))`.
pub open spec fn scaled_spec(base: int, raw: int) -> int {
    base * one_plus(raw) / 10_000
}

/// The upper end of the actual damage range:
/// `round(weapon_constant × stat_value × attack / 100)`, with the constant in
/// ten-thousandths.
pub open spec fn upper_actual(wc: int, stat_value: int, attack: int) -> int {
    round_div(clamp0(wc) * stat_value * attack, 1_000_000)
}

/// The lower end: `round(upper × mastery)`.
pub open spec fn lower_actual(upper: int, mastery: int) -> int {
    round_div(upper * clamp0(mastery), 10_000)
}

/// Combat Power before the final floor, as a numerator and denominator.
pub open spec fn cp_num(stat_value: int, attack: int, cd: int, damage: int, fd: int, class_fd: Seq<i64>) -> int {
    stat_value * attack * clamp0(13_500 + cd) * one_plus(damage) * (one_plus(fd) * whole_pow(class_fd.len()))
}

/// See [`cp_num`].
pub open spec fn cp_den(class_fd: Seq<i64>) -> int {
    100 * 10_000 * 10_000 * (10_000 * stack_plus(class_fd))
}

/// The bow-normalised attack, with Euclidean (floor) division.
pub open spec fn bow_spec(flat: int, weapon: int, star_force: int, bow: int) -> int {
    if weapon == 0 { flat } else { flat + (bow - weapon) * (weapon + star_force) / weapon }
}

/// `r = (a·f)/(b·g)`, `a/b = p/q` and `f/g = s/t` give `r = (p·s)/(q·t)`.
proof fn lemma_is_mul(r: Ratio, a: Ratio, f: Ratio, p: int, q: int, s: int, t: int)
    requires a.wf(), f.wf(), r.is(a.n() * f.n(), a.d() * f.d()), a.is(p, q), f.is(s, t),
    ensures r.is(p * s, q * t),
{
    lemma_same_value_scaled(r.n(), r.d(), a.n(), a.d(), f.n(), f.d(), p, q);
    assert(r.n() * (f.d() * q) == (f.n() * p) * r.d()) by (nonlinear_arith)
        requires r.n() * (q * f.d()) == (p * f.n()) * r.d();
    lemma_same_value_scaled(r.n(), r.d(), f.n(), f.d(), p, q, s, t);
    assert(r.n() * (q * t) == (p * s) * r.d()) by (nonlinear_arith)
        requires r.n() * (t * q) == (s * p) * r.d();
}

/// `floor` agrees with integer division for equal fractions.
proof fn lemma_floor(r: Ratio, q: int, n: int, d: int)
    requires r.wf(), r.is(n, d), d > 0, q * r.d() <= r.n() < (q + 1) * r.d(),
    ensures q == n / d,
{
    assert(q * (1 * r.d()) <= 1 * r.n() + 0 * r.d() < (q + 1) * (1 * r.d())) by (nonlinear_arith)
        requires q * r.d() <= r.n() < (q + 1) * r.d();
    lemma_rounding_agrees(q, r.n(), r.d(), n, d, 1, 1, 0);
    assert((1 * n + 0 * d) / (1 * d) == n / d) by (nonlinear_arith);
}

/// `round_half_up` agrees with [`round_div`] for equal fractions.
proof fn lemma_round(r: Ratio, q: int, n: int, d: int)
    requires r.wf(), r.is(n, d), d > 0, q * 2 * r.d() <= 2 * r.n() + r.d() < (q + 1) * 2 * r.d(),
    ensures q == round_div(n, d),
{
    assert(q * (2 * r.d()) <= 2 * r.n() + 1 * r.d() < (q + 1) * (2 * r.d())) by (nonlinear_arith)
        requires q * 2 * r.d() <= 2 * r.n() + r.d() < (q + 1) * 2 * r.d();
    lemma_rounding_agrees(q, r.n(), r.d(), n, d, 2, 2, 1);
    assert((2 * n + 1 * d) / (2 * d) == round_div(n, d)) by (nonlinear_arith);
}

proof fn lemma_sum_prefix(s: Seq<u64>, i: int)
    requires 0 <= i <= s.len(),
    ensures 0 <= sum(s.take(i)) <= sum(s),
    decreases s.len(),
{
    if i == s.len() {
        assert(s.take(i) =~= s);
    } else {
        lemma_sum_prefix(s.drop_last(), i);
        assert(s.drop_last().take(i) =~= s.take(i));
    }
    lemma_sum_nonneg(s.take(i));
}

proof fn lemma_sum_nonneg(s: Seq<u64>)
    ensures sum(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sum_nonneg(s.drop_last());
    }
}

proof fn lemma_stack_plus_nonneg(s: Seq<i64>)
    ensures stack_plus(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_stack_plus_nonneg(s.drop_last());
        let (a, b) = (stack_plus(s.drop_last()), one_plus(s.last() as int));
        assert(a * b >= 0) by (nonlinear_arith) requires a >= 0, b >= 0;
    }
}

proof fn lemma_whole_pow_pos(k: nat)
    ensures whole_pow(k) > 0,
    decreases k,
{
    if k > 0 {
        lemma_whole_pow_pos((k - 1) as nat);
    }
}

} // verus!

/// `max(0, n) / d`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires d > 0,
    ensures r.wf(), r.is(clamp0(n as int), d as int), r.n() <= clamp0(n as int), r.d() <= d,
))]
#[must_use]
pub fn fraction(n: i128, d: u128) -> Ratio {
    let n = if n < 0 { 0 } else { n as u128 };
    match Ratio::new(n, d) {
        Some(r) => r,
        None => Ratio::from_int(0),
    }
}

/// `1 + p`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r.wf(), r.is(one_plus(raw as int), 10_000), r.n() <= one_plus(raw as int), r.d() <= 10_000,
))]
#[must_use]
pub fn one_plus_factor(raw: i64) -> Ratio {
    fraction(10_000 + raw as i128, 10_000)
}

/// `1 - p`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(one_minus(raw as int), 10_000)))]
#[must_use]
pub fn one_minus_factor(raw: i64) -> Ratio {
    fraction(10_000 - raw as i128, 10_000)
}

/// `p` itself as a fraction of one, never negative.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(clamp0(raw as int), 10_000)))]
#[must_use]
pub fn percent(raw: i64) -> Ratio {
    fraction(raw as i128, 10_000)
}

/// The average critical multiplier: `1.35 + cd`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(clamp0(13_500 + raw as int), 10_000)))]
#[must_use]
pub fn crit_factor(raw: i64) -> Ratio {
    fraction(13_500 + raw as i128, 10_000)
}

/// `(1 + a)(1 + b)…` over Final Damage sources.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(r) ==> r.wf() && r.is(stack_plus(raws@), whole_pow(raws@.len())),
))]
#[must_use]
pub fn stack_final_damage(raws: &[i64]) -> Option<Ratio> {
    let mut acc = Ratio::from_int(1);
    let mut i = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            0 <= i <= raws@.len(),
            acc.wf(),
            acc.is(stack_plus(raws@.take(i as int)), whole_pow(i as nat)),
        decreases raws@.len() - i
    ))]
    while i < raws.len() {
        let f = one_plus_factor(raws[i]);
        let next = acc.checked_mul(f)?;
        proof! {
            lemma_is_mul(next, acc, f, stack_plus(raws@.take(i as int)), whole_pow(i as nat),
                one_plus(raws@[i as int] as int), 10_000);
            assert(raws@.take(i + 1).drop_last() =~= raws@.take(i as int));
            assert(whole_pow((i + 1) as nat) == 10_000 * whole_pow(i as nat));
            assert(whole_pow(i as nat) * 10_000 == 10_000 * whole_pow(i as nat)) by (nonlinear_arith);
        }
        acc = next;
        i += 1;
    }
    proof! { assert(raws@.take(raws@.len() as int) =~= raws@); }
    Some(acc)
}

/// `(1 - a)(1 - b)…` over Ignore Defense sources: the defense left.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(r) ==> r.wf() && r.is(stack_minus(raws@), whole_pow(raws@.len())),
))]
#[must_use]
pub fn stack_ignore_defense(raws: &[i64]) -> Option<Ratio> {
    let mut acc = Ratio::from_int(1);
    let mut i = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            0 <= i <= raws@.len(),
            acc.wf(),
            acc.is(stack_minus(raws@.take(i as int)), whole_pow(i as nat)),
        decreases raws@.len() - i
    ))]
    while i < raws.len() {
        let f = one_minus_factor(raws[i]);
        let next = acc.checked_mul(f)?;
        proof! {
            lemma_is_mul(next, acc, f, stack_minus(raws@.take(i as int)), whole_pow(i as nat),
                one_minus(raws@[i as int] as int), 10_000);
            assert(raws@.take(i + 1).drop_last() =~= raws@.take(i as int));
            assert(whole_pow((i + 1) as nat) == 10_000 * whole_pow(i as nat));
            assert(whole_pow(i as nat) * 10_000 == 10_000 * whole_pow(i as nat)) by (nonlinear_arith);
        }
        acc = next;
        i += 1;
    }
    proof! { assert(raws@.take(raws@.len() as int) =~= raws@); }
    Some(acc)
}

/// The defense multiplier against a monster: `max(0, 1 - pdr × (1 - ied))`,
/// with the defense rate clamped to `[0%, 500%]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(r) ==> {
        let p = if pdr_raw < 0 { 0 } else if pdr_raw > 50_000 { 50_000 } else { pdr_raw as int };
        &&& r.wf()
        &&& r.is(clamp0(100_000_000 - p * one_minus(ied_raw as int)), 100_000_000)
    },
))]
#[must_use]
pub fn defense_factor(ied_raw: i64, pdr_raw: i64) -> Option<Ratio> {
    let clamped = if pdr_raw < 0 {
        0
    } else if pdr_raw > 50_000 {
        50_000
    } else {
        pdr_raw
    };
    let pdr = percent(clamped);
    let remaining = one_minus_factor(ied_raw);
    let hit = pdr.checked_mul(remaining)?;
    let one = Ratio::from_int(1);
    let r = one.checked_saturating_sub(hit)?;
    proof! {
        let (p, l, w) = (clamped as int, one_minus(ied_raw as int), 10_000int);
        lemma_is_mul(hit, pdr, remaining, p, 10_000, l, w);
        let (hn, hd) = (hit.n(), hit.d());
        // hit = (p·l) / 10^8, so `1 - hit` has the sign of `10^8 - p·l`.
        assert((1 * hd >= hn * 1) == (100_000_000 - p * l >= 0)) by (nonlinear_arith)
            requires hn * (100_000_000int) == (p * l) * hd, hd > 0;
        if 1 * hd >= hn * 1 {
            assert(r.n() * 100_000_000 == (100_000_000 - p * l) * r.d()) by (nonlinear_arith)
                requires r.n() * (1 * hd) == (1 * hd - hn * 1) * r.d(),
                    hn * (100_000_000int) == (p * l) * hd, hd > 0;
        } else {
            assert(r.n() * 100_000_000 == 0 * r.d()) by (nonlinear_arith) requires r.n() == 0;
        }
    }
    Some(r)
}

/// `w × Σ values`, or `None` exactly when that exceeds `u64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(r) ==> r == weight * sum(values@),
        r is None ==> weight * sum(values@) > u64::MAX,
))]
fn weighted_sum(values: &[u64], weight: u64) -> Option<u64> {
    let mut acc: u64 = 0;
    let mut i = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            0 <= i <= values@.len(),
            acc == weight * sum(values@.take(i as int)),
        decreases values@.len() - i
    ))]
    while i < values.len() {
        proof! {
            assert(values@.take(i + 1).drop_last() =~= values@.take(i as int));
            lemma_sum_prefix(values@, i + 1);
            lemma_sum_prefix(values@, i as int);
            let (s, t) = (sum(values@.take(i + 1)), sum(values@));
            assert(weight * s <= weight * t) by (nonlinear_arith) requires s <= t, weight >= 0;
            assert(weight * s == weight * sum(values@.take(i as int)) + weight * values@[i as int])
                by (nonlinear_arith) requires s == sum(values@.take(i as int)) + values@[i as int];
            assert(weight * values@[i as int] >= 0) by (nonlinear_arith) requires weight >= 0;
            assert(values@[i as int] * weight == weight * values@[i as int]) by (nonlinear_arith);
            assert(weight * sum(values@.take(i as int)) >= 0) by (nonlinear_arith)
                requires weight >= 0, sum(values@.take(i as int)) >= 0;
        }
        acc = acc.checked_add(values[i].checked_mul(weight)?)?;
        i += 1;
    }
    proof! { assert(values@.take(values@.len() as int) =~= values@); }
    Some(acc)
}

/// The stat value `4 × Σ primary + Σ secondary`, or `None` exactly when it
/// exceeds `u64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(r) ==> r == stat_value_spec(primary@, secondary@),
        r is None ==> stat_value_spec(primary@, secondary@) > u64::MAX,
))]
#[must_use]
pub fn stat_value(primary: &[u64], secondary: &[u64]) -> Option<u64> {
    proof! {
        lemma_sum_nonneg(primary@);
        lemma_sum_nonneg(secondary@);
    }
    let p = weighted_sum(primary, 4)?;
    let s = weighted_sum(secondary, 1)?;
    p.checked_add(s)
}

/// `floor(base × (1 + p))`, or `None` exactly when that exceeds `u64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(r) ==> r == scaled_spec(base as int, raw as int),
        r is None ==> scaled_spec(base as int, raw as int) > u64::MAX,
))]
#[must_use]
pub fn scaled(base: u64, raw: i64) -> Option<u64> {
    let b = Ratio::from_int(base);
    let f = one_plus_factor(raw);
    proof! {
        // base < 2^64 and 1 + p < 2^64, so the exact product fits in u128.
        assert(b.n() * f.n() <= u128::MAX) by (nonlinear_arith)
            requires 0 <= b.n() <= u64::MAX, 0 <= f.n() <= one_plus(raw as int),
                one_plus(raw as int) <= 10_000 + i64::MAX;
        assert(b.d() * f.d() <= u128::MAX) by (nonlinear_arith) requires b.d() == 1, f.d() <= 10_000;
    }
    let x = b.checked_mul(f)?;
    let q = x.floor();
    proof! {
        lemma_is_mul(x, b, f, base as int, 1, one_plus(raw as int), 10_000);
        assert(base * one_plus(raw as int) == (base as int) * one_plus(raw as int));
        lemma_floor(x, q as int, (base as int) * one_plus(raw as int), 10_000int);
    }
    if q <= u64::MAX as u128 { Some(q as u64) } else { None }
}

/// The total a stat tooltip implies, `floor(base × (1 + p)) + flat`, or `None`
/// exactly when that exceeds `u64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(r) ==> r == scaled_spec(base as int, raw as int) + flat,
        r is None ==> scaled_spec(base as int, raw as int) + flat > u64::MAX,
))]
#[must_use]
pub fn implied_total(base: u64, raw: i64, flat: u64) -> Option<u64> {
    proof! {
        assert(base * one_plus(raw as int) >= 0) by (nonlinear_arith)
            requires base >= 0, one_plus(raw as int) >= 0;
        assert(scaled_spec(base as int, raw as int) >= 0) by (nonlinear_arith)
            requires base * one_plus(raw as int) >= 0;
    }
    scaled(base, raw)?.checked_add(flat)
}

/// `n` as a `u64`, or `None` if it does not fit.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(r) ==> r == n, r is None ==> n > u64::MAX,
))]
fn narrow(n: u128) -> Option<u64> {
    if n <= u64::MAX as u128 { Some(n as u64) } else { None }
}

/// The displayed damage range, `(min, max)`.
///
/// ```text
/// upper_actual = round(weapon_constant × stat_value × attack / 100)
/// lower_actual = round(upper_actual × mastery)
/// max = floor(upper_actual × (1 + damage) × (1 + final_damage))
/// min = floor(1 + lower_actual × (1 + damage) × (1 + final_damage))
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some((min, max)) ==> {
        let upper = upper_actual(wc_raw as int, stat_value as int, attack as int);
        let lower = lower_actual(upper, mastery_raw as int);
        let shown = one_plus(damage_raw as int) * one_plus(fd_raw as int);
        &&& max == upper * shown / 100_000_000
        &&& min == (lower * shown + 100_000_000) / 100_000_000
    },
))]
#[must_use]
pub fn displayed_range(
    wc_raw: i64,
    mastery_raw: i64,
    stat_value: u64,
    attack: u64,
    damage_raw: i64,
    fd_raw: i64,
) -> Option<(u64, u64)> {
    let wc = percent(wc_raw);
    let sv = Ratio::from_int(stat_value);
    let att = Ratio::from_int(attack);
    let hundredth = fraction(1, 100);
    let b1 = wc.checked_mul(sv)?;
    let b2 = b1.checked_mul(att)?;
    let base = b2.checked_mul(hundredth)?;
    let upper_actual = base.round_half_up();
    proof! {
        let c = clamp0(wc_raw as int);
        lemma_is_mul(b1, wc, sv, c, 10_000, stat_value as int, 1);
        lemma_is_mul(b2, b1, att, c * stat_value, 10_000int, attack as int, 1);
        lemma_is_mul(base, b2, hundredth, c * stat_value * attack, 10_000int, 1, 100);
        lemma_round(base, upper_actual as int, c * stat_value * attack, 1_000_000int);
    }
    let upper_u64 = narrow(upper_actual)?;
    let up = Ratio::from_int(upper_u64);
    let mastery = percent(mastery_raw);
    let l = up.checked_mul(mastery)?;
    let lower_actual = l.round_half_up();
    proof! {
        lemma_is_mul(l, up, mastery, upper_actual as int, 1, clamp0(mastery_raw as int), 10_000);
        lemma_round(l, lower_actual as int, (upper_actual as int) * clamp0(mastery_raw as int), 10_000int);
    }
    let lower_u64 = narrow(lower_actual)?;
    let dmg = one_plus_factor(damage_raw);
    let fd = one_plus_factor(fd_raw);
    let shown = dmg.checked_mul(fd)?;
    let hi = up.checked_mul(shown)?;
    let max = hi.floor();
    let lo = Ratio::from_int(lower_u64);
    let lo_shown = lo.checked_mul(shown)?;
    let one = Ratio::from_int(1);
    let lo_plus = lo_shown.checked_add(one)?;
    let min = lo_plus.floor();
    proof! {
        let s = one_plus(damage_raw as int) * one_plus(fd_raw as int);
        lemma_is_mul(shown, dmg, fd, one_plus(damage_raw as int), 10_000, one_plus(fd_raw as int), 10_000);
        lemma_is_mul(hi, up, shown, upper_actual as int, 1, s, 100_000_000int);
        lemma_floor(hi, max as int, (upper_actual as int) * s, 100_000_000int);
        lemma_is_mul(lo_shown, lo, shown, lower_actual as int, 1, s, 100_000_000int);
        let (xn, xd) = (lo_shown.n(), lo_shown.d());
        let (p, q) = ((lower_actual as int) * s, 100_000_000int);
        assert(lo_plus.n() * q == (p + q) * lo_plus.d()) by (nonlinear_arith)
            requires lo_plus.n() * (xd * 1) == (xn * 1 + 1 * xd) * lo_plus.d(), xn * q == p * xd, xd > 0;
        lemma_floor(lo_plus, min as int, p + q, q);
    }
    Some((narrow(min)?, narrow(max)?))
}

/// Bow-normalised attack: `flat + floor((bow - weapon) × (weapon + star_force) / weapon)`.
///
/// `None` if the result is negative, exceeds `u64`, or an intermediate exceeds
/// `u128`; the last needs a weapon attack above 2^63 and never happens.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(r) ==> r == bow_spec(flat as int, weapon as int, star_force as int, bow as int),
        weapon > 0 && 0 <= bow_spec(flat as int, weapon as int, star_force as int, bow as int) <= u64::MAX
            && (if bow >= weapon { bow - weapon } else { weapon - bow }) * (weapon + star_force) <= u128::MAX
            ==> r is Some,
))]
#[must_use]
pub fn bow_normalised(flat: u64, weapon: u64, star_force: u64, bow: u64) -> Option<u64> {
    if weapon == 0 {
        return Some(flat);
    }
    let span = weapon as u128 + star_force as u128;
    let w = weapon as u128;
    if bow >= weapon {
        let delta = (bow - weapon) as u128;
        let d = delta.checked_mul(span)?;
        let step = d / w;
        proof! {
            assert(((bow - weapon) * (weapon + star_force)) as int / weapon as int == step as int);
        }
        narrow((flat as u128).checked_add(step)?)
    } else {
        let delta = (weapon - bow) as u128;
        let d = delta.checked_mul(span)?;
        // floor(-d / w) is -ceil(d / w).
        proof! {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d as int, w as int);
            if d % w != 0 {
                assert(w >= 2);
                assert((d / w) * 2 <= d) by (nonlinear_arith)
                    requires d == w * (d / w) + d % w, w >= 2, d / w >= 0, d % w >= 0;
            }
        }
        let up = d / w + if d % w == 0 { 0 } else { 1 };
        proof! {
            let (di, wi, ui) = (d as int, w as int, up as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(di, wi);
            assert(-ui * wi <= -di < (-ui + 1) * wi) by (nonlinear_arith)
                requires di == wi * (di / wi) + di % wi, 0 <= di % wi < wi,
                    ui == di / wi + (if di % wi == 0 { 0int } else { 1int });
            lemma_quotient_unique(-ui, -di, wi);
            assert((bow - weapon) * (weapon + star_force) == -di) by (nonlinear_arith)
                requires di == (weapon - bow) * (weapon + star_force);
        }
        if (flat as u128) < up { None } else { narrow(flat as u128 - up) }
    }
}

/// Combat Power:
/// `floor(stat_value / 100 × attack × (1.35 + cd) × (1 + damage) × (1 + fd) / Π(1 + class_fd))`,
/// where `attack` is already `floor(flat × (1 + attack%))`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r matches Some(r) ==> {
        &&& cp_den(class_fd@) > 0
        &&& r == cp_num(stat_value as int, attack as int, cd_raw as int, damage_raw as int, fd_raw as int,
            class_fd@) / cp_den(class_fd@)
    },
))]
#[must_use]
pub fn combat_power(
    stat_value: u64,
    attack: u64,
    cd_raw: i64,
    damage_raw: i64,
    fd_raw: i64,
    class_fd: &[i64],
) -> Option<u64> {
    let class = stack_final_damage(class_fd)?;
    let fd = one_plus_factor(fd_raw);
    let fd_net = fd.checked_div(class)?;
    let sv = fraction(stat_value as i128, 100);
    let att = Ratio::from_int(attack);
    let crit = crit_factor(cd_raw);
    let dmg = one_plus_factor(damage_raw);
    let c1 = sv.checked_mul(att)?;
    let c2 = c1.checked_mul(crit)?;
    let c3 = c2.checked_mul(dmg)?;
    let c4 = c3.checked_mul(fd_net)?;
    let cp = c4.floor();
    proof! {
        let (sp, k) = (stack_plus(class_fd@), whole_pow(class_fd@.len()));
        lemma_whole_pow_pos(class_fd@.len());
        lemma_stack_plus_nonneg(class_fd@);
        // fd_net = fd / class = (fd·k) / (10_000·sp); class has a positive numerator.
        assert(class.n() > 0);
        assert(sp > 0) by (nonlinear_arith) requires class.n() * k == sp * class.d(), class.n() > 0,
            class.d() > 0, k > 0, sp >= 0;
        assert(fd_net.n() * (10_000 * sp) == (one_plus(fd_raw as int) * k) * fd_net.d()) by (nonlinear_arith)
            requires fd_net.n() * (fd.d() * class.n()) == (fd.n() * class.d()) * fd_net.d(),
                fd.n() * 10_000 == one_plus(fd_raw as int) * fd.d(), class.n() * k == sp * class.d(),
                fd.d() > 0, class.d() > 0, class.n() > 0, sp > 0;
        let s = stat_value as int;
        let a = attack as int;
        let cr = clamp0(13_500 + cd_raw as int);
        let dm = one_plus(damage_raw as int);
        lemma_is_mul(c1, sv, att, s, 100, a, 1);
        lemma_is_mul(c2, c1, crit, s * a, 100int, cr, 10_000);
        lemma_is_mul(c3, c2, dmg, s * a * cr, 1_000_000int, dm, 10_000);
        lemma_is_mul(c4, c3, fd_net, s * a * cr * dm, 10_000_000_000int,
            one_plus(fd_raw as int) * k, 10_000 * sp);
        assert(10_000_000_000int * (10_000 * sp) == cp_den(class_fd@));
        assert(cp_den(class_fd@) > 0) by (nonlinear_arith) requires sp > 0, cp_den(class_fd@) == 100 * 10_000 * 10_000 * (10_000 * sp);
        lemma_floor(c4, cp as int,
            cp_num(s, a, cd_raw as int, damage_raw as int, fd_raw as int, class_fd@), cp_den(class_fd@));
    }
    narrow(cp)
}
