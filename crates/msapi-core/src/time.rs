//! UTC timestamps with millisecond precision, in RFC 3339 on the wire.
//!
//! This is the small subset of date handling the API needs, written out so
//! the crate does not depend on a date library. Verus checks it against a
//! calendar written as day counts (`day_number`): `civil_from_days` and
//! `days_from_civil` are inverses on valid dates, [`format_rfc3339`] writes
//! the digits of the date and time (`text`), [`parse_rfc3339`] accepts
//! exactly the byte grammar of `parse_spec`, and parsing a formatted
//! timestamp gives it back.
//!
//! The supported range is `0000-01-01T00:00:00.000Z` to
//! `9999-12-31T23:59:59.999Z`, the years RFC 3339 can write. Formatting
//! saturates to the nearest end outside it, so every timestamp serializes as
//! text a client can parse (`plus_millis` saturates at `i64::MAX`, for one).
//! Parsing rejects text whose instant falls outside it.

#![allow(
    clippy::single_char_add_str,
    clippy::manual_unwrap_or_default,
    clippy::manual_map,
    clippy::single_match,
    clippy::collapsible_if,
    clippy::manual_unwrap_or,
    clippy::single_match_else,
    reason = "Verus checks plain casts, matches and `push_str`; it has no spec for `From` widening, `Option` combinators or `if let` chains"
)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each one here is proven in range"
)]
#![allow(
    clippy::manual_range_contains,
    clippy::manual_clamp,
    reason = "Verus reasons about comparisons, not `RangeInclusive::contains` or `Ord::clamp`"
)]

use std::fmt;
use std::str::FromStr;

use std::time::{SystemTime, UNIX_EPOCH};
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;

use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "verus")]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_mod, lemma_mod_pos_bound,
};
#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Milliseconds since the Unix epoch, always UTC.
///
/// ```
/// use msapi_core::Timestamp;
///
/// let t: Timestamp = "2026-10-23T09:38:00.5+02:00".parse()?;
/// assert_eq!(t.to_string(), "2026-10-23T07:38:00.500Z");
/// # Ok::<(), String>(())
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Timestamp(i64);

#[cfg_attr(feature = "verus", verus_verify)]
const MS_PER_DAY: i64 = 86_400_000;

/// Days from 1970-01-01 to 0000-01-01.
#[cfg_attr(feature = "verus", verus_verify)]
const MIN_DAY: i64 = -719_528;

/// Days from 1970-01-01 to 9999-12-31.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(not(feature = "verus"), allow(dead_code, reason = "only the proofs and tests use it"))]
const MAX_DAY: i64 = 2_932_896;

/// `0000-01-01T00:00:00.000Z`, the earliest timestamp with a text form.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MIN_MS: i64 = -62_167_219_200_000;

/// `9999-12-31T23:59:59.999Z`, the latest timestamp with a text form.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_MS: i64 = 253_402_300_799_999;

#[cfg(feature = "verus")]
verus! {

impl Timestamp {
    /// Milliseconds since the Unix epoch, for specs.
    pub closed spec fn ms(self) -> int {
        self.0 as int
    }
}

/// `t` limited to the range of `i64`.
pub open spec fn saturate_i64(t: int) -> int {
    if t > i64::MAX { i64::MAX as int } else if t < i64::MIN { i64::MIN as int } else { t }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl Timestamp {
    /// From milliseconds since the Unix epoch.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.ms() == ms as int))]
    pub const fn from_millis(ms: i64) -> Self {
        Self(ms)
    }

    /// Milliseconds since the Unix epoch.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.ms()))]
    pub const fn millis(self) -> i64 {
        self.0
    }

    /// This time plus `ms` milliseconds, saturating.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.ms() == saturate_i64(self.ms() + ms)))]
    pub const fn plus_millis(self, ms: i64) -> Self {
        // `i64::saturating_add`, written out so Verus can check it.
        let sum = self.0 as i128 + ms as i128;
        let t = if sum > i64::MAX as i128 {
            i64::MAX
        } else if sum < i64::MIN as i128 {
            i64::MIN
        } else {
            #[allow(clippy::cast_possible_truncation, reason = "in range: the branches above cut off the rest")]
            let t = sum as i64;
            t
        };
        Self(t)
    }
}

impl Timestamp {
    /// The current time: the system clock, which no proof can speak for.
    #[must_use]
    pub fn now() -> Self {
        let ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| i64::try_from(d.as_millis()).unwrap_or(i64::MAX));
        Self(ms)
    }
}

/// A date and time of day, as the text writes them.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DateTime {
    /// 0 to 9999.
    pub year: i64,
    /// 1 to 12.
    pub month: i64,
    /// 1 to the month's length.
    pub day: i64,
    /// 0 to 23.
    pub hour: i64,
    /// 0 to 59.
    pub minute: i64,
    /// 0 to 59.
    pub second: i64,
    /// 0 to 999.
    pub milli: i64,
}

#[cfg(feature = "verus")]
verus! {

/// Whether `y` is a Gregorian leap year.
pub open spec fn leap_year(y: int) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

/// Days in month `m` of year `y`.
pub open spec fn month_len(y: int, m: int) -> int {
    if m == 2 {
        if leap_year(y) { 29 } else { 28 }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

/// A date with a four-digit year.
pub open spec fn valid_date(y: int, m: int, d: int) -> bool {
    0 <= y <= 9999 && 1 <= m <= 12 && 1 <= d <= month_len(y, m)
}

/// Days from 0000-01-01 to the start of year `y >= 0`: 365 a year, plus one
/// for each leap year before `y` (0, 4, 8, …, less the centuries 400 does not
/// divide).
pub open spec fn year_start(y: int) -> int {
    365 * y + (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400
}

/// Days from the start of year `y` to the start of month `m` (1 to 13).
pub open spec fn month_start(y: int, m: int) -> int {
    let before: int = if m == 1 {
        0
    } else if m == 2 {
        31
    } else if m == 3 {
        59
    } else if m == 4 {
        90
    } else if m == 5 {
        120
    } else if m == 6 {
        151
    } else if m == 7 {
        181
    } else if m == 8 {
        212
    } else if m == 9 {
        243
    } else if m == 10 {
        273
    } else if m == 11 {
        304
    } else if m == 12 {
        334
    } else {
        365
    };
    if m > 2 && leap_year(y) { before + 1 } else { before }
}

/// Days from 1970-01-01 to `y-m-d`.
pub open spec fn day_number(y: int, m: int, d: int) -> int {
    year_start(y) + month_start(y, m) + d - 1 - 719_528
}

/// A valid date and time of day.
pub open spec fn dt_valid(t: DateTime) -> bool {
    &&& valid_date(t.year as int, t.month as int, t.day as int)
    &&& 0 <= t.hour <= 23 && 0 <= t.minute <= 59 && 0 <= t.second <= 59 && 0 <= t.milli <= 999
}

/// Milliseconds from the epoch to `t`.
pub open spec fn instant(y: int, m: int, d: int, h: int, mi: int, s: int, ms: int) -> int {
    day_number(y, m, d) * 86_400_000 + ((h * 60 + mi) * 60 + s) * 1000 + ms
}

/// Milliseconds from the epoch to `t`.
pub open spec fn dt_instant(t: DateTime) -> int {
    instant(t.year as int, t.month as int, t.day as int, t.hour as int, t.minute as int, t.second as int, t.milli as int)
}

/// `t`, moved into the supported range.
pub open spec fn clamp(t: int) -> int {
    if t < MIN_MS { MIN_MS as int } else if t > MAX_MS { MAX_MS as int } else { t }
}

/// The ASCII digit for `n` in 0 to 9.
pub open spec fn ascii_digit(n: int) -> u8 {
    (48 + n) as u8
}

/// `t` as `YYYY-MM-DDTHH:MM:SS.mmmZ`, digit by digit.
pub open spec fn text(t: DateTime) -> Seq<u8> {
    let (y, mo, d) = (t.year as int, t.month as int, t.day as int);
    let (h, mi, s, ms) = (t.hour as int, t.minute as int, t.second as int, t.milli as int);
    seq![
        ascii_digit(y / 1000), ascii_digit(y / 100 % 10), ascii_digit(y / 10 % 10), ascii_digit(y % 10), 45u8,
        ascii_digit(mo / 10), ascii_digit(mo % 10), 45u8,
        ascii_digit(d / 10), ascii_digit(d % 10), 84u8,
        ascii_digit(h / 10), ascii_digit(h % 10), 58u8,
        ascii_digit(mi / 10), ascii_digit(mi % 10), 58u8,
        ascii_digit(s / 10), ascii_digit(s % 10), 46u8,
        ascii_digit(ms / 100), ascii_digit(ms / 10 % 10), ascii_digit(ms % 10), 90u8,
    ]
}

/// Whether `c` is an ASCII digit.
pub open spec fn is_digit(c: u8) -> bool {
    48 <= c <= 57
}

/// Whether `s[i..i + n]` are all ASCII digits.
pub open spec fn digits(s: Seq<u8>, i: int, n: int) -> bool {
    forall|k: int| i <= k < i + n ==> is_digit(#[trigger] s[k])
}

/// The value of the two digits at `s[i..i + 2]`.
pub open spec fn num2(s: Seq<u8>, i: int) -> int {
    10 * (s[i] - 48) + (s[i + 1] - 48)
}

/// The value of the four digits at `s[i..i + 4]`.
pub open spec fn num4(s: Seq<u8>, i: int) -> int {
    100 * num2(s, i) + num2(s, i + 2)
}

/// How many ASCII digits `s` has in a row from `i`.
pub open spec fn digit_run(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(s[i]) { 1 + digit_run(s, i + 1) } else { 0 }
}

/// Milliseconds for the `k >= 1` fraction digits at `s[i..]`: the first
/// three, scaled, and the rest dropped.
pub open spec fn fraction_ms(s: Seq<u8>, i: int, k: int) -> int {
    let d0 = s[i] - 48;
    if k == 1 {
        100 * d0
    } else if k == 2 {
        100 * d0 + 10 * (s[i + 1] - 48)
    } else {
        100 * d0 + 10 * (s[i + 1] - 48) + (s[i + 2] - 48)
    }
}

/// The offset east of UTC, in minutes, if `s[i..]` is exactly `Z`, `z`,
/// `+HH:MM` or `-HH:MM` with `HH <= 23` and `MM <= 59`.
pub open spec fn offset_at(s: Seq<u8>, i: int) -> Option<int> {
    if s.len() == i + 1 && (s[i] == 90 || s[i] == 122) {
        Some(0)
    } else if s.len() == i + 6 && (s[i] == 43 || s[i] == 45) && s[i + 3] == 58 && digits(s, i + 1, 2)
        && digits(s, i + 4, 2) && num2(s, i + 1) <= 23 && num2(s, i + 4) <= 59 {
        let minutes = num2(s, i + 1) * 60 + num2(s, i + 4);
        Some(if s[i] == 45 { -minutes } else { minutes })
    } else {
        None
    }
}

/// The instant `s` names: `YYYY-MM-DDTHH:MM:SS[.fraction](Z|+HH:MM|-HH:MM)`
/// (`T` and `Z` either case) for a valid date and time, when that instant is
/// in the supported range.
pub open spec fn parse_spec(s: Seq<u8>) -> Option<int> {
    if !(s.len() >= 20 && digits(s, 0, 4) && s[4] == 45 && digits(s, 5, 2) && s[7] == 45 && digits(s, 8, 2)
        && (s[10] == 84 || s[10] == 116) && digits(s, 11, 2) && s[13] == 58 && digits(s, 14, 2) && s[16] == 58
        && digits(s, 17, 2)) {
        None
    } else {
        let (y, mo, d) = (num4(s, 0), num2(s, 5), num2(s, 8));
        let (h, mi, sec) = (num2(s, 11), num2(s, 14), num2(s, 17));
        let dot = s[19] == 46;
        let k = if dot { digit_run(s, 20) } else { 0 };
        let end = if dot { 20 + k } else { 19 };
        let ms = if dot { fraction_ms(s, 20, k) } else { 0 };
        if !(valid_date(y, mo, d) && h <= 23 && mi <= 59 && sec <= 59) || (dot && k == 0) {
            None
        } else {
            match offset_at(s, end) {
                None => None,
                Some(o) => {
                    let t = instant(y, mo, d, h, mi, sec, ms) - o * 60_000;
                    if MIN_MS <= t <= MAX_MS { Some(t) } else { None }
                },
            }
        }
    }
}

/// `(x + d) / d` and `(x + d - 1) / d` differ by one exactly when `d` divides `x`.
proof fn lemma_ceil_step(x: int, d: int)
    requires 0 <= x, 0 < d,
    ensures (x + d) / d - (x + d - 1) / d == if x % d == 0 { 1int } else { 0int },
{
    let q = x / d;
    let r = x % d;
    lemma_fundamental_div_mod(x, d);
    lemma_mod_pos_bound(x, d);
    assert((q + 1) * d == q * d + d) by (nonlinear_arith);
    assert(x == q * d + r) by (nonlinear_arith) requires x == d * q + r;
    lemma_fundamental_div_mod_converse(x + d, d, q + 1, r);
    if r == 0 {
        lemma_fundamental_div_mod_converse(x + d - 1, d, q, d - 1);
    } else {
        lemma_fundamental_div_mod_converse(x + d - 1, d, q + 1, r - 1);
    }
}

/// A year is 365 days, or 366 in a leap year.
proof fn lemma_year_step(y: int)
    requires 0 <= y,
    ensures year_start(y + 1) == year_start(y) + if leap_year(y) { 366int } else { 365int },
{
    lemma_ceil_step(y, 4);
    lemma_ceil_step(y, 100);
    lemma_ceil_step(y, 400);
    lemma_mod_mod(y, 100, 4);
    lemma_mod_mod(y, 4, 25);
}

/// Years are 365 or 366 days.
proof fn lemma_year_start_bounds(y: int)
    requires 0 <= y,
    ensures 365 * y <= year_start(y) <= 366 * y,
    decreases y,
{
    if y > 0 {
        lemma_year_start_bounds(y - 1);
        lemma_year_step(y - 1);
    }
}

/// Later years start at least 365 days a year later.
proof fn lemma_year_start_mono(a: int, b: int)
    requires 0 <= a <= b,
    ensures year_start(a) + 365 * (b - a) <= year_start(b),
    decreases b - a,
{
    if a < b {
        lemma_year_start_mono(a + 1, b);
        lemma_year_step(a);
    }
}

/// A valid date falls inside its year, and inside the supported days.
proof fn lemma_date_in_year(y: int, m: int, d: int)
    requires valid_date(y, m, d),
    ensures
        year_start(y) <= day_number(y, m, d) + 719_528 < year_start(y + 1),
        MIN_DAY <= day_number(y, m, d) <= MAX_DAY,
{
    lemma_year_step(y);
    lemma_year_start_mono(0, y);
    lemma_year_start_mono(y + 1, 10000);
    assert(year_start(0) == 0) by (compute);
    assert(year_start(10000) == 3_652_425) by (compute);
}

/// Different valid dates have different day numbers, so `civil_from_days`
/// undoes `days_from_civil`.
pub proof fn lemma_day_number_injective(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int)
    requires
        valid_date(y1, m1, d1),
        valid_date(y2, m2, d2),
        day_number(y1, m1, d1) == day_number(y2, m2, d2),
    ensures y1 == y2 && m1 == m2 && d1 == d2,
{
    lemma_date_in_year(y1, m1, d1);
    lemma_date_in_year(y2, m2, d2);
    if y1 < y2 {
        lemma_year_start_mono(y1 + 1, y2);
    } else if y2 < y1 {
        lemma_year_start_mono(y2 + 1, y1);
    }
    assert(y1 == y2);
}

/// The digits of a number below 10,000 give it back.
proof fn lemma_digits4(n: int)
    requires 0 <= n <= 9999,
    ensures
        0 <= n / 1000 <= 9,
        0 <= n / 100 % 10 <= 9,
        0 <= n / 10 % 10 <= 9,
        0 <= n % 10 <= 9,
        0 <= n / 100 <= 99,
        0 <= n / 10 <= 999,
        n % 100 == 10 * (n / 10 % 10) + n % 10,
        n / 100 == 10 * (n / 1000) + n / 100 % 10,
        n == 100 * (n / 100) + n % 100,
        n == 10 * (n / 10) + n % 10,
{
    lemma_fundamental_div_mod(n, 10);
    lemma_fundamental_div_mod(n, 100);
    lemma_fundamental_div_mod(n, 1000);
    lemma_mod_pos_bound(n, 10);
    lemma_mod_pos_bound(n, 100);
    lemma_mod_pos_bound(n, 1000);
    let a = n / 10;
    let b = n / 100;
    lemma_fundamental_div_mod(a, 10);
    lemma_fundamental_div_mod(b, 10);
    lemma_mod_pos_bound(a, 10);
    lemma_mod_pos_bound(b, 10);
    // n / 100 == (n / 10) / 10, and n / 1000 == (n / 100) / 10.
    lemma_fundamental_div_mod_converse(n, 100, a / 10, 10 * (a % 10) + n % 10);
    lemma_fundamental_div_mod_converse(n, 1000, b / 10, 100 * (b % 10) + n % 100);
}

/// Formatting then parsing gives back the instant.
pub proof fn lemma_round_trip(t: DateTime)
    requires dt_valid(t),
    ensures parse_spec(text(t)) == Some(dt_instant(t)),
{
    let s = text(t);
    let (y, mo, d) = (t.year as int, t.month as int, t.day as int);
    let (h, mi, sec, ms) = (t.hour as int, t.minute as int, t.second as int, t.milli as int);
    lemma_digits4(y);
    lemma_digits4(mo);
    lemma_digits4(d);
    lemma_digits4(h);
    lemma_digits4(mi);
    lemma_digits4(sec);
    lemma_digits4(ms);
    lemma_date_in_year(y, mo, d);
    assert(s.len() == 24);
    assert(digits(s, 0, 4));
    assert(digits(s, 5, 2));
    assert(digits(s, 8, 2));
    assert(digits(s, 11, 2));
    assert(digits(s, 14, 2));
    assert(digits(s, 17, 2));
    assert(num4(s, 0) == y);
    assert(num2(s, 5) == mo);
    assert(num2(s, 8) == d);
    assert(num2(s, 11) == h);
    assert(num2(s, 14) == mi);
    assert(num2(s, 17) == sec);
    assert(digit_run(s, 23) == 0);
    assert(digit_run(s, 22) == 1);
    assert(digit_run(s, 21) == 2);
    assert(digit_run(s, 20) == 3);
    assert(fraction_ms(s, 20, 3) == ms);
    assert(offset_at(s, 23) == Some(0int));
}

} // verus!

/// Whether `y >= 0` is a leap year.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= y,
    ensures r == leap_year(y as int)
))]
const fn is_leap(y: i64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

/// Days in month `m` of year `y`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= y, 1 <= m <= 12,
    ensures r == month_len(y as int, m as int)
))]
const fn days_in_month(y: i64, m: i64) -> i64 {
    match m {
        2 if is_leap(y) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/// Days from 0000-01-01 to the start of year `y`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= y <= 10_000,
    ensures r == year_start(y as int)
))]
const fn year_days(y: i64) -> i64 {
    365 * y + (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400
}

/// Days from the start of year `y` to the start of month `m` (1 to 13).
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= y, 1 <= m <= 13,
    ensures r == month_start(y as int, m as int)
))]
const fn month_days(y: i64, m: i64) -> i64 {
    let before = match m {
        1 => 0,
        2 => 31,
        3 => 59,
        4 => 90,
        5 => 120,
        6 => 151,
        7 => 181,
        8 => 212,
        9 => 243,
        10 => 273,
        11 => 304,
        12 => 334,
        _ => 365,
    };
    if m > 2 && is_leap(y) { before + 1 } else { before }
}

/// Days since 1970-01-01 for a proleptic Gregorian date.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires valid_date(y as int, m as int, d as int),
    ensures r == day_number(y as int, m as int, d as int), MIN_DAY <= r <= MAX_DAY
))]
#[must_use]
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    proof! {
        lemma_date_in_year(y as int, m as int, d as int);
    }
    year_days(y) + month_days(y, m) + d - 1 - 719_528
}

/// The proleptic Gregorian date `(year, month, day)` for days since
/// 1970-01-01, from 0000-01-01 to 9999-12-31.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires MIN_DAY <= z <= MAX_DAY,
    ensures valid_date(r.0 as int, r.1 as int, r.2 as int), day_number(r.0 as int, r.1 as int, r.2 as int) == z
))]
#[must_use]
fn civil_from_days(z: i64) -> (i64, i64, i64) {
    // Days since 0000-01-01. No year is longer than 366 days, so the year is
    // at least `n / 366`, and a few steps forward finds it.
    let n = z + 719_528;
    let mut y = n / 366;
    proof! {
        lemma_fundamental_div_mod(n as int, 366);
        lemma_mod_pos_bound(n as int, 366);
        lemma_year_start_bounds(y as int);
        assert(year_start(10000) == 3_652_425) by (compute);
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            0 <= n < year_start(10000),
            year_start(10000) == 3_652_425,
            0 <= y <= 9999,
            year_start(y as int) <= n,
        decreases 9999 - y
    ))]
    while year_days(y + 1) <= n {
        y += 1;
    }
    let doy = n - year_days(y);
    proof! {
        lemma_year_step(y as int);
    }
    let mut m = 1;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            0 <= y <= 9999,
            1 <= m <= 12,
            month_start(y as int, m as int) <= doy < month_start(y as int, 13),
        decreases 12 - m
    ))]
    while m < 12 && month_days(y, m + 1) <= doy {
        m += 1;
    }
    (y, m, doy - month_days(y, m) + 1)
}

/// The ASCII digit for `n`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 0 <= n <= 9,
    ensures r == ascii_digit(n as int)
))]
const fn digit_char(n: i64) -> u8 {
    n as u8 + b'0'
}

/// The date and time `t` milliseconds after the epoch, moved into the
/// supported range first.
#[allow(clippy::many_single_char_names, reason = "h/s mirror the time fields")]
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures dt_valid(r), dt_instant(r) == clamp(t as int)
))]
fn date_time(t: i64) -> DateTime {
    let t = if t < MIN_MS {
        MIN_MS
    } else if t > MAX_MS {
        MAX_MS
    } else {
        t
    };
    let since = t - MIN_MS;
    let days = since / MS_PER_DAY + MIN_DAY;
    let tod = since % MS_PER_DAY;
    let (h, rest) = (tod / 3_600_000, tod % 3_600_000);
    let (mi, rest2) = (rest / 60_000, rest % 60_000);
    let (s, ms) = (rest2 / 1000, rest2 % 1000);
    proof! {
        lemma_fundamental_div_mod(since as int, 86_400_000);
        lemma_mod_pos_bound(since as int, 86_400_000);
        lemma_fundamental_div_mod(tod as int, 3_600_000);
        lemma_mod_pos_bound(tod as int, 3_600_000);
        lemma_fundamental_div_mod(rest as int, 60_000);
        lemma_mod_pos_bound(rest as int, 60_000);
        lemma_fundamental_div_mod(rest2 as int, 1000);
        lemma_mod_pos_bound(rest2 as int, 1000);
    }
    let (y, mo, d) = civil_from_days(days);
    DateTime { year: y, month: mo, day: d, hour: h, minute: mi, second: s, milli: ms }
}

/// `t` as RFC 3339 text, `YYYY-MM-DDTHH:MM:SS.mmmZ`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires dt_valid(t),
    ensures r@ == text(t)
))]
#[allow(clippy::vec_init_then_push, reason = "one push per spec digit keeps the proof direct")]
fn render(t: DateTime) -> Vec<u8> {
    proof! {
        lemma_digits4(t.year as int);
        lemma_digits4(t.month as int);
        lemma_digits4(t.day as int);
        lemma_digits4(t.hour as int);
        lemma_digits4(t.minute as int);
        lemma_digits4(t.second as int);
        lemma_digits4(t.milli as int);
    }
    let mut out = Vec::new();
    out.push(digit_char(t.year / 1000));
    out.push(digit_char(t.year / 100 % 10));
    out.push(digit_char(t.year / 10 % 10));
    out.push(digit_char(t.year % 10));
    out.push(b'-');
    out.push(digit_char(t.month / 10));
    out.push(digit_char(t.month % 10));
    out.push(b'-');
    out.push(digit_char(t.day / 10));
    out.push(digit_char(t.day % 10));
    out.push(b'T');
    out.push(digit_char(t.hour / 10));
    out.push(digit_char(t.hour % 10));
    out.push(b':');
    out.push(digit_char(t.minute / 10));
    out.push(digit_char(t.minute % 10));
    out.push(b':');
    out.push(digit_char(t.second / 10));
    out.push(digit_char(t.second % 10));
    out.push(b'.');
    out.push(digit_char(t.milli / 100));
    out.push(digit_char(t.milli / 10 % 10));
    out.push(digit_char(t.milli % 10));
    out.push(b'Z');
    proof! {
        assert(out@ =~= text(t));
    }
    out
}

/// `t` milliseconds after the epoch as RFC 3339 text in UTC,
/// `YYYY-MM-DDTHH:MM:SS.mmmZ`, saturating to the supported range.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        exists|d: DateTime| #[trigger] text(d) == r@ && dt_valid(d) && dt_instant(d) == clamp(t as int),
        parse_spec(r@) == Some(clamp(t as int)),
))]
#[must_use]
pub fn format_rfc3339(t: i64) -> Vec<u8> {
    let d = date_time(t);
    proof! {
        lemma_round_trip(d);
    }
    render(d)
}

/// The value of the two ASCII digits at `s[i..i + 2]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires i + 2 <= s@.len(),
    ensures match r {
        Some(v) => digits(s@, i as int, 2) && v == num2(s@, i as int),
        None => !digits(s@, i as int, 2),
    }
))]
fn num2_at(s: &[u8], i: usize) -> Option<i64> {
    let (a, b) = (s[i], s[i + 1]);
    if b'0' <= a && a <= b'9' && b'0' <= b && b <= b'9' {
        Some(10 * (a - b'0') as i64 + (b - b'0') as i64)
    } else {
        proof! {
            assert(!is_digit(s@[i as int]) || !is_digit(s@[i + 1]));
        }
        None
    }
}

/// The value of the four ASCII digits at `s[0..4]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires 4 <= s@.len(),
    ensures match r {
        Some(v) => digits(s@, 0, 4) && v == num4(s@, 0),
        None => !digits(s@, 0, 4),
    }
))]
fn num4_at(s: &[u8]) -> Option<i64> {
    let hi = num2_at(s, 0)?;
    let lo = num2_at(s, 2)?;
    Some(100 * hi + lo)
}

/// Parses `YYYY-MM-DDTHH:MM:SS[.fraction](Z|+HH:MM|-HH:MM)` into
/// milliseconds since the epoch: `None` for anything else, for an impossible
/// date or time, and for an instant outside the supported range.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures match r {
        Some(v) => parse_spec(s@) == Some(v as int),
        None => parse_spec(s@) is None,
    }
))]
#[must_use]
#[allow(clippy::many_single_char_names, reason = "y/mo/d/h mirror the date fields")]
pub fn parse_rfc3339(s: &[u8]) -> Option<i64> {
    if s.len() < 20
        || s[4] != b'-'
        || s[7] != b'-'
        || !(s[10] == b'T' || s[10] == b't')
        || s[13] != b':'
        || s[16] != b':'
    {
        return None;
    }
    let y = num4_at(s)?;
    let mo = num2_at(s, 5)?;
    let d = num2_at(s, 8)?;
    let h = num2_at(s, 11)?;
    let mi = num2_at(s, 14)?;
    let sec = num2_at(s, 17)?;
    if !(1 <= mo && mo <= 12) || d < 1 || d > days_in_month(y, mo) || h > 23 || mi > 59 || sec > 59 {
        return None;
    }
    let mut end: usize = 19;
    let mut ms: i64 = 0;
    if s[19] == b'.' {
        let mut j: usize = 20;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant
                20 <= j <= s@.len(),
                digit_run(s@, 20) == (j - 20) + digit_run(s@, j as int),
            decreases s@.len() - j
        ))]
        while j < s.len() && b'0' <= s[j] && s[j] <= b'9' {
            j += 1;
        }
        if j == 20 {
            return None;
        }
        proof! {
            assert(digit_run(s@, j as int) == 0);
            assert(is_digit(s@[20]));
            if j > 21 {
                assert(digit_run(s@, 21) == j - 21);
                assert(is_digit(s@[21]));
            }
            if j > 22 {
                assert(digit_run(s@, 22) == j - 22);
                assert(is_digit(s@[22]));
            }
        }
        let k = j - 20;
        let d0 = (s[20] - b'0') as i64;
        ms = if k == 1 {
            100 * d0
        } else if k == 2 {
            100 * d0 + 10 * (s[21] - b'0') as i64
        } else {
            100 * d0 + 10 * (s[21] - b'0') as i64 + (s[22] - b'0') as i64
        };
        end = j;
    }
    let offset: i64 = if s.len() - end == 1 && (s[end] == b'Z' || s[end] == b'z') {
        0
    } else if s.len() - end == 6 && (s[end] == b'+' || s[end] == b'-') && s[end + 3] == b':' {
        let oh = num2_at(s, end + 1)?;
        let om = num2_at(s, end + 4)?;
        if oh > 23 || om > 59 {
            return None;
        }
        if s[end] == b'-' { -(oh * 60 + om) } else { oh * 60 + om }
    } else {
        return None;
    };
    let t = days_from_civil(y, mo, d) * MS_PER_DAY + ((h * 60 + mi) * 60 + sec) * 1000 + ms - offset * 60_000;
    if t < MIN_MS || t > MAX_MS {
        return None;
    }
    Some(t)
}

#[cfg_attr(feature = "verus", verus_verify)]
impl Timestamp {
    /// The RFC 3339 text the proven [`format_rfc3339`] writes, saturated to
    /// [`MIN_MS`]..=[`MAX_MS`].
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            exists|d: DateTime| r@ == crate::msg::chars(#[trigger] text(d)) && dt_valid(d) && dt_instant(d) == clamp(self.ms()),
    ))]
    #[must_use]
    pub fn to_rfc3339(self) -> String {
        let b = format_rfc3339(self.0);
        crate::msg::text(b.as_slice())
    }

    /// Parses `YYYY-MM-DDTHH:MM:SS[.fraction](Z|+HH:MM|-HH:MM)`.
    ///
    /// Fractions beyond milliseconds are truncated. A timestamp without an
    /// offset is rejected: guessing a timezone is how captures end up an hour off.
    ///
    /// # Errors
    ///
    /// `s` is not such a timestamp; the message shows the expected form.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(t) => parse_spec(s.spec_bytes()) == Some(t.ms()),
                Err(m) => parse_spec(s.spec_bytes()) is None
                    && m@ == "`"@ + s@ + "` is not an RFC 3339 timestamp like 2026-10-23T09:38:00Z"@,
            },
    ))]
    pub fn parse(s: &str) -> Result<Self, String> {
        match parse_rfc3339(s.as_bytes()) {
            Some(v) => Ok(Self(v)),
            None => {
                let mut m = String::new();
                m.push_str("`");
                m.push_str(s);
                m.push_str("` is not an RFC 3339 timestamp like 2026-10-23T09:38:00Z");
                Err(m)
            }
        }
    }
}

impl fmt::Display for Timestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_rfc3339())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FromStr for Timestamp {
    type Err = String;

    /// Parses `YYYY-MM-DDTHH:MM:SS[.fraction](Z|+HH:MM|-HH:MM)`: [`Timestamp::parse`].
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl Serialize for Timestamp {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

impl<'de> Deserialize<'de> for Timestamp {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = <std::borrow::Cow<'de, str>>::deserialize(deserializer)?;
        s.parse().map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Howard Hinnant's `days_from_civil`, the previous implementation.
    fn hinnant_days(y: i64, m: i64, d: i64) -> i64 {
        let y = if m <= 2 { y - 1 } else { y };
        let era = y.div_euclid(400);
        let yoe = y - era * 400;
        let mp = (m + 9) % 12;
        let doy = (153 * mp + 2) / 5 + d - 1;
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
        era * 146_097 + doe - 719_468
    }

    /// Howard Hinnant's `civil_from_days`, the previous implementation.
    fn hinnant_civil(z: i64) -> (i64, i64, i64) {
        let z = z + 719_468;
        let era = z.div_euclid(146_097);
        let doe = z - era * 146_097;
        let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
        let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
        let mp = (5 * doy + 2) / 153;
        let d = doy - (153 * mp + 2) / 5 + 1;
        let m = if mp < 10 { mp + 3 } else { mp - 9 };
        (yoe + era * 400 + i64::from(m <= 2), m, d)
    }

    /// The previous `Display`, for comparing output byte for byte.
    #[allow(clippy::many_single_char_names, reason = "y/mo/d/h/s mirror the date fields")]
    fn hinnant_text(t: i64) -> String {
        let (y, mo, d) = hinnant_civil(t.div_euclid(MS_PER_DAY));
        let ms_of_day = t.rem_euclid(MS_PER_DAY);
        let (h, rest) = (ms_of_day / 3_600_000, ms_of_day % 3_600_000);
        let (mi, rest) = (rest / 60_000, rest % 60_000);
        let (s, ms) = (rest / 1000, rest % 1000);
        format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{ms:03}Z")
    }

    #[test]
    fn range_ends() {
        assert_eq!(MIN_MS, MIN_DAY * MS_PER_DAY);
        assert_eq!(MAX_MS, (MAX_DAY + 1) * MS_PER_DAY - 1);
        assert_eq!(days_from_civil(0, 1, 1), MIN_DAY);
        assert_eq!(days_from_civil(9999, 12, 31), MAX_DAY);
    }

    #[test]
    fn known_instants() {
        assert_eq!(Timestamp(0).to_string(), "1970-01-01T00:00:00.000Z");
        assert_eq!(Timestamp(-1).to_string(), "1969-12-31T23:59:59.999Z");
        assert_eq!(Timestamp(951_782_400_000).to_string(), "2000-02-29T00:00:00.000Z");
        assert_eq!(Timestamp(MIN_MS).to_string(), "0000-01-01T00:00:00.000Z");
        assert_eq!(Timestamp(MAX_MS).to_string(), "9999-12-31T23:59:59.999Z");
        assert_eq!(Timestamp(1_234).to_string(), "1970-01-01T00:00:01.234Z");
        assert_eq!(Timestamp(5).to_string(), "1970-01-01T00:00:00.005Z");
        assert_eq!(Timestamp(50).to_string(), "1970-01-01T00:00:00.050Z");
        assert_eq!("2026-10-23T09:38:00Z".parse::<Timestamp>().unwrap().millis(), 1_792_748_280_000);
        assert_eq!("1970-01-01T00:00:00Z".parse::<Timestamp>().unwrap().millis(), 0);
        assert_eq!("9999-12-31T23:59:59.999Z".parse::<Timestamp>().unwrap().millis(), MAX_MS);
        assert_eq!("0000-01-01T00:00:00Z".parse::<Timestamp>().unwrap().millis(), MIN_MS);
        assert_eq!("2026-10-23T09:38:00.123456789Z".parse::<Timestamp>().unwrap().millis(), 1_792_748_280_123);
        assert_eq!("2026-10-23T09:38:00.12z".parse::<Timestamp>().unwrap().millis(), 1_792_748_280_120);
    }

    #[test]
    fn leap_days() {
        assert_eq!(days_from_civil(2000, 2, 29), 11_016);
        assert_eq!(civil_from_days(11_016), (2000, 2, 29));
        assert_eq!(civil_from_days(days_from_civil(1900, 3, 1) - 1), (1900, 2, 28));
        assert_eq!(civil_from_days(days_from_civil(2024, 3, 1) - 1), (2024, 2, 29));
        assert!("1900-02-29T00:00:00Z".parse::<Timestamp>().is_err());
        assert!("2000-02-29T00:00:00Z".parse::<Timestamp>().is_ok());
        assert_eq!("1900-03-01T00:00:00Z".parse::<Timestamp>().unwrap().to_string(), "1900-03-01T00:00:00.000Z");
    }

    #[test]
    fn matches_hinnant() {
        for z in MIN_DAY..=MAX_DAY {
            let (y, m, d) = civil_from_days(z);
            assert_eq!((y, m, d), hinnant_civil(z));
            assert_eq!(days_from_civil(y, m, d), hinnant_days(y, m, d));
        }
        for day in (MIN_DAY..=MAX_DAY).step_by(97) {
            let t = Timestamp(day * MS_PER_DAY + (day.rem_euclid(1000) * 86_399) % MS_PER_DAY);
            assert_eq!(t.to_string(), hinnant_text(t.0));
        }
    }

    #[test]
    fn saturates_outside_the_range() {
        assert_eq!(Timestamp(i64::MAX).to_string(), "9999-12-31T23:59:59.999Z");
        assert_eq!(Timestamp(i64::MIN).to_string(), "0000-01-01T00:00:00.000Z");
        assert_eq!(Timestamp(MAX_MS + 1).to_string(), "9999-12-31T23:59:59.999Z");
        assert!("9999-12-31T23:59:59.999-00:01".parse::<Timestamp>().is_err());
        assert!("0000-01-01T00:00:00+00:01".parse::<Timestamp>().is_err());
    }

    #[test]
    fn round_trips_every_day_for_six_centuries() {
        for day in (-200_000..20_000).step_by(1) {
            let t = Timestamp(day * MS_PER_DAY + 45_296_789);
            assert_eq!(t.to_string().parse::<Timestamp>().unwrap(), t);
        }
    }

    #[test]
    fn rejects_impossible_and_ambiguous_input() {
        for bad in [
            "2026-02-29T00:00:00Z",
            "2026-13-01T00:00:00Z",
            "2026-10-23T24:00:00Z",
            "2026-10-23T09:38:00",
            "2026-10-23 09:38:00Z",
            "2026-10-23T09:38:00.Z",
            "2026-10-23T09:38:00+0200",
            "2026-1a-23T09:38:00Z",
            "2026-10-23T09:38:00+24:00",
            "2026-10-23T09:38:00Zz",
            "+2026-10-23T09:38:00Z",
        ] {
            assert!(bad.parse::<Timestamp>().is_err(), "{bad} should be rejected");
        }
    }
}
