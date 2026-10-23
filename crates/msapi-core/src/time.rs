//! UTC timestamps with millisecond precision, in RFC 3339 on the wire.
//!
//! This is the small subset of date handling the API needs, written out so
//! the crate does not depend on a date library: civil-date conversion uses
//! Howard Hinnant's `days_from_civil` and `civil_from_days` algorithms.

use std::fmt;
use std::str::FromStr;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Milliseconds since the Unix epoch, always UTC.
///
/// ```
/// use msapi_core::Timestamp;
///
/// let t: Timestamp = "2026-10-23T09:38:00.5+02:00".parse()?;
/// assert_eq!(t.to_string(), "2026-10-23T07:38:00.500Z");
/// # Ok::<(), String>(())
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Timestamp(i64);

const MS_PER_DAY: i64 = 86_400_000;

impl Timestamp {
    /// From milliseconds since the Unix epoch.
    #[must_use]
    pub const fn from_millis(ms: i64) -> Self {
        Self(ms)
    }

    /// Milliseconds since the Unix epoch.
    #[must_use]
    pub const fn millis(self) -> i64 {
        self.0
    }

    /// The current time.
    #[must_use]
    pub fn now() -> Self {
        let ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| i64::try_from(d.as_millis()).unwrap_or(i64::MAX));
        Self(ms)
    }

    /// This time plus `ms` milliseconds, saturating.
    #[must_use]
    pub const fn plus_millis(self, ms: i64) -> Self {
        Self(self.0.saturating_add(ms))
    }
}

/// Days since 1970-01-01 for a proleptic Gregorian date.
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

/// The proleptic Gregorian date for days since 1970-01-01.
fn civil_from_days(z: i64) -> (i64, i64, i64) {
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

fn days_in_month(y: i64, m: i64) -> i64 {
    match m {
        2 if (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

impl fmt::Display for Timestamp {
    #[allow(clippy::many_single_char_names, reason = "y/mo/d/h/s mirror the date fields")]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let days = self.0.div_euclid(MS_PER_DAY);
        let ms_of_day = self.0.rem_euclid(MS_PER_DAY);
        let (y, mo, d) = civil_from_days(days);
        let (h, rest) = (ms_of_day / 3_600_000, ms_of_day % 3_600_000);
        let (mi, rest) = (rest / 60_000, rest % 60_000);
        let (s, ms) = (rest / 1000, rest % 1000);
        write!(f, "{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{ms:03}Z")
    }
}

impl FromStr for Timestamp {
    type Err = String;

    /// Parses `YYYY-MM-DDTHH:MM:SS[.fraction](Z|+HH:MM|-HH:MM)`.
    ///
    /// Fractions beyond milliseconds are truncated. A timestamp without an
    /// offset is rejected: guessing a timezone is how captures end up an hour off.
    #[allow(clippy::many_single_char_names, reason = "y/mo/d/h mirror the date fields")]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let err = || format!("`{s}` is not an RFC 3339 timestamp like 2026-10-23T09:38:00Z");
        let b = s.as_bytes();
        if b.len() < 20
            || b[4] != b'-'
            || b[7] != b'-'
            || !matches!(b[10], b'T' | b't')
            || b[13] != b':'
            || b[16] != b':'
        {
            return Err(err());
        }
        let num = |range: std::ops::Range<usize>| -> Result<i64, String> {
            let part = s.get(range).ok_or_else(err)?;
            if !part.bytes().all(|c| c.is_ascii_digit()) {
                return Err(err());
            }
            part.parse().map_err(|_| err())
        };
        let (y, mo, d) = (num(0..4)?, num(5..7)?, num(8..10)?);
        let (h, mi, sec) = (num(11..13)?, num(14..16)?, num(17..19)?);
        if !(1..=12).contains(&mo) || d < 1 || d > days_in_month(y, mo) || h > 23 || mi > 59 || sec > 59 {
            return Err(err());
        }
        let mut i = 19;
        let mut ms = 0;
        if b[i] == b'.' {
            let start = i + 1;
            let end = start + b[start..].iter().take_while(|c| c.is_ascii_digit()).count();
            if end == start {
                return Err(err());
            }
            let digits = &s[start..end.min(start + 3)];
            ms = digits.parse::<i64>().map_err(|_| err())?
                * 10_i64.pow(3 - u32::try_from(digits.len()).map_err(|_| err())?);
            i = end;
        }
        let offset_minutes = match &s[i..] {
            "Z" | "z" => 0,
            tz if tz.len() == 6 && matches!(tz.as_bytes()[0], b'+' | b'-') && tz.as_bytes()[3] == b':' => {
                let oh = num(i + 1..i + 3)?;
                let om = num(i + 4..i + 6)?;
                if oh > 23 || om > 59 {
                    return Err(err());
                }
                let sign = if tz.starts_with('-') { -1 } else { 1 };
                sign * (oh * 60 + om)
            }
            _ => return Err(err()),
        };
        let days = days_from_civil(y, mo, d);
        let local = days * MS_PER_DAY + ((h * 60 + mi) * 60 + sec) * 1000 + ms;
        Ok(Self(local - offset_minutes * 60_000))
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

    #[test]
    fn known_instants() {
        assert_eq!(Timestamp(0).to_string(), "1970-01-01T00:00:00.000Z");
        assert_eq!(Timestamp(-1).to_string(), "1969-12-31T23:59:59.999Z");
        assert_eq!(Timestamp(951_782_400_000).to_string(), "2000-02-29T00:00:00.000Z");
        assert_eq!("2026-10-23T09:38:00Z".parse::<Timestamp>().unwrap().millis(), 1_792_748_280_000);
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
        ] {
            assert!(bad.parse::<Timestamp>().is_err(), "{bad} should be rejected");
        }
    }
}
