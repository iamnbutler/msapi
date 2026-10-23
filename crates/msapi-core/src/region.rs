//! Game regions: the separately operated versions of MapleStory.

use std::fmt;
use std::str::FromStr;
use std::sync::LazyLock;

use serde::{Deserialize, Serialize};

use crate::ascii::lowercase;
use crate::lookup::Index;

/// A separately operated MapleStory service, each with its own accounts and worlds.
///
/// Names follow Nexon's own abbreviations. Only [`Region::Gms`] has a world
/// catalogue so far; see [`Region::is_supported`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Region {
    /// Global MapleStory: the North America and Europe data centers.
    Gms,
    /// Korea.
    Kms,
    /// South-East Asia.
    Msea,
    /// Taiwan.
    Tms,
    /// Japan.
    Jms,
}

impl Region {
    /// Every region, in display order.
    pub const ALL: [Self; 5] = [Self::Gms, Self::Kms, Self::Msea, Self::Tms, Self::Jms];

    /// The wire name, e.g. `"gms"`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Gms => "gms",
            Self::Kms => "kms",
            Self::Msea => "msea",
            Self::Tms => "tms",
            Self::Jms => "jms",
        }
    }

    /// A human-readable name.
    #[must_use]
    pub const fn display_name(self) -> &'static str {
        match self {
            Self::Gms => "MapleStory Global (NA/EU)",
            Self::Kms => "MapleStory Korea",
            Self::Msea => "MapleStory SEA",
            Self::Tms => "MapleStory Taiwan",
            Self::Jms => "MapleStory Japan",
        }
    }

    /// Whether msapi can hold accounts for this region yet.
    ///
    /// A region is supported once its worlds are catalogued in
    /// [`crate::world::WORLDS`], because every character needs a world.
    ///
    /// ```
    /// use msapi_core::Region;
    /// assert!(Region::Gms.is_supported());
    /// assert!(!Region::Kms.is_supported());
    /// ```
    #[must_use]
    pub fn is_supported(self) -> bool {
        crate::world::WORLDS.iter().any(|w| w.region == self)
    }
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Each region's wire name, lowercased → position in [`Region::ALL`].
#[allow(
    clippy::expect_used,
    reason = "the table is constant, so build either always or never succeeds; tests build it"
)]
static INDEX: LazyLock<Index> = LazyLock::new(|| {
    let keys = Region::ALL.iter().map(|r| lowercase(r.as_str().as_bytes())).collect();
    Index::build(keys, (0..Region::ALL.len()).collect()).expect("two regions share a name")
});

impl FromStr for Region {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        INDEX
            .get(&lowercase(s.as_bytes()))
            .map(|i| Self::ALL[i])
            .ok_or_else(|| format!("unknown region `{s}`; expected one of gms, kms, msea, tms, jms"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_region_parses_by_name_in_any_case() {
        for r in Region::ALL {
            assert_eq!(r.as_str().parse::<Region>(), Ok(r));
            assert_eq!(r.as_str().to_ascii_uppercase().parse::<Region>(), Ok(r));
        }
        assert!("eu".parse::<Region>().is_err());
    }
}
