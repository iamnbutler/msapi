//! Game regions: the separately operated versions of MapleStory.

use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

use crate::ascii::lowercase;

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

    /// The wire name, e.g. `"gms"`: the proven text `names::region::text`
    /// at the region's position (ASCII, so the conversion cannot fail).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match std::str::from_utf8(crate::names::region::text(self as usize)) {
            Ok(s) => s,
            Err(_) => "",
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
        crate::world::has_tag(self as u8)
    }
}

// Each region's wire name is exactly the text `names::region` proves its
// lookup over, and its tag is its position; the build fails otherwise
// (rerun `scripts/name_keys.py`).
// Normal builds run it; under `verus` the ghost code is not const-evaluable.
#[cfg(not(feature = "verus"))]
const _: () = {
    use crate::names::{
        region::{GROUP, LEN, text},
        same,
    };
    assert!(GROUP == 1 && LEN == Region::ALL.len(), "run scripts/name_keys.py");
    let mut r = 0;
    while r < Region::ALL.len() {
        assert!(same(Region::ALL[r].as_str().as_bytes(), text(r)), "run scripts/name_keys.py");
        assert!(Region::ALL[r] as usize == r, "run scripts/name_keys.py");
        r += 1;
    }
};

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for Region {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        crate::names::region::find(&lowercase(s.as_bytes()))
            .and_then(|i| Self::ALL.get(i).copied())
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
