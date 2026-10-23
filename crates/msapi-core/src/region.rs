//! Game regions: the separately operated versions of MapleStory.

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

#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;

use crate::ascii::lowercase;
#[cfg(feature = "verus")]
use crate::ascii::lowered;
#[cfg(feature = "verus")]
use crate::names::region as names_region;
#[cfg(feature = "verus")]
use crate::names::world;

/// A separately operated MapleStory service, each with its own accounts and worlds.
///
/// Names follow Nexon's own abbreviations. Only [`Region::Gms`] has a world
/// catalogue so far; see [`Region::is_supported`].
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

#[cfg(feature = "verus")]
verus! {

impl Region {
    /// The position in [`Region::ALL`], for specs.
    pub open spec fn pos(self) -> int {
        match self {
            Self::Gms => 0,
            Self::Kms => 1,
            Self::Msea => 2,
            Self::Tms => 3,
            Self::Jms => 4,
        }
    }
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl Region {
    /// Every region, in display order.
    pub const ALL: [Self; 5] = [Self::Gms, Self::Kms, Self::Msea, Self::Tms, Self::Jms];

    /// The region's position in [`Region::ALL`], which is also its tag in
    /// the world catalogue.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == self.pos(), r < 5))]
    #[must_use]
    pub const fn index(self) -> usize {
        match self {
            Self::Gms => 0,
            Self::Kms => 1,
            Self::Msea => 2,
            Self::Tms => 3,
            Self::Jms => 4,
        }
    }

    /// The region at position `i` of [`Region::ALL`].
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r is Some <==> i < 5, r matches Some(g) ==> g.pos() == i))]
    #[must_use]
    pub const fn from_index(i: usize) -> Option<Self> {
        match i {
            0 => Some(Self::Gms),
            1 => Some(Self::Kms),
            2 => Some(Self::Msea),
            3 => Some(Self::Tms),
            4 => Some(Self::Jms),
            _ => None,
        }
    }

    /// The wire name, e.g. `"gms"`: the text `names::region::text` holds at
    /// the region's position (the build checks they agree).
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r@ == match self {
                Self::Gms => "gms"@,
                Self::Kms => "kms"@,
                Self::Msea => "msea"@,
                Self::Tms => "tms"@,
                Self::Jms => "jms"@,
            },
    ))]
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
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r@ == match self {
                Self::Gms => "MapleStory Global (NA/EU)"@,
                Self::Kms => "MapleStory Korea"@,
                Self::Msea => "MapleStory SEA"@,
                Self::Tms => "MapleStory Taiwan"@,
                Self::Jms => "MapleStory Japan"@,
            },
    ))]
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
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r == exists|o: usize| o < world::LEN / world::GROUP && #[trigger] world::tag_of(o) == self.pos() as u8
    ))]
    #[must_use]
    pub fn is_supported(self) -> bool {
        #[allow(clippy::cast_possible_truncation, reason = "an index below 5")]
        let t = self.index() as u8;
        crate::world::has_tag(t)
    }

    /// The region named `s`, in any case; otherwise the message the API
    /// answers with.
    ///
    /// # Errors
    ///
    /// `s` names no region.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            match r {
                Ok(g) => exists|i: usize| i < names_region::LEN && #[trigger] names_region::key(i) == lowered(s.spec_bytes())
                    && i == g.pos(),
                Err(m) => (forall|i: usize| i < names_region::LEN ==> #[trigger] names_region::key(i) != lowered(s.spec_bytes()))
                    && m@ == "unknown region `"@ + s@ + "`; expected one of gms, kms, msea, tms, jms"@,
            },
    ))]
    pub fn parse(s: &str) -> Result<Self, String> {
        let q = lowercase(s.as_bytes());
        if let Some(i) = crate::names::region::find(q.as_slice()) {
            if let Some(r) = Self::from_index(i) {
                return Ok(r);
            }
        }
        let mut m = String::new();
        m.push_str("unknown region `");
        m.push_str(s);
        m.push_str("`; expected one of gms, kms, msea, tms, jms");
        proof! {
            assert(Seq::<char>::empty() + "unknown region `"@ =~= "unknown region `"@);
        }
        Err(m)
    }
}

crate::wire::unit_enum_serde!(Region, 5, ["gms", "kms", "msea", "tms", "jms"]);

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
        assert!(Region::ALL[r].index() == r, "run scripts/name_keys.py");
        r += 1;
    }
};

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FromStr for Region {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[test]
    fn every_region_parses_by_name_in_any_case() {
        for r in Region::ALL {
            assert_eq!(r.as_str().parse::<Region>(), Ok(r));
            assert_eq!(r.as_str().to_ascii_uppercase().parse::<Region>(), Ok(r));
        }
        assert!("eu".parse::<Region>().is_err());
        assert_eq!(
            "eu".parse::<Region>(),
            Err("unknown region `eu`; expected one of gms, kms, msea, tms, jms".to_owned())
        );
    }

    #[test]
    fn serde_matches_the_derive() {
        #[derive(Serialize, Deserialize, Debug)]
        #[serde(rename_all = "lowercase")]
        enum Derived {
            Gms,
            Kms,
            Msea,
            Tms,
            Jms,
        }
        let derived = [Derived::Gms, Derived::Kms, Derived::Msea, Derived::Tms, Derived::Jms];
        for (r, d) in Region::ALL.into_iter().zip(derived) {
            assert_eq!(serde_json::to_string(&r).unwrap(), serde_json::to_string(&d).unwrap());
        }
        for j in ["\"gms\"", "\"msea\"", "\"GMS\"", "\"eu\"", "5", "null", "{\"gms\":null}", "{\"x\":1}", "[]", "\"\""]
        {
            let ours = serde_json::from_str::<Region>(j).map(|r| r.as_str().to_owned()).map_err(|e| e.to_string());
            let theirs = serde_json::from_str::<Derived>(j)
                .map(|d| serde_json::to_string(&d).unwrap().trim_matches('"').to_owned())
                .map_err(|e| e.to_string());
            assert_eq!(ours, theirs, "{j}");
        }
    }
}
