//! Worlds (servers) within a region, and what type of world each is.

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

use serde::ser::{Serialize, SerializeStruct, Serializer};

#[cfg(feature = "verus")]
use crate::lookup::tagged;
use crate::lookup::tagged_key;
use crate::names::same;
use crate::names::world::{GROUP, LEN, tag, text};
#[cfg(feature = "verus")]
use crate::names::world::{key, raw, tag_of};
use crate::region::Region;
use crate::text::trim;
#[cfg(feature = "verus")]
use crate::text::trimmed;
#[cfg(feature = "verus")]
use vstd::prelude::*;
#[cfg(feature = "verus")]
use vstd::string::StringSliceAdditionalSpecFns;

/// Which GMS data center hosts a world.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DataCenter {
    /// North America.
    Na,
    /// Europe.
    Eu,
}

#[cfg_attr(feature = "verus", verus_verify)]
impl DataCenter {
    /// The position in declaration order.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r < 2))]
    #[must_use]
    pub const fn index(self) -> usize {
        match self {
            Self::Na => 0,
            Self::Eu => 1,
        }
    }

    /// The data center at position `i`.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r is Some <==> i < 2))]
    #[must_use]
    pub const fn from_index(i: usize) -> Option<Self> {
        match i {
            0 => Some(Self::Na),
            1 => Some(Self::Eu),
            _ => None,
        }
    }

    /// The wire name.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r@ == match self { Self::Na => "na"@, Self::Eu => "eu"@ },
    ))]
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Na => "na",
            Self::Eu => "eu",
        }
    }
}

crate::wire::unit_enum_serde!(DataCenter, 2, ["na", "eu"]);

/// The ruleset a world runs under.
///
/// GMS split its worlds this way in February 2023: the former Reboot worlds
/// became **Heroic** (no trading between players, boosted meso and damage) and
/// every other world became **Interactive**.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum WorldType {
    /// Former Reboot worlds.
    Heroic,
    /// Former regular worlds.
    Interactive,
}

#[cfg_attr(feature = "verus", verus_verify)]
impl WorldType {
    /// The position in declaration order.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r < 2))]
    #[must_use]
    pub const fn index(self) -> usize {
        match self {
            Self::Heroic => 0,
            Self::Interactive => 1,
        }
    }

    /// The world type at position `i`.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r is Some <==> i < 2))]
    #[must_use]
    pub const fn from_index(i: usize) -> Option<Self> {
        match i {
            0 => Some(Self::Heroic),
            1 => Some(Self::Interactive),
            _ => None,
        }
    }

    /// The wire name.
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r@ == match self { Self::Heroic => "heroic"@, Self::Interactive => "interactive"@ },
    ))]
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Heroic => "heroic",
            Self::Interactive => "interactive",
        }
    }
}

crate::wire::unit_enum_serde!(WorldType, 2, ["heroic", "interactive"]);

/// One world (server).
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct World {
    /// Nexon's numeric world ID, as returned in `worldID` by the GMS rankings API.
    pub id: u16,
    /// Stable lowercase key, e.g. `"kronos"`.
    pub key: &'static str,
    /// Display name, e.g. `"Kronos"`.
    pub name: &'static str,
    /// The region the world belongs to.
    pub region: Region,
    /// The data center hosting it.
    pub data_center: DataCenter,
    /// Heroic or Interactive.
    pub world_type: WorldType,
}

/// What serde's derive writes: the fields in order.
impl Serialize for World {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut st = s.serialize_struct("World", 6)?;
        st.serialize_field("id", &self.id)?;
        st.serialize_field("key", self.key)?;
        st.serialize_field("name", self.name)?;
        st.serialize_field("region", &self.region)?;
        st.serialize_field("data_center", &self.data_center)?;
        st.serialize_field("world_type", &self.world_type)?;
        st.end()
    }
}

/// Every catalogued world.
///
/// Source: the world table in Nexon's own rankings bundle
/// (`web.nxfs.nexon.com/maplestory/assets/RankingWorldIcon-*.js`, read
/// 2026-10-23), which lists exactly these six live worlds with their data
/// center. Cross-checked against live `worldID` values from
/// `nexon.com/api/maplestory/no-auth/ranking/v2/{na,eu}`.
///
/// Not yet included: Challengers worlds. The same bundle names IDs 48 and 49
/// "Challengers Interactive" and 52 and 54 "Challengers Heroic", but does not
/// say which data center each is on, and none had rankings when this was
/// written (season 4 is expected in November 2026).
#[allow(clippy::redundant_static_lifetimes, reason = "Verus needs the lifetime spelled out")]
#[cfg_attr(feature = "verus", verus_verify)]
pub static WORLDS: &'static [World] = &[
    World {
        id: 1,
        key: "bera",
        name: "Bera",
        region: Region::Gms,
        data_center: DataCenter::Na,
        world_type: WorldType::Interactive,
    },
    World {
        id: 19,
        key: "scania",
        name: "Scania",
        region: Region::Gms,
        data_center: DataCenter::Na,
        world_type: WorldType::Interactive,
    },
    World {
        id: 45,
        key: "kronos",
        name: "Kronos",
        region: Region::Gms,
        data_center: DataCenter::Na,
        world_type: WorldType::Heroic,
    },
    World {
        id: 70,
        key: "hyperion",
        name: "Hyperion",
        region: Region::Gms,
        data_center: DataCenter::Na,
        world_type: WorldType::Heroic,
    },
    World {
        id: 30,
        key: "luna",
        name: "Luna",
        region: Region::Gms,
        data_center: DataCenter::Eu,
        world_type: WorldType::Interactive,
    },
    World {
        id: 46,
        key: "solis",
        name: "Solis",
        region: Region::Gms,
        data_center: DataCenter::Eu,
        world_type: WorldType::Heroic,
    },
];

// Each world's key, name and region are exactly the texts and tags
// `names::world` proves its lookup over; the build fails otherwise (rerun
// `scripts/name_keys.py`).
// Normal builds run it; under `verus` the ghost code is not const-evaluable.
#[cfg(not(feature = "verus"))]
const _: () = {
    assert!(GROUP == 2 && LEN == 2 * WORLDS.len(), "run scripts/name_keys.py");
    let mut r = 0;
    while r < WORLDS.len() {
        assert!(same(WORLDS[r].key.as_bytes(), text(2 * r)), "run scripts/name_keys.py");
        assert!(same(WORLDS[r].name.as_bytes(), text(2 * r + 1)), "run scripts/name_keys.py");
        assert!(WORLDS[r].region.index() == tag(r) as usize, "run scripts/name_keys.py");
        r += 1;
    }
};

/// Finds a world in `region` by key or display name, ignoring case and
/// surrounding whitespace.
///
/// ```
/// use msapi_core::{Region, WorldType, world};
///
/// let kronos = world::find(Region::Gms, "KRONOS").unwrap();
/// assert_eq!(kronos.id, 45);
/// assert_eq!(kronos.world_type, WorldType::Heroic);
/// assert!(world::find(Region::Kms, "kronos").is_none());
/// ```
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r is Some ==> exists|i: usize| i < LEN
            && #[trigger] key(i) == tagged(region.pos() as u8, trimmed(name.spec_bytes())),
))]
#[must_use]
pub fn find(region: Region, name: &str) -> Option<&'static World> {
    let b = name.as_bytes();
    let (lo, hi) = trim(b);
    #[allow(clippy::cast_possible_truncation, reason = "a region index is below 5")]
    let t = region.index() as u8;
    let k = tagged_key(t, &b[lo..hi]);
    match crate::names::world::find(k.as_slice()) {
        Some(i) if i < WORLDS.len() => Some(&WORLDS[i]),
        _ => None,
    }
}

/// Finds a world by its stable key.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r is Some ==> exists|o: usize| o < LEN / GROUP && #[trigger] raw((GROUP * o) as usize) == key.spec_bytes(),
))]
#[must_use]
pub fn by_key(key: &str) -> Option<&'static World> {
    match key_index(key.as_bytes()) {
        Some(o) if o < WORLDS.len() => Some(&WORLDS[o]),
        _ => None,
    }
}

/// The worlds in one region, in table order.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@.len() <= tagged_below(region.pos() as u8, (LEN / GROUP) as int).len()))]
#[must_use]
pub fn in_region(region: Region) -> Vec<&'static World> {
    #[allow(clippy::cast_possible_truncation, reason = "a region index is below 5")]
    let positions = with_tag(region.index() as u8);
    let mut out = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= positions@.len(),
            out@.len() <= i,
        decreases positions@.len() - i
    ))]
    while i < positions.len() {
        let o = positions[i];
        if o < WORLDS.len() {
            out.push(&WORLDS[o]);
        }
        i += 1;
    }
    out
}

#[cfg(feature = "verus")]
verus! {

/// The worlds below `n` whose region has tag `t`, in table order.
pub open spec fn tagged_below(t: u8, n: int) -> Seq<usize>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else if tag_of((n - 1) as usize) == t {
        tagged_below(t, n - 1).push((n - 1) as usize)
    } else {
        tagged_below(t, n - 1)
    }
}

} // verus!

/// The position in [`WORLDS`] of the first world whose key is exactly `key`
/// (the compile-time check above ties `WORLDS` to these texts).
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some(o) => o < LEN / GROUP && raw((GROUP * o) as usize) == key@
                && forall|p: usize| p < o ==> #[trigger] raw((GROUP * p) as usize) != key@,
            None => forall|p: usize| p < LEN / GROUP ==> #[trigger] raw((GROUP * p) as usize) != key@,
        },
))]
#[must_use]
pub fn key_index(key: &[u8]) -> Option<usize> {
    let mut o: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            o <= LEN / GROUP,
            forall|p: usize| p < o ==> #[trigger] raw((GROUP * p) as usize) != key@,
        decreases LEN / GROUP - o
    ))]
    while o < LEN / GROUP {
        if same(text(GROUP * o), key) {
            return Some(o);
        }
        o += 1;
    }
    None
}

/// The positions in [`WORLDS`] of the worlds whose region has tag `t`, in order.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == tagged_below(t, (LEN / GROUP) as int)))]
#[must_use]
pub fn with_tag(t: u8) -> Vec<usize> {
    let mut out = Vec::new();
    let mut o: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            o <= LEN / GROUP,
            out@ == tagged_below(t, o as int),
        decreases LEN / GROUP - o
    ))]
    while o < LEN / GROUP {
        if tag(o) == t {
            out.push(o);
        }
        o += 1;
    }
    out
}

/// Whether some world's region has tag `t`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == exists|o: usize| o < LEN / GROUP && #[trigger] tag_of(o) == t))]
#[must_use]
pub fn has_tag(t: u8) -> bool {
    let mut o: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            o <= LEN / GROUP,
            forall|p: usize| p < o ==> #[trigger] tag_of(p) != t,
        decreases LEN / GROUP - o
    ))]
    while o < LEN / GROUP {
        if tag(o) == t {
            return true;
        }
        o += 1;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keys_and_ids_are_unique_and_keys_are_lowercase() {
        for (i, a) in WORLDS.iter().enumerate() {
            assert_eq!(a.key, a.key.to_ascii_lowercase());
            for b in &WORLDS[i + 1..] {
                assert_ne!(a.key, b.key);
                assert!(a.id != b.id || a.region != b.region, "{} and {}", a.key, b.key);
            }
        }
    }

    #[test]
    fn every_world_resolves_by_its_own_name() {
        for w in WORLDS {
            assert_eq!(find(w.region, w.name), Some(w));
            assert_eq!(by_key(w.key), Some(w));
        }
    }

    #[test]
    fn serde_matches_the_derive() {
        #[derive(serde::Serialize, serde::Deserialize, Debug)]
        #[serde(rename_all = "lowercase")]
        enum Dc {
            Na,
            Eu,
        }
        #[derive(serde::Serialize, serde::Deserialize, Debug)]
        #[serde(rename_all = "lowercase")]
        enum Wt {
            Heroic,
            Interactive,
        }
        #[derive(serde::Serialize)]
        struct W {
            id: u16,
            key: &'static str,
            name: &'static str,
            region: Region,
            data_center: Dc,
            world_type: Wt,
        }
        for w in WORLDS {
            let d = W {
                id: w.id,
                key: w.key,
                name: w.name,
                region: w.region,
                data_center: if w.data_center == DataCenter::Na { Dc::Na } else { Dc::Eu },
                world_type: if w.world_type == WorldType::Heroic { Wt::Heroic } else { Wt::Interactive },
            };
            assert_eq!(serde_json::to_string(w).unwrap(), serde_json::to_string(&d).unwrap());
        }
        for j in ["\"na\"", "\"eu\"", "\"heroic\"", "\"interactive\"", "\"NA\"", "1", "null"] {
            let a = serde_json::from_str::<DataCenter>(j).map(|v| v.as_str().to_owned()).map_err(|e| e.to_string());
            let b = serde_json::from_str::<Dc>(j)
                .map(|v| serde_json::to_string(&v).unwrap().trim_matches('"').to_owned())
                .map_err(|e| e.to_string());
            assert_eq!(a, b, "{j}");
            let a = serde_json::from_str::<WorldType>(j).map(|v| v.as_str().to_owned()).map_err(|e| e.to_string());
            let b = serde_json::from_str::<Wt>(j)
                .map(|v| serde_json::to_string(&v).unwrap().trim_matches('"').to_owned())
                .map_err(|e| e.to_string());
            assert_eq!(a, b, "{j}");
        }
    }
}
