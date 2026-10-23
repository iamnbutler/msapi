//! Worlds (servers) within a region, and what type of world each is.

use serde::{Deserialize, Serialize};

use crate::lookup::tagged_key;
use crate::names::same;
use crate::names::world::{GROUP, LEN, tag, text};
#[cfg(feature = "verus")]
use crate::names::world::{raw, tag_of};
use crate::region::Region;
#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Which GMS data center hosts a world.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DataCenter {
    /// North America.
    Na,
    /// Europe.
    Eu,
}

/// The ruleset a world runs under.
///
/// GMS split its worlds this way in February 2023: the former Reboot worlds
/// became **Heroic** (no trading between players, boosted meso and damage) and
/// every other world became **Interactive**.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum WorldType {
    /// Former Reboot worlds.
    Heroic,
    /// Former regular worlds.
    Interactive,
}

/// One world (server).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
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
pub static WORLDS: &[World] = &[
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
        assert!(WORLDS[r].region as u8 == tag(r), "run scripts/name_keys.py");
        r += 1;
    }
};

/// Finds a world in `region` by key or display name, ignoring case.
///
/// ```
/// use msapi_core::{Region, WorldType, world};
///
/// let kronos = world::find(Region::Gms, "KRONOS").unwrap();
/// assert_eq!(kronos.id, 45);
/// assert_eq!(kronos.world_type, WorldType::Heroic);
/// assert!(world::find(Region::Kms, "kronos").is_none());
/// ```
#[must_use]
pub fn find(region: Region, name: &str) -> Option<&'static World> {
    crate::names::world::find(&tagged_key(region as u8, name.trim().as_bytes())).and_then(|i| WORLDS.get(i))
}

/// Finds a world by its stable key.
#[must_use]
pub fn by_key(key: &str) -> Option<&'static World> {
    key_index(key.as_bytes()).and_then(|o| WORLDS.get(o))
}

/// The worlds in one region.
pub fn in_region(region: Region) -> impl Iterator<Item = &'static World> {
    with_tag(region as u8).into_iter().filter_map(|o| WORLDS.get(o))
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
}
