//! Worlds (servers) within a region, and what type of world each is.

use serde::{Deserialize, Serialize};

use std::sync::LazyLock;

use crate::lookup::{Index, tagged_key};
use crate::region::Region;

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
    INDEX.get(&tagged_key(region as u8, name.trim().as_bytes())).map(|i| &WORLDS[i])
}

/// Each world's key and name, tagged with its region → position in
/// [`WORLDS`]. [`Index::build`] refuses a catalogue where one region has two
/// worlds whose keys or names are equal ignoring case.
#[allow(
    clippy::expect_used,
    reason = "the table is constant, so build either always or never succeeds; tests build it"
)]
static INDEX: LazyLock<Index> = LazyLock::new(|| {
    let keys = WORLDS
        .iter()
        .flat_map(|w| [tagged_key(w.region as u8, w.key.as_bytes()), tagged_key(w.region as u8, w.name.as_bytes())])
        .collect();
    let owners = (0..WORLDS.len()).flat_map(|i| [i, i]).collect();
    Index::build(keys, owners).expect("two worlds in one region share a key or name")
});

/// Finds a world by its stable key.
#[must_use]
pub fn by_key(key: &str) -> Option<&'static World> {
    WORLDS.iter().find(|w| w.key == key)
}

/// The worlds in one region.
pub fn in_region(region: Region) -> impl Iterator<Item = &'static World> {
    WORLDS.iter().filter(move |w| w.region == region)
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
