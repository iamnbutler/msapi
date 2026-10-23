//! The class (job) roster.

use serde::ser::{Serialize, SerializeStruct, Serializer};
#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::fixed::{Fixed, Pct};
use crate::units::WeaponMastery;

/// The five class archetypes, plus Xenon's hybrid.
// Verus checks these types and refuses serde's derive on a checked type, so
// their serde impls are written out below, the same in both builds.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum JobType {
    /// Warrior.
    Warrior,
    /// Magician.
    Magician,
    /// Bowman.
    Bowman,
    /// Thief.
    Thief,
    /// Pirate.
    Pirate,
    /// Xenon counts as both thief and pirate.
    ThiefPirate,
}

/// A stat that feeds a class's damage.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MainStat {
    /// STR.
    Str,
    /// DEX.
    Dex,
    /// INT.
    Int,
    /// LUK.
    Luk,
    /// Max HP (Demon Avenger).
    Hp,
}

/// One playable class.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Class {
    /// Stable kebab-case ID, e.g. `"night-walker"`.
    pub id: &'static str,
    /// Display name as GMS spells it, e.g. `"Night Walker"`.
    pub name: &'static str,
    /// Archetype.
    pub job_type: JobType,
    /// Primary stats (counted 4x in the stat multiplier).
    pub primary: &'static [MainStat],
    /// Secondary stats (counted 1x).
    pub secondary: &'static [MainStat],
    /// Whether the class's damage uses Magic ATT rather than ATT.
    pub uses_magic_attack: bool,
    /// The job's weapon multiplier in the damage range formula.
    pub weapon_constant: WeaponConstant,
    /// Weapon Mastery after the job's mastery skills: the minimum of the published range.
    pub mastery: WeaponMastery,
    /// False where no published table covers the class and `mastery` was inferred
    /// from its job type. Mastery only moves the low end of the damage range.
    pub mastery_verified: bool,
}

impl Serialize for JobType {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(match self {
            Self::Warrior => "warrior",
            Self::Magician => "magician",
            Self::Bowman => "bowman",
            Self::Thief => "thief",
            Self::Pirate => "pirate",
            Self::ThiefPirate => "thief-pirate",
        })
    }
}

impl Serialize for MainStat {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(match self {
            Self::Str => "str",
            Self::Dex => "dex",
            Self::Int => "int",
            Self::Luk => "luk",
            Self::Hp => "hp",
        })
    }
}

impl Serialize for Class {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut st = s.serialize_struct("Class", 9)?;
        st.serialize_field("id", self.id)?;
        st.serialize_field("name", self.name)?;
        st.serialize_field("job_type", &self.job_type)?;
        st.serialize_field("primary", self.primary)?;
        st.serialize_field("secondary", self.secondary)?;
        st.serialize_field("uses_magic_attack", &self.uses_magic_attack)?;
        st.serialize_field("weapon_constant", &self.weapon_constant)?;
        st.serialize_field("mastery", &self.mastery)?;
        st.serialize_field("mastery_verified", &self.mastery_verified)?;
        st.end()
    }
}

/// A job's weapon multiplier, to four decimals (Xenon's is 1.3125).
pub type WeaponConstant = Fixed<4>;

/// One table row. Positional so the roster below reads as a table.
#[allow(clippy::too_many_arguments, reason = "a table-row constructor; each argument is one column")]
const fn row(
    id: &'static str,
    name: &'static str,
    job_type: JobType,
    primary: &'static [MainStat],
    secondary: &'static [MainStat],
    uses_magic_attack: bool,
    weapon_constant_ten_thousandths: i64,
    mastery_percent: i64,
    mastery_verified: bool,
) -> Class {
    Class {
        id,
        name,
        job_type,
        primary,
        secondary,
        uses_magic_attack,
        weapon_constant: Fixed::from_raw(weapon_constant_ten_thousandths),
        mastery: WeaponMastery::new(Pct::from_raw(mastery_percent * 100)),
        mastery_verified,
    }
}

/// Every GMS class, as of September 2026.
///
/// Ported from the `maple` tracker's `src/lib/data/classes.ts`, whose sources
/// are the MapleStory Wiki job table (weapon constants), StrategyWiki (main
/// stats, mastery) and the GMS 2026 Legion member table (roster). Ren's 1.30
/// weapon constant was confirmed by a real stat window: see the golden test
/// in `calc`. Mo Xuan's main stats are inferred from its job type.
/// Lethe is KMS-only until it reaches GMS (expected November 2026); Beast
/// Tamer, Jett and Zen were removed from the game.
#[rustfmt::skip] // one class per line, as a table
pub static CLASSES: &[Class] = &[
    row("hero", "Hero", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 14400, 90, true),
    row("paladin", "Paladin", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13400, 90, true),
    row("dark-knight", "Dark Knight", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 14900, 90, true),
    row(
        "arch-mage-fp",
        "Arch Mage (Fire, Poison)",
        JobType::Magician,
        &[MainStat::Int],
        &[MainStat::Luk],
        true,
        12000,
        95,
        true,
    ),
    row(
        "arch-mage-il",
        "Arch Mage (Ice, Lightning)",
        JobType::Magician,
        &[MainStat::Int],
        &[MainStat::Luk],
        true,
        12000,
        95,
        true,
    ),
    row("bishop", "Bishop", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, false),
    row("bow-master", "Bow Master", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13000, 85, true),
    row("marksman", "Marksman", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13500, 85, true),
    row("pathfinder", "Pathfinder", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13000, 85, true),
    row("night-lord", "Night Lord", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex], false, 17500, 85, true),
    row(
        "shadower",
        "Shadower",
        JobType::Thief,
        &[MainStat::Luk],
        &[MainStat::Dex, MainStat::Str],
        false,
        13000,
        90,
        true,
    ),
    row(
        "dual-blade",
        "Dual Blade",
        JobType::Thief,
        &[MainStat::Luk],
        &[MainStat::Dex, MainStat::Str],
        false,
        13000,
        90,
        true,
    ),
    row("buccaneer", "Buccaneer", JobType::Pirate, &[MainStat::Str], &[MainStat::Dex], false, 17000, 90, true),
    row("corsair", "Corsair", JobType::Pirate, &[MainStat::Dex], &[MainStat::Str], false, 15000, 85, true),
    row("cannoneer", "Cannoneer", JobType::Pirate, &[MainStat::Str], &[MainStat::Dex], false, 15000, 85, true),
    row("dawn-warrior", "Dawn Warrior", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13400, 90, true),
    row("mihile", "Mihile", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 12400, 90, true),
    row("blaze-wizard", "Blaze Wizard", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, true),
    row("wind-archer", "Wind Archer", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13000, 85, true),
    row("night-walker", "Night Walker", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex], false, 17500, 85, true),
    row(
        "thunder-breaker",
        "Thunder Breaker",
        JobType::Pirate,
        &[MainStat::Str],
        &[MainStat::Dex],
        false,
        17000,
        90,
        true,
    ),
    row("aran", "Aran", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 14900, 90, true),
    row("evan", "Evan", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, true),
    row("luminous", "Luminous", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, true),
    row("mercedes", "Mercedes", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13000, 85, true),
    row("phantom", "Phantom", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex], false, 13000, 90, true),
    row("shade", "Shade", JobType::Pirate, &[MainStat::Str], &[MainStat::Dex], false, 17000, 90, true),
    row("blaster", "Blaster", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 17000, 90, true),
    row("battle-mage", "Battle Mage", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, true),
    row("wild-hunter", "Wild Hunter", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13500, 85, true),
    row("mechanic", "Mechanic", JobType::Pirate, &[MainStat::Dex], &[MainStat::Str], false, 15000, 85, true),
    row(
        "xenon",
        "Xenon",
        JobType::ThiefPirate,
        &[MainStat::Str, MainStat::Dex, MainStat::Luk],
        &[],
        false,
        13125,
        90,
        true,
    ),
    row("demon-slayer", "Demon Slayer", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 12000, 90, true),
    row("demon-avenger", "Demon Avenger", JobType::Warrior, &[MainStat::Hp], &[MainStat::Str], false, 13000, 90, true),
    row("kaiser", "Kaiser", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13400, 90, true),
    row("kain", "Kain", JobType::Bowman, &[MainStat::Dex], &[MainStat::Str], false, 13000, 85, true),
    row("cadena", "Cadena", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex, MainStat::Str], false, 13000, 90, true),
    row("angelic-buster", "Angelic Buster", JobType::Pirate, &[MainStat::Dex], &[MainStat::Str], false, 17000, 95, true),
    row("zero", "Zero", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13400, 90, false),
    row("kinesis", "Kinesis", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 90, true),
    row("adele", "Adele", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13000, 90, true),
    row("illium", "Illium", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 90, true),
    row("khali", "Khali", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex], false, 13000, 90, false),
    row("ark", "Ark", JobType::Pirate, &[MainStat::Str], &[MainStat::Dex], false, 17000, 90, true),
    row("lara", "Lara", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, false),
    row("hoyoung", "Hoyoung", JobType::Thief, &[MainStat::Luk], &[MainStat::Dex], false, 13000, 90, true),
    row("ren", "Ren", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 13000, 90, false),
    row("hayato", "Hayato", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 12500, 90, false),
    row("kanna", "Kanna", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 13500, 95, true),
    row("lynn", "Lynn", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 13400, 90, false),
    row("mo-xuan", "Mo Xuan", JobType::Pirate, &[MainStat::Str], &[MainStat::Dex], false, 17500, 90, false),
    row("sia-astelle", "Sia Astelle", JobType::Magician, &[MainStat::Int], &[MainStat::Luk], true, 12000, 95, false),
    row("erel-light", "Erel Light", JobType::Warrior, &[MainStat::Str], &[MainStat::Dex], false, 14900, 90, false),
];

// Each class's ID and name are exactly the texts `names::class` proves its
// lookup over; the build fails otherwise (rerun `scripts/name_keys.py`).
// Normal builds run it; under `verus` the ghost code is not const-evaluable.
#[cfg(not(feature = "verus"))]
const _: () = {
    use crate::names::{
        class::{GROUP, LEN, text},
        same,
    };
    assert!(GROUP == 2 && LEN == 2 * CLASSES.len(), "run scripts/name_keys.py");
    let mut r = 0;
    while r < CLASSES.len() {
        assert!(same(CLASSES[r].id.as_bytes(), text(2 * r)), "run scripts/name_keys.py");
        assert!(same(CLASSES[r].name.as_bytes(), text(2 * r + 1)), "run scripts/name_keys.py");
        r += 1;
    }
};

/// Lowercases and keeps only ASCII letters and digits, so `"Night Walker"`,
/// `"night-walker"` and `"nightwalker"` compare equal.
fn fold(s: &str) -> Vec<u8> {
    crate::ascii::fold(s.as_bytes())
}

/// Finds a class by ID or display name, ignoring case, spaces and punctuation.
///
/// ```
/// use msapi_core::class;
///
/// assert_eq!(class::find("Night Walker").unwrap().id, "night-walker");
/// assert_eq!(class::find("night-walker").unwrap().name, "Night Walker");
/// assert_eq!(class::find("Arch Mage (Fire, Poison)").unwrap().id, "arch-mage-fp");
/// assert!(class::find("Beast Tamer").is_none());
/// ```
#[must_use]
pub fn find(name: &str) -> Option<&'static Class> {
    crate::names::class::find(&fold(name)).and_then(|i| CLASSES.get(i))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roster_is_complete_and_unambiguous() {
        assert_eq!(CLASSES.len(), 53);
        for (i, a) in CLASSES.iter().enumerate() {
            assert!(!a.primary.is_empty(), "{} has no primary stat", a.id);
            assert!(
                (Fixed::from_raw(12_000)..=Fixed::from_raw(17_500)).contains(&a.weapon_constant),
                "{} weapon constant {} is outside every published value",
                a.id,
                a.weapon_constant
            );
            for b in &CLASSES[i + 1..] {
                assert_ne!(fold(a.id), fold(b.id));
                assert_ne!(fold(a.name), fold(b.name));
                assert_ne!(fold(a.id), fold(b.name), "{} collides with {}", a.id, b.name);
            }
        }
    }

    #[test]
    fn every_class_resolves_by_id_and_name() {
        for class in CLASSES {
            assert_eq!(find(class.id), Some(class));
            assert_eq!(find(class.name), Some(class));
        }
    }
}
