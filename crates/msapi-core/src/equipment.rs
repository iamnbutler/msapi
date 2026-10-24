//! The equipment window: what a character wears and each item's tooltip.
//!
//! Field names follow the Nexon Open API's `character/item-equipment`, with
//! one addition for GMS: the tooltip there shows a stat as base (white),
//! enhancement (yellow: scrolls and star force together) and bonus (green:
//! flames). Nexon splits enhancement into `item_etc_option` and
//! `item_starforce_option`; GMS never shows that split, so msapi records the
//! sum as [`Item::item_enhancement_option`].
//!
//! These are records of what one item showed, so [`ItemEquipment::check`]
//! checks them at run time and nothing here is proven: the proofs stay on
//! the formulas (see `docs/verification.md`).

use std::fmt;
use std::ops::Add;

use serde::{Deserialize, Serialize};

use crate::stat::{Issue, Severity};
use crate::time::Timestamp;
use crate::units::{
    AttackPower, DamagePct, Defense, Dex, HpPct, IgnoreDefense, Int, Jump, Luk, MagicAttack, MaxHp, MaxMp, MpPct,
    Speed, StatPct, Str,
};

/// The most stars any item can hold.
pub const MAX_STARFORCE: u8 = 30;

/// A slot in the equipment window.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Slot {
    /// Ring, first from the top.
    #[serde(rename = "ring-1")]
    Ring1,
    /// Ring, second.
    #[serde(rename = "ring-2")]
    Ring2,
    /// Ring, third.
    #[serde(rename = "ring-3")]
    Ring3,
    /// Ring, fourth.
    #[serde(rename = "ring-4")]
    Ring4,
    /// Pocket item.
    Pocket,
    /// Pendant, upper.
    #[serde(rename = "pendant-1")]
    Pendant1,
    /// Pendant, lower (needs a slot extension).
    #[serde(rename = "pendant-2")]
    Pendant2,
    /// Belt.
    Belt,
    /// Hat.
    Hat,
    /// Face accessory.
    FaceAccessory,
    /// Eye accessory.
    EyeAccessory,
    /// Earrings.
    Earrings,
    /// Top, or an overall.
    Top,
    /// Bottom.
    Bottom,
    /// Shoes.
    Shoes,
    /// Gloves.
    Gloves,
    /// Cape.
    Cape,
    /// Shoulder.
    Shoulder,
    /// Weapon.
    Weapon,
    /// Secondary weapon.
    Secondary,
    /// Emblem.
    Emblem,
    /// Badge.
    Badge,
    /// Medal.
    Medal,
    /// Mechanical heart.
    Heart,
    /// Android.
    Android,
    /// Familiar manager.
    FamiliarManager,
}

impl Slot {
    /// The wire name, such as `ring-1`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Ring1 => "ring-1",
            Self::Ring2 => "ring-2",
            Self::Ring3 => "ring-3",
            Self::Ring4 => "ring-4",
            Self::Pocket => "pocket",
            Self::Pendant1 => "pendant-1",
            Self::Pendant2 => "pendant-2",
            Self::Belt => "belt",
            Self::Hat => "hat",
            Self::FaceAccessory => "face-accessory",
            Self::EyeAccessory => "eye-accessory",
            Self::Earrings => "earrings",
            Self::Top => "top",
            Self::Bottom => "bottom",
            Self::Shoes => "shoes",
            Self::Gloves => "gloves",
            Self::Cape => "cape",
            Self::Shoulder => "shoulder",
            Self::Weapon => "weapon",
            Self::Secondary => "secondary",
            Self::Emblem => "emblem",
            Self::Badge => "badge",
            Self::Medal => "medal",
            Self::Heart => "heart",
            Self::Android => "android",
            Self::FamiliarManager => "familiar-manager",
        }
    }
}

/// A potential tier, by the colour of its border.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PotentialGrade {
    /// Blue.
    Rare,
    /// Purple.
    Epic,
    /// Gold.
    Unique,
    /// Green.
    Legendary,
}

/// The stats one colour of an item's tooltip adds, or their total.
///
/// Every field is optional: absent means the tooltip did not show it.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct ItemOption {
    /// STR.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub str: Option<Str>,
    /// DEX.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dex: Option<Dex>,
    /// INT.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub int: Option<Int>,
    /// LUK.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub luk: Option<Luk>,
    /// Max HP.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_hp: Option<MaxHp>,
    /// Max MP.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_mp: Option<MaxMp>,
    /// Attack Power.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub attack_power: Option<AttackPower>,
    /// Magic ATT.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub magic_power: Option<MagicAttack>,
    /// Defense.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub armor: Option<Defense>,
    /// Speed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub speed: Option<Speed>,
    /// Jump.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub jump: Option<Jump>,
    /// Boss Damage %.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub boss_damage: Option<DamagePct>,
    /// Enemy DEF Ignored %. Not summed by [`ItemEquipment::check`]: it stacks
    /// multiplicatively.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ignore_monster_armor: Option<IgnoreDefense>,
    /// All Stats %.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub all_stat: Option<StatPct>,
    /// Damage %.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub damage: Option<DamagePct>,
    /// Max HP %.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_hp_rate: Option<HpPct>,
    /// Max MP %.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_mp_rate: Option<MpPct>,
    /// The required level the item has before flames lower it. Base only.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub base_equipment_level: Option<u16>,
    /// How far a flame lowers the required level. Bonus (add) only.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub equipment_level_decrease: Option<u16>,
}

/// One equipped item, as its tooltip reads.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Item {
    /// Where it is worn.
    pub item_equipment_slot: Slot,
    /// The item type the tooltip names, such as `Sword` or `Ring`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item_equipment_part: Option<String>,
    /// The name as the tooltip shows it.
    pub item_name: String,
    /// The item's icon: an asset key, `item/icon/{sha256}.png`, served at
    /// `/assets/{key}`. A key rather than a URL, so the host can change.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item_icon: Option<String>,
    /// The tooltip's description text.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item_description: Option<String>,
    /// The set the item belongs to, as the tooltip names it. An msapi
    /// addition.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item_set_name: Option<String>,

    /// Stars filled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub starforce: Option<u8>,
    /// Stars shown, filled or not (`0` when the item cannot take stars). An
    /// msapi addition.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub starforce_max: Option<u8>,

    /// What the tooltip shows as each stat's total.
    #[serde(default)]
    pub item_total_option: ItemOption,
    /// White: the item's own stats.
    #[serde(default)]
    pub item_base_option: ItemOption,
    /// Yellow: scrolls and star force. An msapi addition.
    #[serde(default)]
    pub item_enhancement_option: ItemOption,
    /// Green: bonus stats (flames).
    #[serde(default)]
    pub item_add_option: ItemOption,
    /// Pink: exceptional enhancement.
    #[serde(default)]
    pub item_exceptional_option: ItemOption,

    /// The potential's tier.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub potential_option_grade: Option<PotentialGrade>,
    /// Potential line 1, as shown.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub potential_option_1: Option<String>,
    /// Potential line 2.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub potential_option_2: Option<String>,
    /// Potential line 3.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub potential_option_3: Option<String>,
    /// The bonus potential's tier.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub additional_potential_option_grade: Option<PotentialGrade>,
    /// Bonus potential line 1, as shown.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub additional_potential_option_1: Option<String>,
    /// Bonus potential line 2.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub additional_potential_option_2: Option<String>,
    /// Bonus potential line 3.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub additional_potential_option_3: Option<String>,

    /// Successful scrolls.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scroll_upgrade: Option<u8>,
    /// Upgrade slots left.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scroll_upgradeable_count: Option<u8>,
    /// Failed slots that can be restored.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scroll_resilience_count: Option<u8>,
    /// Scissors of Karma uses left.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cuttable_count: Option<u8>,
    /// Whether a Golden Hammer was used.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub golden_hammer_flag: Option<bool>,
    /// The soul, on a weapon.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub soul_name: Option<String>,
    /// The soul's stat line.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub soul_option: Option<String>,
    /// The level of a special skill ring, such as 4 for `Lv. 4`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub special_ring_level: Option<u8>,

    /// Anything else the tooltip shows.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub notes: Option<String>,
}

/// The whole equipment window.
#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ItemEquipment {
    /// When the window was read in game. Defaults to when it was recorded.
    #[serde(default)]
    pub captured_at: Option<Timestamp>,
    /// The items worn, one per slot, in any order.
    #[serde(default)]
    pub item_equipment: Vec<Item>,
}

/// Longest text accepted, in characters, for each kind of field.
const NAME_MAX: usize = 100;
const LINE_MAX: usize = 200;
const TEXT_MAX: usize = 2000;

impl ItemEquipment {
    /// Problems with the window: errors are impossible values (two items in
    /// one slot, more stars than the item shows); warnings are tooltips
    /// whose parts do not add up to their total, which usually means a
    /// misread digit.
    #[must_use]
    pub fn check(&self) -> Vec<Issue> {
        let mut out = Vec::new();
        let mut seen = Vec::new();
        for item in &self.item_equipment {
            let slot = item.item_equipment_slot.name();
            if seen.contains(&item.item_equipment_slot) {
                out.push(error("item_equipment_slot", format!("two items are in `{slot}`")));
            }
            seen.push(item.item_equipment_slot);
            item.check(slot, &mut out);
        }
        out
    }
}

impl Item {
    fn check(&self, slot: &str, out: &mut Vec<Issue>) {
        let name = self.item_name.trim();
        if name.is_empty() {
            out.push(error("item_name", format!("`{slot}` has no item name")));
        }
        if let Some(icon) = &self.item_icon
            && !is_icon_key(icon)
        {
            out.push(error(
                "item_icon",
                format!("`{slot}` item_icon must be an asset key like `item/icon/{{sha256}}.png`"),
            ));
        }
        let texts: [(&'static str, Option<&str>, usize); 13] = [
            ("item_name", Some(&self.item_name), NAME_MAX),
            ("item_equipment_part", self.item_equipment_part.as_deref(), NAME_MAX),
            ("item_set_name", self.item_set_name.as_deref(), NAME_MAX),
            ("soul_name", self.soul_name.as_deref(), NAME_MAX),
            ("potential_option_1", self.potential_option_1.as_deref(), LINE_MAX),
            ("potential_option_2", self.potential_option_2.as_deref(), LINE_MAX),
            ("potential_option_3", self.potential_option_3.as_deref(), LINE_MAX),
            ("additional_potential_option_1", self.additional_potential_option_1.as_deref(), LINE_MAX),
            ("additional_potential_option_2", self.additional_potential_option_2.as_deref(), LINE_MAX),
            ("additional_potential_option_3", self.additional_potential_option_3.as_deref(), LINE_MAX),
            ("soul_option", self.soul_option.as_deref(), LINE_MAX),
            ("item_description", self.item_description.as_deref(), TEXT_MAX),
            ("notes", self.notes.as_deref(), TEXT_MAX),
        ];
        for (field, text, max) in texts {
            if text.is_some_and(|t| t.chars().count() > max) {
                out.push(error(field, format!("`{slot}` {field} is longer than {max} characters")));
            }
        }

        if let Some(max) = self.starforce_max
            && max > MAX_STARFORCE
        {
            out.push(error(
                "starforce_max",
                format!("`{slot}` shows {max} stars; no item has more than {MAX_STARFORCE}"),
            ));
        }
        match (self.starforce, self.starforce_max) {
            (Some(n), Some(max)) if n > max => {
                out.push(error("starforce", format!("`{slot}` has {n} stars but shows only {max}")));
            }
            (Some(n), None) if n > MAX_STARFORCE => {
                out.push(error("starforce", format!("`{slot}` has {n} stars; no item has more than {MAX_STARFORCE}")));
            }
            _ => {}
        }

        let lines = [&self.potential_option_1, &self.potential_option_2, &self.potential_option_3];
        if self.potential_option_grade.is_none() && lines.iter().any(|l| l.is_some()) {
            out.push(warning("potential_option_grade", format!("`{slot}` has potential lines but no grade")));
        }
        let lines = [
            &self.additional_potential_option_1,
            &self.additional_potential_option_2,
            &self.additional_potential_option_3,
        ];
        if self.additional_potential_option_grade.is_none() && lines.iter().any(|l| l.is_some()) {
            out.push(warning(
                "additional_potential_option_grade",
                format!("`{slot}` has bonus potential lines but no grade"),
            ));
        }

        self.check_sums(slot, out);
    }

    /// Each total against base + enhancement + bonus + exceptional.
    fn check_sums(&self, slot: &str, out: &mut Vec<Issue>) {
        let parts = [
            &self.item_base_option,
            &self.item_enhancement_option,
            &self.item_add_option,
            &self.item_exceptional_option,
        ];
        let t = &self.item_total_option;
        sum(out, slot, "str", t.str, parts.map(|p| p.str));
        sum(out, slot, "dex", t.dex, parts.map(|p| p.dex));
        sum(out, slot, "int", t.int, parts.map(|p| p.int));
        sum(out, slot, "luk", t.luk, parts.map(|p| p.luk));
        sum(out, slot, "max_hp", t.max_hp, parts.map(|p| p.max_hp));
        sum(out, slot, "max_mp", t.max_mp, parts.map(|p| p.max_mp));
        sum(out, slot, "attack_power", t.attack_power, parts.map(|p| p.attack_power));
        sum(out, slot, "magic_power", t.magic_power, parts.map(|p| p.magic_power));
        sum(out, slot, "armor", t.armor, parts.map(|p| p.armor));
        sum(out, slot, "speed", t.speed, parts.map(|p| p.speed));
        sum(out, slot, "jump", t.jump, parts.map(|p| p.jump));
        sum(out, slot, "boss_damage", t.boss_damage, parts.map(|p| p.boss_damage));
        sum(out, slot, "all_stat", t.all_stat, parts.map(|p| p.all_stat));
        sum(out, slot, "damage", t.damage, parts.map(|p| p.damage));
        sum(out, slot, "max_hp_rate", t.max_hp_rate, parts.map(|p| p.max_hp_rate));
        sum(out, slot, "max_mp_rate", t.max_mp_rate, parts.map(|p| p.max_mp_rate));
    }
}

/// Warns when a stat's recorded parts do not add up to its total, or are
/// recorded without one. A total alone is fine: the tooltip shows no
/// breakdown for an item nobody enhanced.
fn sum<T>(out: &mut Vec<Issue>, slot: &str, field: &'static str, total: Option<T>, parts: [Option<T>; 4])
where
    T: Add<Output = T> + Copy + PartialEq + Default + fmt::Display,
{
    if parts.iter().all(Option::is_none) {
        return;
    }
    let implied = parts.into_iter().flatten().fold(T::default(), |a, b| a + b);
    match total {
        None => out.push(warning(field, format!("`{slot}` {field} has parts but no total"))),
        Some(t) if t != implied => {
            out.push(warning(field, format!("`{slot}` {field} totals {t} but its parts add to {implied}")));
        }
        Some(_) => {}
    }
}

/// Whether `key` names an item icon: `item/icon/`, the image's SHA-256 in
/// lowercase hex, `.png`.
#[must_use]
pub fn is_icon_key(key: &str) -> bool {
    key.strip_prefix("item/icon/")
        .and_then(|k| k.strip_suffix(".png"))
        .is_some_and(|h| h.len() == 64 && h.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))
}

fn error(field: &'static str, message: String) -> Issue {
    Issue { severity: Severity::Error, field, message }
}

fn warning(field: &'static str, message: String) -> Issue {
    Issue { severity: Severity::Warning, field, message }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(items: &serde_json::Value) -> ItemEquipment {
        serde_json::from_value(serde_json::json!({ "item_equipment": items })).unwrap()
    }

    #[test]
    fn a_tooltip_that_adds_up_is_clean() {
        let w = window(&serde_json::json!([{
            "item_equipment_slot": "belt",
            "item_name": "Superior Engraved Gollux Belt",
            "starforce": 18, "starforce_max": 30,
            "item_total_option": { "str": 149, "all_stat": 4, "max_mp": 200 },
            "item_base_option": { "str": 60, "all_stat": 0, "base_equipment_level": 150 },
            "item_enhancement_option": { "str": 73 },
            "item_add_option": { "str": 16, "all_stat": 4 },
            "potential_option_grade": "unique",
            "potential_option_1": "STR: +9%"
        }]));
        assert_eq!(w.check(), []);
        let back: ItemEquipment = serde_json::from_str(&serde_json::to_string(&w).unwrap()).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn misreads_warn_and_impossibilities_fail() {
        let w = window(&serde_json::json!([
            { "item_equipment_slot": "ring-1", "item_name": "A", "starforce": 18, "starforce_max": 17,
              "item_total_option": { "str": 72 }, "item_base_option": { "str": 10 }, "item_enhancement_option": { "str": 61 } },
            { "item_equipment_slot": "ring-1", "item_name": " ", "item_base_option": { "dex": 5 } }
        ]));
        let issues: Vec<_> = w.check().into_iter().map(|i| (i.severity, i.field, i.message)).collect();
        assert_eq!(
            issues,
            [
                (Severity::Error, "starforce", "`ring-1` has 18 stars but shows only 17".to_owned()),
                (Severity::Warning, "str", "`ring-1` str totals 72 but its parts add to 71".to_owned()),
                (Severity::Error, "item_equipment_slot", "two items are in `ring-1`".to_owned()),
                (Severity::Error, "item_name", "`ring-1` has no item name".to_owned()),
                (Severity::Warning, "dex", "`ring-1` dex has parts but no total".to_owned()),
            ]
        );
    }

    #[test]
    fn icons_are_asset_keys() {
        let hash = "0123456789abcdef".repeat(4);
        assert!(is_icon_key(&format!("item/icon/{hash}.png")));
        for bad in [
            format!("/assets/item/icon/{hash}.png"),
            format!("https://example.com/item/icon/{hash}.png"),
            format!("item/icon/{}.png", hash.to_uppercase()),
            format!("item/icon/{hash}.svg"),
            "item/icon/../x.png".to_owned(),
        ] {
            assert!(!is_icon_key(&bad), "{bad}");
        }
    }

    #[test]
    fn slot_names_are_the_wire_names() {
        for slot in ["ring-1", "pendant-2", "face-accessory", "familiar-manager"] {
            let s: Slot = serde_json::from_value(serde_json::json!(slot)).unwrap();
            assert_eq!(s.name(), slot);
            assert_eq!(serde_json::to_value(s).unwrap(), slot);
        }
    }

    #[test]
    fn unknown_fields_and_slots_are_refused() {
        let bad = serde_json::json!({ "item_equipment": [{ "item_equipment_slot": "ring-5", "item_name": "A" }] });
        assert!(serde_json::from_value::<ItemEquipment>(bad).is_err());
        let bad =
            serde_json::json!({ "item_equipment": [{ "item_equipment_slot": "hat", "item_name": "A", "stars": 1 }] });
        assert!(serde_json::from_value::<ItemEquipment>(bad).is_err());
    }
}
