//! The Character Info stat window.

use serde::{Deserialize, Serialize};

#[cfg(feature = "verus")]
use vstd::prelude::*;

use crate::fixed::Pct;
use crate::rules;
use crate::time::Timestamp;
use crate::units::{
    AbilityPoints, AbnormalStatusDamage, AdditionalExp, ArcanePower, AttackPower, BuffDuration, CombatPower,
    CooldownReductionPct, CooldownSeconds, CooldownSkip, CritDamage, CritRate, DamagePct, Defense, Dex, FinalDamage,
    IgnoreDefense, IgnoreElementalResistance, Int, ItemDropRate, Jump, Luk, MagicAttack, MaxHp, MaxMp, MesosObtained,
    Percent, SacredPower, Scalable, Speed, Stance, StarForce, StatAttack, StatusResistance, Str, SummonDuration,
    WeaponMastery,
};

/// A stat as its hover tooltip breaks it down.
///
/// `total = floor(base × (1 + percent / 100)) + flat`
///
/// - `base`: the pool percentages apply to (AP, equipment, flames, scrolls, stars)
/// - `percent`: the summed percentage, in the stat's own percent unit
/// - `flat`: the "% not applied" pool (hyper stats, symbols, Legion, Inner Ability)
///
/// The type parameter ties all three to one stat: a `StatBreakdown<Str>` takes
/// a [`crate::units::StatPct`], and a `StatBreakdown<AttackPower>` takes an
/// [`crate::units::AttackPct`].
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(
    deny_unknown_fields,
    bound(
        serialize = "T: Serialize, T::Percent: Serialize",
        deserialize = "T: Deserialize<'de>, T::Percent: Deserialize<'de>"
    )
)]
pub struct StatBreakdown<T: Scalable> {
    /// The pool percentages apply to.
    pub base: T,
    /// The summed percentage. `None` means not captured.
    #[serde(default)]
    pub percent: Option<T::Percent>,
    /// The pool percentages do not apply to. `None` means not captured.
    #[serde(default)]
    pub flat: Option<T>,
}

impl<T: Scalable> StatBreakdown<T> {
    /// The total the tooltip implies, treating uncaptured parts as zero.
    ///
    /// Returns `None` only if the arithmetic overflows.
    ///
    /// ```
    /// use msapi_core::StatBreakdown;
    /// use msapi_core::units::{Luk, StatPct};
    ///
    /// let luk = StatBreakdown { base: Luk::new(5_000), percent: Some("300".parse::<StatPct>()?), flat: Some(Luk::new(18_120)) };
    /// assert_eq!(luk.implied_total(), Some(Luk::new(38_120)));
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    pub fn implied_total(&self) -> Option<T> {
        breakdown_total(self.base, self.percent, self.flat)
    }
}

/// `floor(base × (1 + percent / 100)) + flat`, with an uncaptured percent or
/// flat part counted as zero; `None` exactly when the total exceeds `u64`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(t) ==> t.count() == crate::formula::scaled_spec(base.count(), percent_raw(percent))
            + flat_count(flat),
        r is None ==> crate::formula::scaled_spec(base.count(), percent_raw(percent)) + flat_count(flat) > u64::MAX,
))]
#[must_use]
#[allow(clippy::manual_map)] // Verus checks the explicit match, not a closure.
pub fn breakdown_total<T: Scalable>(base: T, percent: Option<T::Percent>, flat: Option<T>) -> Option<T> {
    let raw = match percent {
        Some(p) => p.pct().raw(),
        None => 0,
    };
    let flat_n = match flat {
        Some(f) => f.get(),
        None => 0,
    };
    match crate::formula::implied_total(base.get(), raw, flat_n) {
        Some(n) => Some(T::of_count(n)),
        None => None,
    }
}

#[cfg(feature = "verus")]
verus! {

/// A captured percentage in hundredths, or 0.
pub open spec fn percent_raw<P: Percent>(p: Option<P>) -> int {
    match p {
        Some(p) => p.pct_raw(),
        None => 0,
    }
}

/// A captured flat part, or 0.
pub open spec fn flat_count<T: crate::units::Count>(t: Option<T>) -> int {
    match t {
        Some(t) => t.count(),
        None => 0,
    }
}

} // verus!

/// Tooltip breakdowns for the stats that have one.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct StatBreakdowns {
    /// STR tooltip.
    pub str: Option<StatBreakdown<Str>>,
    /// DEX tooltip.
    pub dex: Option<StatBreakdown<Dex>>,
    /// INT tooltip.
    pub int: Option<StatBreakdown<Int>>,
    /// LUK tooltip.
    pub luk: Option<StatBreakdown<Luk>>,
    /// Max HP tooltip (Demon Avenger's main stat).
    pub hp: Option<StatBreakdown<MaxHp>>,
    /// Attack Power tooltip.
    pub attack_power: Option<StatBreakdown<AttackPower>>,
    /// Magic Attack tooltip.
    pub magic_attack: Option<StatBreakdown<MagicAttack>>,
}

/// Attack Speed stage as the window shows it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct AttackSpeed(pub u8);

/// Everything the Character Info window shows, as displayed.
///
/// Every field is optional and `None` means *not captured*, never zero. A
/// client can record a window over several screenshots and merge them in.
///
/// Names follow the in-game labels in snake case, and every field has its own
/// unit type from [`crate::units`]. Field order follows the window.
#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct StatWindow {
    /// When the window was read in game. Defaults to when it was recorded.
    pub captured_at: Option<Timestamp>,

    /// Combat Power.
    pub combat_power: Option<CombatPower>,
    /// Lower end of the displayed damage range ("stat attack").
    pub stat_attack_min: Option<StatAttack>,
    /// Upper end of the displayed damage range.
    pub stat_attack_max: Option<StatAttack>,

    /// Max HP.
    pub hp: Option<MaxHp>,
    /// Max MP.
    pub mp: Option<MaxMp>,
    /// Total STR.
    pub str: Option<Str>,
    /// Total DEX.
    pub dex: Option<Dex>,
    /// Total INT.
    pub int: Option<Int>,
    /// Total LUK.
    pub luk: Option<Luk>,

    /// Damage %.
    pub damage: Option<DamagePct>,
    /// Boss Damage %. Same additive pool as Damage %.
    pub boss_damage: Option<DamagePct>,
    /// Normal (non-boss) Monster Damage %. Same additive pool as Damage %.
    pub normal_damage: Option<DamagePct>,
    /// Final Damage %.
    pub final_damage: Option<FinalDamage>,
    /// Ignore Enemy Defense %. Always below 100.
    pub ignore_defense: Option<IgnoreDefense>,
    /// Ignore Elemental Resistance %.
    pub ignore_elemental_resistance: Option<IgnoreElementalResistance>,
    /// Critical Rate %.
    pub critical_rate: Option<CritRate>,
    /// Critical Damage %.
    pub critical_damage: Option<CritDamage>,
    /// Additional damage to enemies with an abnormal status, %.
    pub abnormal_status_damage: Option<AbnormalStatusDamage>,
    /// Attack Power (ATT).
    pub attack_power: Option<AttackPower>,
    /// Magic Attack (MATT).
    pub magic_attack: Option<MagicAttack>,

    /// Buff Duration %.
    pub buff_duration: Option<BuffDuration>,
    /// Cooldown reduction in seconds.
    pub cooldown_reduction_seconds: Option<CooldownSeconds>,
    /// Cooldown reduction %.
    pub cooldown_reduction_percent: Option<CooldownReductionPct>,
    /// Chance to skip a cooldown, %.
    pub cooldown_skip: Option<CooldownSkip>,
    /// Summon Duration %.
    pub summon_duration: Option<SummonDuration>,
    /// Attack Speed stage.
    pub attack_speed: Option<AttackSpeed>,
    /// Weapon Mastery %.
    pub weapon_mastery: Option<WeaponMastery>,

    /// Star Force.
    pub star_force: Option<StarForce>,
    /// Arcane Power.
    pub arcane_power: Option<ArcanePower>,
    /// Sacred Power (Authentic Force).
    pub sacred_power: Option<SacredPower>,

    /// Item Drop Rate %.
    pub item_drop_rate: Option<ItemDropRate>,
    /// Mesos Obtained %.
    pub mesos_obtained: Option<MesosObtained>,
    /// Additional EXP Obtained %.
    pub additional_exp: Option<AdditionalExp>,

    /// Status Resistance.
    pub status_resistance: Option<StatusResistance>,
    /// Knockback resistance (Stance) %.
    pub stance: Option<Stance>,
    /// Defense.
    pub defense: Option<Defense>,
    /// Speed %.
    pub speed: Option<Speed>,
    /// Jump %.
    pub jump: Option<Jump>,

    /// Unspent AP.
    pub remain_ap: Option<AbilityPoints>,
    /// Hover-tooltip breakdowns, where captured.
    pub breakdowns: Option<StatBreakdowns>,
}

/// How serious an [`Issue`] is.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// The value is impossible; the write is refused.
    Error,
    /// The value is suspicious (usually a misread); the write is kept.
    Warning,
}

/// A problem found by [`StatWindow::check`].
#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct Issue {
    /// Error or warning.
    pub severity: Severity,
    /// The field it concerns, e.g. `"ignore_defense"`.
    pub field: &'static str,
    /// What is wrong, phrased for whoever is reading the screen.
    pub message: String,
}

/// Compares one tooltip with the total it should produce.
fn check_breakdown<T: Scalable + PartialEq + std::fmt::Display>(
    issues: &mut Vec<Issue>,
    field: &'static str,
    breakdown: Option<StatBreakdown<T>>,
    total: Option<T>,
) {
    let (Some(breakdown), Some(total)) = (breakdown, total) else { return };
    match breakdown.implied_total() {
        Some(implied) if implied == total => {}
        Some(implied) => issues.push(Issue {
            severity: Severity::Warning,
            field,
            message: format!(
                "tooltip implies {implied} (floor(base × (1 + percent/100)) + flat) but the total reads {total}; one of them is probably misread"
            ),
        }),
        None => issues.push(Issue {
            severity: Severity::Error,
            field,
            message: "tooltip values are too large to combine".into(),
        }),
    }
}

impl StatWindow {
    /// Checks the window for impossible and suspicious values.
    ///
    /// ```
    /// use msapi_core::{Severity, StatWindow};
    ///
    /// let window = StatWindow { ignore_defense: Some("100".parse()?), ..StatWindow::default() };
    /// let issues = window.check();
    /// assert_eq!(issues[0].field, "ignore_defense");
    /// assert_eq!(issues[0].severity, Severity::Error);
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    pub fn check(&self) -> Vec<Issue> {
        let mut issues = Vec::new();
        let mut error = |field, message: String| issues.push(Issue { severity: Severity::Error, field, message });
        if let Some(ied) = self.ignore_defense
            && !rules::ignore_defense_ok(ied.pct().raw())
        {
            error("ignore_defense", format!("Ignore Enemy Defense is always below 100%, got {ied}"));
        }
        if let Some(cdr) = self.cooldown_reduction_percent
            && !rules::cooldown_reduction_ok(cdr.pct().raw())
        {
            error("cooldown_reduction_percent", format!("cooldown reduction cannot exceed 100%, got {cdr}"));
        }
        if let (Some(min), Some(max)) = (self.stat_attack_min, self.stat_attack_max)
            && !rules::range_ok(min.get(), max.get())
        {
            error("stat_attack_min", format!("damage range minimum {min} is above the maximum {max}"));
        }
        for (field, value) in self.percentages() {
            if let Some(v) = value
                && !rules::percentage_ok(v.raw())
            {
                error(field, format!("{field} cannot be negative, got {v}"));
            }
        }

        if let Some(b) = &self.breakdowns {
            check_breakdown(&mut issues, "str", b.str, self.str);
            check_breakdown(&mut issues, "dex", b.dex, self.dex);
            check_breakdown(&mut issues, "int", b.int, self.int);
            check_breakdown(&mut issues, "luk", b.luk, self.luk);
            check_breakdown(&mut issues, "hp", b.hp, self.hp);
            check_breakdown(&mut issues, "attack_power", b.attack_power, self.attack_power);
            check_breakdown(&mut issues, "magic_attack", b.magic_attack, self.magic_attack);
        }
        issues
    }

    /// Every percentage field that can never be negative, by name.
    fn percentages(&self) -> [(&'static str, Option<Pct>); 19] {
        [
            ("damage", self.damage.map(Percent::pct)),
            ("boss_damage", self.boss_damage.map(Percent::pct)),
            ("normal_damage", self.normal_damage.map(Percent::pct)),
            ("final_damage", self.final_damage.map(Percent::pct)),
            ("ignore_defense", self.ignore_defense.map(Percent::pct)),
            ("ignore_elemental_resistance", self.ignore_elemental_resistance.map(Percent::pct)),
            ("critical_rate", self.critical_rate.map(Percent::pct)),
            ("critical_damage", self.critical_damage.map(Percent::pct)),
            ("abnormal_status_damage", self.abnormal_status_damage.map(Percent::pct)),
            ("buff_duration", self.buff_duration.map(Percent::pct)),
            ("cooldown_reduction_percent", self.cooldown_reduction_percent.map(Percent::pct)),
            ("cooldown_skip", self.cooldown_skip.map(Percent::pct)),
            ("summon_duration", self.summon_duration.map(Percent::pct)),
            ("weapon_mastery", self.weapon_mastery.map(Percent::pct)),
            ("item_drop_rate", self.item_drop_rate.map(Percent::pct)),
            ("mesos_obtained", self.mesos_obtained.map(Percent::pct)),
            ("additional_exp", self.additional_exp.map(Percent::pct)),
            ("stance", self.stance.map(Percent::pct)),
            ("speed", self.speed.map(Percent::pct)),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::units::StatPct;

    #[test]
    fn absent_fields_serialize_as_null_not_zero() {
        let json = serde_json::to_value(StatWindow::default()).unwrap();
        assert!(json["boss_damage"].is_null());
        assert!(json["combat_power"].is_null());
    }

    #[test]
    fn unknown_fields_are_rejected_with_the_field_name() {
        let err = serde_json::from_str::<StatWindow>(r#"{"boss_dmg": 300}"#).unwrap_err();
        assert!(err.to_string().contains("boss_dmg"), "{err}");
    }

    #[test]
    fn breakdown_mismatch_is_a_warning() {
        let window = StatWindow {
            luk: Some(Luk::new(38_000)),
            breakdowns: Some(StatBreakdowns {
                luk: Some(StatBreakdown {
                    base: Luk::new(5_000),
                    percent: Some("300".parse::<StatPct>().unwrap()),
                    flat: Some(Luk::new(18_120)),
                }),
                ..StatBreakdowns::default()
            }),
            ..StatWindow::default()
        };
        let issues = window.check();
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].severity, Severity::Warning);
        assert_eq!(issues[0].field, "luk");
    }

    #[test]
    fn breakdown_floors_like_the_game() {
        // 1234 × 1.15 = 1419.1 → 1419
        let b = StatBreakdown::<Str> { base: Str::new(1234), percent: Some("15".parse().unwrap()), flat: None };
        assert_eq!(b.implied_total(), Some(Str::new(1419)));
    }

    #[test]
    fn a_consistent_window_has_no_issues() {
        let window: StatWindow = serde_json::from_str(
            r#"{
                "captured_at": "2026-10-23T09:00:00Z",
                "combat_power": 123456789,
                "stat_attack_min": 10, "stat_attack_max": 20,
                "luk": 23120, "boss_damage": 380, "ignore_defense": 93.14,
                "breakdowns": { "luk": { "base": 1000, "percent": 400, "flat": 18120 } }
            }"#,
        )
        .unwrap();
        assert_eq!(window.check(), vec![]);
    }
}
