//! Formulas over typed units: the stat multiplier, the displayed damage range
//! and Combat Power.
//!
//! Everything is computed in exact fractions ([`Ratio`]) and floored or rounded
//! only where the source formula does. Each function says where its formula
//! comes from; the tests at the bottom check them against numbers the game
//! itself displayed.

use std::fmt;

use crate::class::{Class, MainStat, WeaponConstant};
use crate::formula;
use crate::units::{
    AttackPct, AttackPower, CombatPower, Count, CritDamage, DamagePct, Dex, FinalDamage, Int, Luk, MagicAttack,
    MagicAttackPct, Percent, StatAttack, Str, WeaponMastery,
};

/// Why a formula could not produce a value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CalcError {
    /// An intermediate value overflowed.
    Overflow,
    /// The formula does not cover this case yet.
    Unsupported(&'static str),
}

impl fmt::Display for CalcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow => f.write_str("an intermediate value overflowed"),
            Self::Unsupported(what) => write!(f, "not supported yet: {what}"),
        }
    }
}

impl std::error::Error for CalcError {}

/// Turns a checked-arithmetic `None` into [`CalcError::Overflow`].
trait OrOverflow<T> {
    fn or_overflow(self) -> Result<T, CalcError>;
}

impl<T> OrOverflow<T> for Option<T> {
    fn or_overflow(self) -> Result<T, CalcError> {
        self.ok_or(CalcError::Overflow)
    }
}

/// The four main-stat totals.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct MainStats {
    /// Total STR.
    pub str: Str,
    /// Total DEX.
    pub dex: Dex,
    /// Total INT.
    pub int: Int,
    /// Total LUK.
    pub luk: Luk,
}

impl MainStats {
    fn get(&self, stat: MainStat) -> Option<u64> {
        match stat {
            MainStat::Str => Some(self.str.get()),
            MainStat::Dex => Some(self.dex.get()),
            MainStat::Int => Some(self.int.get()),
            MainStat::Luk => Some(self.luk.get()),
            MainStat::Hp => None,
        }
    }
}

/// The stat multiplier: `4 × primary + secondary`.
///
/// This is the only place different stats are combined, which is why it is its
/// own unit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct StatValue(u64);

impl StatValue {
    /// The stat value.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }

    /// The stat value for `class` from its main-stat totals.
    ///
    /// Source: StrategyWiki §Stat Value, via `maple`'s `docs/research/formulas.md`
    /// §1.2. Xenon is `4 × (STR + DEX + LUK)`, which the roster encodes as three
    /// primaries and no secondary. Demon Avenger's HP formula needs the
    /// character's pure HP and is not supported yet.
    ///
    /// ```
    /// use msapi_core::calc::{MainStats, StatValue};
    /// use msapi_core::class;
    /// use msapi_core::units::{Dex, Str};
    ///
    /// let stats = MainStats { str: Str::new(29_216), dex: Dex::new(3_882), ..MainStats::default() };
    /// let ren = class::find("ren").unwrap();
    /// assert_eq!(StatValue::for_class(ren, &stats)?.get(), 4 * 29_216 + 3_882);
    /// # Ok::<(), msapi_core::calc::CalcError>(())
    /// ```
    pub fn for_class(class: &Class, stats: &MainStats) -> Result<Self, CalcError> {
        let values = |list: &[MainStat]| -> Result<Vec<u64>, CalcError> {
            list.iter().map(|&s| stats.get(s).ok_or(CalcError::Unsupported("Demon Avenger's HP stat value"))).collect()
        };
        formula::stat_value(&values(class.primary)?, &values(class.secondary)?).map(Self).or_overflow()
    }
}

/// A job's attack, keeping physical and magic attack apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum JobAttack {
    /// Total Attack Power, for non-magicians.
    Physical(AttackPower),
    /// Total Magic Attack, for magicians.
    Magic(MagicAttack),
}

impl JobAttack {
    /// Picks the attack `class` uses from a stat window's two totals.
    #[must_use]
    pub fn for_class(class: &Class, attack: AttackPower, magic: MagicAttack) -> Self {
        if class.uses_magic_attack { Self::Magic(magic) } else { Self::Physical(attack) }
    }

    fn get(self) -> u64 {
        match self {
            Self::Physical(a) => a.get(),
            Self::Magic(m) => m.get(),
        }
    }
}

/// A flat attack and its percentage, before they are combined.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScaledAttack {
    /// ATT and ATT%.
    Physical(AttackPower, AttackPct),
    /// Magic ATT and Magic ATT%.
    Magic(MagicAttack, MagicAttackPct),
}

impl ScaledAttack {
    /// `floor(flat × (1 + percent))`.
    pub fn total(self) -> Result<u64, CalcError> {
        let (flat, pct) = match self {
            Self::Physical(a, p) => (a.get(), p.pct()),
            Self::Magic(m, p) => (m.get(), p.pct()),
        };
        formula::scaled(flat, pct.raw()).or_overflow()
    }
}

/// The two ends of the displayed damage range.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DamageRange {
    /// The lower end.
    pub min: StatAttack,
    /// The upper end.
    pub max: StatAttack,
}

/// Inputs to [`displayed_range`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RangeInputs {
    /// The job's weapon multiplier.
    pub weapon_constant: WeaponConstant,
    /// Weapon Mastery; only affects the lower end.
    pub mastery: WeaponMastery,
    /// The stat multiplier.
    pub stat_value: StatValue,
    /// Total ATT or Magic ATT.
    pub attack: JobAttack,
    /// Damage % (the window's, not including Boss Damage).
    pub damage: DamagePct,
    /// Final Damage %.
    pub final_damage: FinalDamage,
}

/// The damage range the stat window displays.
///
/// Source: StrategyWiki §Damage Range, via `maple`'s `formulas.md` §1.13:
///
/// ```text
/// upper_actual = round(weapon_constant × stat_value × attack / 100)
/// lower_actual = round(upper_actual × mastery / 100)
/// upper_shown  = floor(upper_actual × (1 + damage) × (1 + final_damage))
/// lower_shown  = floor(1 + lower_actual × (1 + damage) × (1 + final_damage))
/// ```
///
/// The displayed range leaves out Boss Damage and Normal Monster Damage; the
/// game applies those only when a hit lands. Passing `damage + boss_damage`
/// here would compile (they are one unit) but give the wrong number, so the
/// field is documented as Damage % alone.
pub fn displayed_range(inputs: &RangeInputs) -> Result<DamageRange, CalcError> {
    let (min, max) = formula::displayed_range(
        inputs.weapon_constant.raw(),
        inputs.mastery.pct().raw(),
        inputs.stat_value.get(),
        inputs.attack.get(),
        inputs.damage.pct().raw(),
        inputs.final_damage.pct().raw(),
    )
    .or_overflow()?;
    Ok(DamageRange { min: StatAttack::displayed(min), max: StatAttack::displayed(max) })
}

/// Converts a weapon's attack to the bow-equivalent attack Combat Power uses.
///
/// `flat + floor((bow_base / weapon_base - 1) × (weapon_base + weapon_star_force))`
///
/// Source: maplestorywiki.net Combat Power, and the runnable reference in
/// `maple`'s `formulas.md` §2.3, whose floor placement is the one that
/// reproduces a real character's CP.
pub fn bow_normalised_attack(
    flat: AttackPower,
    weapon_base: AttackPower,
    weapon_star_force: AttackPower,
    bow_base: AttackPower,
) -> Result<AttackPower, CalcError> {
    formula::bow_normalised(flat.get(), weapon_base.get(), weapon_star_force.get(), bow_base.get())
        .map(AttackPower::new)
        .or_overflow()
}

/// Inputs to [`combat_power`].
///
/// Combat Power excludes stats from skills, links and consumables, so every
/// field here is the value with those removed, except `final_damage`, which is
/// the window's total; class Final Damage sources are divided out instead.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CombatPowerInputs {
    /// The stat multiplier over non-skill stats.
    pub stat_value: StatValue,
    /// Bow-normalised flat attack and its percentage.
    pub attack: ScaledAttack,
    /// Critical Damage % without class sources.
    pub critical_damage: CritDamage,
    /// Damage % plus Boss Damage %, without class sources.
    pub damage: DamagePct,
    /// The window's Final Damage %.
    pub final_damage: FinalDamage,
    /// Final Damage sources from the class's own skills, divided back out.
    pub class_final_damage: Vec<FinalDamage>,
}

/// Combat Power.
///
/// ```text
/// floor( stat_value / 100
///      × floor(attack × (1 + attack%))
///      × (1.35 + critical_damage)
///      × (1 + damage + boss_damage)
///      × (1 + final_damage) / Π(1 + class_final_damage) )
/// ```
///
/// Source: the python-fiddle reference linked from maplestorywiki.net's Combat
/// Power page, which reproduces a real character's 236,118 (`maple`'s
/// `formulas.md` §2.3). CP leaves out IED and crit rate, so it is a checksum on
/// captured stats, not a measure of damage.
pub fn combat_power(inputs: &CombatPowerInputs) -> Result<CombatPower, CalcError> {
    let class_fd: Vec<i64> = inputs.class_final_damage.iter().map(|f| f.pct().raw()).collect();
    let cp = formula::combat_power(
        inputs.stat_value.get(),
        inputs.attack.total()?,
        inputs.critical_damage.pct().raw(),
        inputs.damage.pct().raw(),
        inputs.final_damage.pct().raw(),
        &class_fd,
    )
    .or_overflow()?;
    Ok(CombatPower::new(cp))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::StatBreakdown;
    use crate::class;
    use crate::units::StatPct;

    fn pct<T: std::str::FromStr>(s: &str) -> T
    where
        T::Err: fmt::Debug,
    {
        s.parse().unwrap()
    }

    /// GOLDEN: a real stat window. Lutoren (Ren, level 272, Kronos), captured
    /// 2026-09-06, displayed a maximum damage range of 14,736,287.
    ///
    /// The formula gives 14,736,007, 0.0019% low. The gap is the game's own
    /// rounding of inputs it does not display, not a formula error: with any
    /// other weapon constant the result moves by percent, and with Boss Damage
    /// included it is four times too large. Do not widen the tolerance.
    #[test]
    fn golden_lutoren_damage_range() {
        let ren = class::find("ren").unwrap();
        let stats = MainStats { str: Str::new(29_216), dex: Dex::new(3_882), ..MainStats::default() };
        let inputs = RangeInputs {
            weapon_constant: ren.weapon_constant,
            mastery: ren.mastery,
            stat_value: StatValue::for_class(ren, &stats).unwrap(),
            attack: JobAttack::for_class(ren, AttackPower::new(1_772), MagicAttack::new(478)),
            damage: pct("102"),
            final_damage: pct("162.27"),
        };
        let range = displayed_range(&inputs).unwrap();
        assert_eq!(range.max, StatAttack::displayed(14_736_007));

        let displayed = 14_736_287_f64;
        #[allow(clippy::cast_precision_loss, reason = "test tolerance on an 8-digit number")]
        let error = (range.max.get() as f64 - displayed).abs() / displayed;
        assert!(error < 0.0001, "off by {:.4}%", error * 100.0);

        for wrong in [12_000, 12_400, 13_400, 14_400] {
            let other = RangeInputs { weapon_constant: WeaponConstant::from_raw(wrong), ..inputs };
            #[allow(clippy::cast_precision_loss, reason = "test tolerance")]
            let miss = (displayed_range(&other).unwrap().max.get() as f64 - displayed).abs() / displayed;
            assert!(miss > 0.01, "weapon constant {wrong} should miss by more than 1%");
        }
    }

    /// GOLDEN: the python-fiddle reference script reproduces a real Phantom
    /// mule's displayed Combat Power of 236,118. Every input below is the
    /// script's, run through our typed functions instead of its floats.
    #[test]
    fn golden_reference_combat_power() {
        let phantom = class::find("phantom").unwrap();

        // Main stat: (2077 flat − 140 from skills) × (1 + 129%) + 500 not-applied.
        let luk = StatBreakdown::<Luk> {
            base: Luk::new(2_077 - 140),
            percent: Some(pct::<StatPct>("129")),
            flat: Some(Luk::new(500)),
        };
        let dex = StatBreakdown::<Dex> {
            base: Dex::new(750 - 40),
            percent: Some(pct::<StatPct>("48")),
            flat: Some(Dex::new(85)),
        };
        let stats =
            MainStats { luk: luk.implied_total().unwrap(), dex: dex.implied_total().unwrap(), ..MainStats::default() };
        assert_eq!((stats.luk, stats.dex), (Luk::new(4_935), Dex::new(1_135)));

        // 484 ATT less 80 from skills, with a level-200 cane (108 base, 37 from stars) as a 105-ATT bow.
        let attack = bow_normalised_attack(
            AttackPower::new(484 - 80),
            AttackPower::new(108),
            AttackPower::new(37),
            AttackPower::new(105),
        )
        .unwrap();
        assert_eq!(attack, AttackPower::new(399));

        let inputs = CombatPowerInputs {
            stat_value: StatValue::for_class(phantom, &stats).unwrap(),
            attack: ScaledAttack::Physical(attack, pct("6")),
            critical_damage: pct("25.5"), // 40.5 less 15 from Cane Expert
            damage: pct::<DamagePct>("42") + pct::<DamagePct>("25"), // damage 72 less 30 from Priere D'Aria, plus boss 25
            final_damage: pct("71.6"),
            class_final_damage: vec![pct("30"), pct("32")], // Piercing Vision, Cane Expert
        };
        assert_eq!(combat_power(&inputs).unwrap(), CombatPower::new(236_118));
    }

    #[test]
    fn demon_avenger_is_reported_unsupported() {
        let da = class::find("demon-avenger").unwrap();
        assert!(matches!(StatValue::for_class(da, &MainStats::default()), Err(CalcError::Unsupported(_))));
    }

    #[test]
    fn magicians_use_magic_attack() {
        let bishop = class::find("bishop").unwrap();
        assert_eq!(
            JobAttack::for_class(bishop, AttackPower::new(10), MagicAttack::new(99)),
            JobAttack::Magic(MagicAttack::new(99))
        );
    }
}
