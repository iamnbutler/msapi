//! One type per unit, so incompatible quantities cannot be combined.
//!
//! Every number on the stat window has a unit, and the units do not mix:
//!
//! - **Flat stats** ([`Str`], [`AttackPower`], …) add only to themselves.
//!   `Str + Dex` does not compile; the stat multiplier that weights them is
//!   [`crate::calc::StatValue`].
//! - **Additive percentages** add within a pool. Damage, Boss Damage and
//!   Normal Monster Damage share one pool in the game, so they share one type,
//!   [`DamagePct`], and `damage + boss_damage` compiles.
//! - **Multiplicative percentages** never add. [`FinalDamage`] sources multiply
//!   as `(1 + a)(1 + b)`, and [`IgnoreDefense`] sources stack as
//!   `1 - (1 - a)(1 - b)`. Neither type implements `Add`, so the classic bug of
//!   summing IED lines cannot be written.
//! - **Displayed results** ([`CombatPower`], [`StatAttack`]) are outputs. They
//!   compare but do not do arithmetic.
//!
//! Crossing units always goes through a named function that turns a quantity
//! into a dimensionless [`Ratio`] (for example [`DamagePct::factor`]), so every
//! multiplication in a formula is visible at the call site.
//!
//! ```compile_fail
//! use msapi_core::units::{Str, Dex};
//! let _ = Str::new(10) + Dex::new(5); // different units
//! ```
//!
//! ```compile_fail
//! use msapi_core::units::IgnoreDefense;
//! let a: IgnoreDefense = "40".parse().unwrap();
//! let _ = a + a; // IED stacks multiplicatively; use IgnoreDefense::stack
//! ```
//!
//! ```
//! use msapi_core::units::DamagePct;
//! let damage: DamagePct = "102".parse()?;
//! let boss: DamagePct = "316".parse()?;
//! assert_eq!((damage + boss).to_string(), "418.00");
//! # Ok::<(), msapi_core::FixedError>(())
//! ```

use std::fmt;
use std::iter::Sum;
use std::ops::{Add, AddAssign};
use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::fixed::{Fixed, FixedError, Pct};
use crate::formula;
use crate::ratio::Ratio;
#[cfg(feature = "verus")]
use vstd::prelude::*;

/// A unit stored as a plain count.
pub trait Count: Copy {
    /// The count.
    fn get(self) -> u64;
}

/// A unit stored as a two-decimal percentage.
pub trait Percent: Copy {
    /// The percentage.
    fn pct(self) -> Pct;
}

/// A flat stat that a tooltip breaks into `base × (1 + percent) + flat`.
///
/// The associated [`Scalable::Percent`] ties each stat to its own percentage,
/// so a STR breakdown cannot be given an ATT% by mistake.
pub trait Scalable: Count + From<u64> {
    /// The percentage that scales this stat.
    type Percent: Percent;
}

macro_rules! flat {
    ($($(#[$doc:meta])* $name:ident;)*) => {$(
        $(#[$doc])*
        #[cfg_attr(feature = "verus", verus_verify)]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(u64);

        // By hand rather than derived (Verus refuses serde's derive on a
        // checked type); the same as `#[serde(transparent)]`.
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                u64::deserialize(deserializer).map(Self)
            }
        }

        #[cfg(feature = "verus")]
        verus! {
            impl $name {
                /// The count, for specs.
                pub closed spec fn value(self) -> int {
                    self.0 as int
                }
            }
        }

        #[cfg_attr(feature = "verus", verus_verify)]
        impl $name {
            /// Wraps a count.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == n as int))]
            pub const fn new(n: u64) -> Self {
                Self(n)
            }

            /// The count.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.value()))]
            pub const fn get(self) -> u64 {
                self.0
            }

            /// The sum, saturating at `u64::MAX` as `Fixed`'s addition does:
            /// no total a stat window shows is near it, and a wrapped one
            /// would be silently wrong.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r =>
                ensures r.value() == if self.value() + rhs.value() > u64::MAX { u64::MAX as int } else { self.value() + rhs.value() }
            ))]
            pub const fn plus(self, rhs: Self) -> Self {
                Self(self.0.saturating_add(rhs.0))
            }
        }

        impl Count for $name {
            fn get(self) -> u64 {
                self.0
            }
        }

        impl From<u64> for $name {
            fn from(n: u64) -> Self {
                Self(n)
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "({})"), self.0)
            }
        }
    )*};
}

macro_rules! additive {
    ($($name:ident),*) => {$(
        // Delegates to the checked `plus`; vstd's `Add` spec is not this one.
        impl Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                self.plus(rhs)
            }
        }

        impl AddAssign for $name {
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs;
            }
        }

        impl Sum for $name {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::default(), Add::add)
            }
        }
    )*};
}

macro_rules! percent {
    ($($(#[$doc:meta])* $name:ident;)*) => {$(
        $(#[$doc])*
        #[cfg_attr(feature = "verus", verus_verify)]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(Pct);

        // By hand rather than derived (Verus refuses serde's derive on a
        // checked type); the same as `#[serde(transparent)]`.
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                Pct::deserialize(deserializer).map(Self)
            }
        }

        #[cfg(feature = "verus")]
        verus! {
            impl $name {
                /// The raw percentage in hundredths, for specs.
                pub closed spec fn value(self) -> int {
                    self.0.value()
                }
            }
        }

        #[cfg_attr(feature = "verus", verus_verify)]
        impl $name {
            /// Wraps a percentage.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == p.value()))]
            pub const fn new(p: Pct) -> Self {
                Self(p)
            }

            /// The percentage.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == self.value()))]
            pub const fn pct(self) -> Pct {
                self.0
            }

            /// The raw percentage in hundredths (`93.14%` is `9314`).
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r => ensures r as int == self.value()))]
            pub const fn raw(self) -> i64 {
                self.0.raw()
            }

            /// The sum within this pool, saturating at the ends of `i64` as
            /// `Fixed`'s addition does.
            #[must_use]
            #[cfg_attr(feature = "verus", verus_spec(r =>
                ensures r.value() == if self.value() + rhs.value() > i64::MAX { i64::MAX as int }
                    else if self.value() + rhs.value() < i64::MIN { i64::MIN as int }
                    else { self.value() + rhs.value() }
            ))]
            pub const fn plus(self, rhs: Self) -> Self {
                // `i64::saturating_add`, written out so Verus can check it.
                let sum = self.0.raw() as i128 + rhs.0.raw() as i128;
                let raw = if sum > i64::MAX as i128 {
                    i64::MAX
                } else if sum < i64::MIN as i128 {
                    i64::MIN
                } else {
                    #[allow(clippy::cast_possible_truncation, reason = "in range: the branches above cut off the rest")]
                    let raw = sum as i64;
                    raw
                };
                Self(Pct::from_raw(raw))
            }
        }


        impl Percent for $name {
            fn pct(self) -> Pct {
                self.0
            }
        }

        impl FromStr for $name {
            type Err = FixedError;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                s.parse().map(Self)
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "({}%)"), self.0)
            }
        }
    )*};
}

flat! {
    /// STR.
    Str;
    /// DEX.
    Dex;
    /// INT.
    Int;
    /// LUK.
    Luk;
    /// Max HP.
    MaxHp;
    /// Max MP.
    MaxMp;
    /// Attack Power (ATT).
    AttackPower;
    /// Magic Attack (MATT).
    MagicAttack;
    /// Defense.
    Defense;
    /// Star Force.
    StarForce;
    /// Arcane Power.
    ArcanePower;
    /// Sacred Power.
    SacredPower;
    /// Status Resistance.
    StatusResistance;
    /// Ability Points.
    AbilityPoints;
    /// Combat Power as displayed. An output: comparable, not summable.
    CombatPower;
    /// One end of the displayed damage range. An output: comparable, not summable.
    StatAttack;
}

additive!(
    Str,
    Dex,
    Int,
    Luk,
    MaxHp,
    MaxMp,
    AttackPower,
    MagicAttack,
    Defense,
    StarForce,
    ArcanePower,
    SacredPower,
    StatusResistance,
    AbilityPoints
);

percent! {
    /// A primary-stat percentage (STR%, DEX%, INT%, LUK%, All Stat%).
    StatPct;
    /// Max HP %.
    HpPct;
    /// ATT %.
    AttackPct;
    /// Magic ATT %.
    MagicAttackPct;
    /// The additive damage pool: Damage %, Boss Damage % and Normal Monster Damage %.
    DamagePct;
    /// Final Damage %. Multiplicative: see [`FinalDamage::stack`].
    FinalDamage;
    /// Ignore Enemy Defense %. Multiplicative: see [`IgnoreDefense::stack`].
    IgnoreDefense;
    /// A monster's defense rate (PDR), e.g. 300% for most endgame bosses.
    DefenseRate;
    /// Ignore Elemental Resistance %.
    IgnoreElementalResistance;
    /// Critical Rate %.
    CritRate;
    /// Critical Damage %.
    CritDamage;
    /// Damage % against enemies with an abnormal status.
    AbnormalStatusDamage;
    /// Buff Duration %.
    BuffDuration;
    /// Cooldown reduction %.
    CooldownReductionPct;
    /// Chance to skip a cooldown, %.
    CooldownSkip;
    /// Summon Duration %.
    SummonDuration;
    /// Weapon Mastery %.
    WeaponMastery;
    /// Item Drop Rate %.
    ItemDropRate;
    /// Mesos Obtained %.
    MesosObtained;
    /// Additional EXP %.
    AdditionalExp;
    /// Stance (knockback resistance) %.
    Stance;
    /// Movement Speed %.
    Speed;
    /// Jump %.
    Jump;
}

additive!(
    StatPct,
    HpPct,
    AttackPct,
    MagicAttackPct,
    DamagePct,
    IgnoreElementalResistance,
    CritRate,
    CritDamage,
    AbnormalStatusDamage,
    BuffDuration,
    CooldownReductionPct,
    CooldownSkip,
    SummonDuration,
    ItemDropRate,
    MesosObtained,
    AdditionalExp,
    Stance,
    Speed,
    Jump
);

impl Scalable for Str {
    type Percent = StatPct;
}
impl Scalable for Dex {
    type Percent = StatPct;
}
impl Scalable for Int {
    type Percent = StatPct;
}
impl Scalable for Luk {
    type Percent = StatPct;
}
impl Scalable for MaxHp {
    type Percent = HpPct;
}
impl Scalable for AttackPower {
    type Percent = AttackPct;
}
impl Scalable for MagicAttack {
    type Percent = MagicAttackPct;
}

/// Cooldown reduction in seconds, to two decimals.
pub type CooldownSeconds = Fixed<2>;

/// `1 + p / 100` as an exact ratio.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(formula::one_plus(p.value()), 10_000)))]
fn one_plus(p: Pct) -> Ratio {
    formula::one_plus_factor(p.raw())
}

#[cfg(feature = "verus")]
verus! {

/// The raw values of a list of percentages, for specs.
pub open spec fn raws_fd(s: Seq<FinalDamage>) -> Seq<i64> {
    s.map_values(|f: FinalDamage| f.value() as i64)
}

/// The raw values of a list of percentages, for specs.
pub open spec fn raws_ied(s: Seq<IgnoreDefense>) -> Seq<i64> {
    s.map_values(|f: IgnoreDefense| f.value() as i64)
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl DamagePct {
    /// The damage multiplier this pool contributes: `1 + d`.
    ///
    /// ```
    /// use msapi_core::units::DamagePct;
    /// let d: DamagePct = "102".parse()?;
    /// assert_eq!(d.factor().to_string(), "101/50"); // 2.02
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(formula::one_plus(self.value()), 10_000)))]
    pub fn factor(self) -> Ratio {
        one_plus(self.0)
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl FinalDamage {
    /// The multiplier: `1 + f`.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(formula::one_plus(self.value()), 10_000)))]
    pub fn factor(self) -> Ratio {
        one_plus(self.0)
    }

    /// Combined multiplier of several independent Final Damage sources:
    /// `(1 + a)(1 + b)…`.
    ///
    /// ```
    /// use msapi_core::units::FinalDamage;
    /// let sources: Vec<FinalDamage> = vec!["30".parse()?, "32".parse()?];
    /// assert_eq!(FinalDamage::stack(&sources).unwrap().to_string(), "429/250"); // 1.716
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(r) ==> r.wf() && r.is(formula::stack_plus(raws_fd(sources@)), formula::whole_pow(sources@.len())),
    ))]
    pub fn stack(sources: &[Self]) -> Option<Ratio> {
        let mut raws: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant i <= sources@.len(), raws@ == raws_fd(sources@.take(i as int)),
            decreases sources@.len() - i
        ))]
        while i < sources.len() {
            proof! {
                assert(raws_fd(sources@.take(i + 1)) =~= raws_fd(sources@.take(i as int)).push(sources@[i as int].value() as i64));
            }
            raws.push(sources[i].raw());
            i += 1;
        }
        proof! {
            assert(sources@.take(sources@.len() as int) =~= sources@);
        }
        formula::stack_final_damage(&raws)
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl IgnoreDefense {
    /// The share of defense left after this source: `1 - i`.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(formula::one_minus(self.value()), 10_000)))]
    pub fn remaining(self) -> Ratio {
        formula::one_minus_factor(self.0.raw())
    }

    /// The defense left after several independent sources:
    /// `(1 - a)(1 - b)…`. Total IED is one minus this.
    ///
    /// Two 20% sources leave `0.64` of the defense, which is 36% IED, not 40%.
    ///
    /// ```
    /// use msapi_core::units::IgnoreDefense;
    /// let twenty: IgnoreDefense = "20".parse()?;
    /// assert_eq!(IgnoreDefense::stack(&[twenty, twenty]).unwrap().to_string(), "16/25"); // 0.64
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures
            r matches Some(r) ==> r.wf() && r.is(formula::stack_minus(raws_ied(sources@)), formula::whole_pow(sources@.len())),
    ))]
    pub fn stack(sources: &[Self]) -> Option<Ratio> {
        let mut raws: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        #[cfg_attr(feature = "verus", verus_spec(
            invariant i <= sources@.len(), raws@ == raws_ied(sources@.take(i as int)),
            decreases sources@.len() - i
        ))]
        while i < sources.len() {
            proof! {
                assert(raws_ied(sources@.take(i + 1)) =~= raws_ied(sources@.take(i as int)).push(sources@[i as int].value() as i64));
            }
            raws.push(sources[i].raw());
            i += 1;
        }
        proof! {
            assert(sources@.take(sources@.len() as int) =~= sources@);
        }
        formula::stack_ignore_defense(&raws)
    }

    /// The defense multiplier against a monster: `max(0, 1 - pdr × (1 - ied))`,
    /// with the monster's defense rate capped at 500%.
    ///
    /// ```
    /// use msapi_core::units::{DefenseRate, IgnoreDefense};
    /// let ied: IgnoreDefense = "90".parse()?;
    /// let boss: DefenseRate = "300".parse()?;
    /// assert_eq!(ied.defense_factor(boss).unwrap().to_string(), "7/10"); // 1 - 3.0 × 0.1
    /// # Ok::<(), msapi_core::FixedError>(())
    /// ```
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r =>
        ensures r matches Some(r) ==> {
            let p = if monster.value() < 0 { 0 } else if monster.value() > 50_000 { 50_000 } else { monster.value() };
            &&& r.wf()
            &&& r.is(formula::clamp0(100_000_000 - p * formula::one_minus(self.value())), 100_000_000)
        },
    ))]
    pub fn defense_factor(self, monster: DefenseRate) -> Option<Ratio> {
        formula::defense_factor(self.0.raw(), monster.0.raw())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl CritDamage {
    /// The average critical multiplier on a crit: `1.35 + cd`.
    ///
    /// A crit rolls uniformly between `1.20 + cd` and `1.50 + cd`.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.wf(), r.is(formula::clamp0(13_500 + self.value()), 10_000)))]
    pub fn crit_factor(self) -> Ratio {
        formula::crit_factor(self.0.raw())
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
impl StatAttack {
    /// Wraps a displayed damage-range value.
    #[must_use]
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r.value() == n as int))]
    pub const fn displayed(n: u64) -> Self {
        Self(n)
    }
}
