//! The Character Info stat window.

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

use serde::{Deserialize, Serialize};

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::decimal::decimal_text;
use crate::fixed::Pct;
use crate::msg::push_uint;
#[cfg(feature = "verus")]
use crate::msg::{self, uint_chars};
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
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// The value is impossible; the write is refused.
    Error,
    /// The value is suspicious (usually a misread); the write is kept.
    Warning,
}

/// A problem found by [`StatWindow::check`].
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Issue {
    /// Error or warning.
    pub severity: Severity,
    /// The field it concerns, e.g. `"ignore_defense"`.
    pub field: &'static str,
    /// What is wrong, phrased for whoever is reading the screen.
    pub message: String,
}

// Verus checks these types and refuses serde's derive on a checked type, so
// their serde impls are written out, the same in both builds.
impl Serialize for Severity {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(match self {
            Self::Error => "error",
            Self::Warning => "warning",
        })
    }
}

impl Serialize for Issue {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = s.serialize_struct("Issue", 3)?;
        st.serialize_field("severity", &self.severity)?;
        st.serialize_field("field", self.field)?;
        st.serialize_field("message", &self.message)?;
        st.end()
    }
}

/// One tooltip set against the total the window shows, as raw counts.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tooltip {
    /// What the tooltip implies ([`breakdown_total`]); `None` if it overflows.
    pub implied: Option<u64>,
    /// The total the window shows.
    pub total: u64,
}

/// One broken rule, found by [`findings`].
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Finding {
    /// Ignore Enemy Defense is 100% or more.
    IgnoreDefense,
    /// Cooldown reduction is above 100%.
    CooldownReduction,
    /// The damage range's minimum is above its maximum.
    Range,
    /// Percentage `k` (in [`PERCENT_FIELDS`] order) is negative.
    Negative(usize),
    /// Tooltip `k` (in [`TOOLTIP_FIELDS`] order) implies another total.
    Mismatch(usize),
    /// Tooltip `k`'s parts are too large to combine.
    Overflow(usize),
}

/// The percentage fields that can never be negative, in check order.
#[allow(clippy::redundant_static_lifetimes, reason = "Verus needs the lifetime spelled out")]
#[cfg_attr(feature = "verus", verus_verify)]
pub const PERCENT_FIELDS: [&'static str; 19] = [
    "damage",
    "boss_damage",
    "normal_damage",
    "final_damage",
    "ignore_defense",
    "ignore_elemental_resistance",
    "critical_rate",
    "critical_damage",
    "abnormal_status_damage",
    "buff_duration",
    "cooldown_reduction_percent",
    "cooldown_skip",
    "summon_duration",
    "weapon_mastery",
    "item_drop_rate",
    "mesos_obtained",
    "additional_exp",
    "stance",
    "speed",
];

/// The stats with a tooltip breakdown, in check order.
#[allow(clippy::redundant_static_lifetimes, reason = "Verus needs the lifetime spelled out")]
#[cfg_attr(feature = "verus", verus_verify)]
pub const TOOLTIP_FIELDS: [&'static str; 7] = ["str", "dex", "int", "luk", "hp", "attack_power", "magic_attack"];

#[cfg(feature = "verus")]
verus! {

/// The negative percentages among the first `n`, in order.
pub open spec fn negatives(p: Seq<Option<i64>>, n: int) -> Seq<Finding>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = negatives(p, n - 1);
        match p[n - 1] {
            Some(v) => if v < 0 { rest.push(Finding::Negative((n - 1) as usize)) } else { rest },
            None => rest,
        }
    }
}

/// The tooltips among the first `n` that disagree with their totals, in order.
pub open spec fn disagreements(t: Seq<Option<Tooltip>>, n: int) -> Seq<Finding>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = disagreements(t, n - 1);
        match t[n - 1] {
            Some(tip) => match tip.implied {
                Some(i) => if i == tip.total { rest } else { rest.push(Finding::Mismatch((n - 1) as usize)) },
                None => rest.push(Finding::Overflow((n - 1) as usize)),
            },
            None => rest,
        }
    }
}

/// The rules on single values a window breaks, in order: Ignore Enemy
/// Defense, cooldown reduction, then the damage range.
pub open spec fn head(ied: Option<i64>, cdr: Option<i64>, range: Option<(u64, u64)>) -> Seq<Finding> {
    let a = match ied {
        Some(v) => if v < 10_000 { seq![] } else { seq![Finding::IgnoreDefense] },
        None => seq![],
    };
    let b = match cdr {
        Some(v) => if v <= 10_000 { seq![] } else { seq![Finding::CooldownReduction] },
        None => seq![],
    };
    let c = match range {
        Some(r) => if r.0 <= r.1 { seq![] } else { seq![Finding::Range] },
        None => seq![],
    };
    a + b + c
}

/// Every rule a window breaks, in order: [`head`], each negative
/// percentage, then each tooltip that disagrees with its total.
pub open spec fn findings_spec(
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: Seq<Option<i64>>,
    tooltips: Seq<Option<Tooltip>>,
) -> Seq<Finding> {
    head(ied, cdr, range) + negatives(percents, percents.len() as int) + disagreements(tooltips, tooltips.len() as int)
}

} // verus!

/// Every rule a window breaks, from its raw values: Ignore Enemy Defense and
/// cooldown reduction in hundredths, the damage range, the percentages in
/// [`PERCENT_FIELDS`] order and the tooltips in [`TOOLTIP_FIELDS`] order.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r@ == findings_spec(ied, cdr, range, percents@, tooltips@),
))]
#[must_use]
#[allow(
    clippy::single_match,
    clippy::collapsible_match,
    reason = "Verus checks plain matches; it does not support `if let` chains"
)]
pub fn findings(
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: &[Option<i64>],
    tooltips: &[Option<Tooltip>],
) -> Vec<Finding> {
    let mut out = Vec::new();
    match ied {
        Some(v) => {
            if !rules::ignore_defense_ok(v) {
                out.push(Finding::IgnoreDefense);
            }
        }
        None => {}
    }
    match cdr {
        Some(v) => {
            if !rules::cooldown_reduction_ok(v) {
                out.push(Finding::CooldownReduction);
            }
        }
        None => {}
    }
    match range {
        Some((min, max)) => {
            if !rules::range_ok(min, max) {
                out.push(Finding::Range);
            }
        }
        None => {}
    }
    proof! {
        assert(out@ =~= head(ied, cdr, range) + negatives(percents@, 0));
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= percents@.len(),
            out@ == head(ied, cdr, range) + negatives(percents@, i as int),
        decreases percents@.len() - i
    ))]
    while i < percents.len() {
        match percents[i] {
            Some(v) => {
                if !rules::percentage_ok(v) {
                    out.push(Finding::Negative(i));
                }
            }
            None => {}
        }
        proof! {
            assert(out@ =~= head(ied, cdr, range) + negatives(percents@, i + 1));
        }
        i += 1;
    }
    proof! {
        assert(out@ =~= head(ied, cdr, range) + negatives(percents@, percents@.len() as int) + disagreements(tooltips@, 0));
    }
    let mut k: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i == percents@.len(),
            k <= tooltips@.len(),
            out@ == head(ied, cdr, range) + negatives(percents@, percents@.len() as int) + disagreements(tooltips@, k as int),
        decreases tooltips@.len() - k
    ))]
    while k < tooltips.len() {
        match tooltips[k] {
            Some(tip) => match tip.implied {
                Some(implied) => {
                    if implied != tip.total {
                        out.push(Finding::Mismatch(k));
                    }
                }
                None => out.push(Finding::Overflow(k)),
            },
            None => {}
        }
        proof! {
            assert(out@ =~= head(ied, cdr, range) + negatives(percents@, percents@.len() as int) + disagreements(tooltips@, k + 1));
        }
        k += 1;
    }
    out
}

#[cfg(feature = "verus")]
verus! {

/// What `{}` prints for a percentage in hundredths: `93.14`.
pub open spec fn pct_chars(raw: int) -> Seq<char> {
    msg::chars(decimal_text(raw, 2))
}

/// The message [`issues`] gives a finding.
pub open spec fn message_of(
    f: Finding,
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: Seq<Option<i64>>,
    tooltips: Seq<Option<Tooltip>>,
) -> Seq<char> {
    match f {
        Finding::IgnoreDefense => "Ignore Enemy Defense is always below 100%, got "@
            + pct_chars(match ied { Some(v) => v as int, None => 0 }),
        Finding::CooldownReduction => "cooldown reduction cannot exceed 100%, got "@
            + pct_chars(match cdr { Some(v) => v as int, None => 0 }),
        Finding::Range => {
            let (min, max) = match range { Some(r) => r, None => (0u64, 0u64) };
            "damage range minimum "@ + uint_chars(min as nat) + " is above the maximum "@ + uint_chars(max as nat)
        },
        Finding::Negative(k) => PERCENT_FIELDS[k as int]@ + " cannot be negative, got "@
            + pct_chars(match percents[k as int] { Some(v) => v as int, None => 0 }),
        Finding::Mismatch(k) => {
            let t = match tooltips[k as int] { Some(t) => t, None => Tooltip { implied: None, total: 0 } };
            "tooltip implies "@ + uint_chars(match t.implied { Some(i) => i as nat, None => 0 })
                + " (floor(base × (1 + percent/100)) + flat) but the total reads "@ + uint_chars(t.total as nat)
                + "; one of them is probably misread"@
        },
        Finding::Overflow(_) => "tooltip values are too large to combine"@,
    }
}

/// The severity [`issues`] gives a finding: only a tooltip mismatch is a warning.
pub open spec fn severity_of(f: Finding) -> Severity {
    match f {
        Finding::Mismatch(_) => Severity::Warning,
        _ => Severity::Error,
    }
}

/// The field [`issues`] names for a finding.
pub open spec fn field_of(f: Finding) -> Seq<char> {
    match f {
        Finding::IgnoreDefense => "ignore_defense"@,
        Finding::CooldownReduction => "cooldown_reduction_percent"@,
        Finding::Range => "stat_attack_min"@,
        Finding::Negative(k) => PERCENT_FIELDS[k as int]@,
        Finding::Mismatch(k) => TOOLTIP_FIELDS[k as int]@,
        Finding::Overflow(k) => TOOLTIP_FIELDS[k as int]@,
    }
}

/// The findings' indices are in range: a `Negative` names one of the
/// percentages, a `Mismatch` or `Overflow` one of the tooltips.
pub open spec fn in_range(f: Finding, np: int, nt: int) -> bool {
    match f {
        Finding::Negative(k) => k < np,
        Finding::Mismatch(k) => k < nt,
        Finding::Overflow(k) => k < nt,
        _ => true,
    }
}

proof fn lemma_negatives_in_range(p: Seq<Option<i64>>, n: int, np: int, nt: int)
    requires 0 <= n <= p.len(), n <= np,
    ensures forall|j: int| 0 <= j < negatives(p, n).len() ==> in_range(#[trigger] negatives(p, n)[j], np, nt),
    decreases n,
{
    if n > 0 {
        lemma_negatives_in_range(p, n - 1, np, nt);
        let rest = negatives(p, n - 1);
        let all = negatives(p, n);
        assert forall|j: int| 0 <= j < all.len() implies in_range(#[trigger] all[j], np, nt) by {
            if j < rest.len() {
                assert(all[j] == rest[j]);
            }
        }
    }
}

proof fn lemma_disagreements_in_range(t: Seq<Option<Tooltip>>, n: int, np: int, nt: int)
    requires 0 <= n <= t.len(), n <= nt,
    ensures forall|j: int| 0 <= j < disagreements(t, n).len() ==> in_range(#[trigger] disagreements(t, n)[j], np, nt),
    decreases n,
{
    if n > 0 {
        lemma_disagreements_in_range(t, n - 1, np, nt);
        let rest = disagreements(t, n - 1);
        let all = disagreements(t, n);
        assert forall|j: int| 0 <= j < all.len() implies in_range(#[trigger] all[j], np, nt) by {
            if j < rest.len() {
                assert(all[j] == rest[j]);
            }
        }
    }
}

proof fn lemma_findings_in_range(
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: Seq<Option<i64>>,
    tooltips: Seq<Option<Tooltip>>,
)
    ensures
        forall|j: int| 0 <= j < findings_spec(ied, cdr, range, percents, tooltips).len()
            ==> in_range(#[trigger] findings_spec(ied, cdr, range, percents, tooltips)[j], percents.len() as int, tooltips.len() as int),
{
    let h = head(ied, cdr, range);
    let ng = negatives(percents, percents.len() as int);
    let d = disagreements(tooltips, tooltips.len() as int);
    lemma_negatives_in_range(percents, percents.len() as int, percents.len() as int, tooltips.len() as int);
    lemma_disagreements_in_range(tooltips, tooltips.len() as int, percents.len() as int, tooltips.len() as int);
    assert forall|j: int| 0 <= j < h.len() implies in_range(#[trigger] h[j], percents.len() as int, tooltips.len() as int) by {}
    let all = findings_spec(ied, cdr, range, percents, tooltips);
    assert(all == h + ng + d);
    assert forall|j: int| 0 <= j < all.len() implies in_range(#[trigger] all[j], percents.len() as int, tooltips.len() as int) by {
        if j < h.len() {
            assert(all[j] == h[j]);
        } else if j < h.len() + ng.len() {
            assert(all[j] == ng[j - h.len()]);
        } else {
            assert(all[j] == d[j - h.len() - ng.len()]);
        }
    }
}

} // verus!

/// What `{}` prints for a percentage of `raw` hundredths.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(ensures final(m)@ == old(m)@ + pct_chars(raw as int)))]
fn push_pct(m: &mut String, raw: i64) {
    let t = Pct::from_raw(raw).text();
    m.push_str(t.as_str());
}

/// The issue for one finding, worded for whoever is reading the screen.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires in_range(f, 19, 7),
    ensures
        r.severity == severity_of(f),
        r.field@ == field_of(f),
        r.message@ == message_of(f, ied, cdr, range, percents@, tooltips@),
))]
fn issue(
    f: Finding,
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: &[Option<i64>; 19],
    tooltips: &[Option<Tooltip>; 7],
) -> Issue {
    let mut text = String::new();
    match f {
        Finding::IgnoreDefense => {
            text.push_str("Ignore Enemy Defense is always below 100%, got ");
            push_pct(
                &mut text,
                match ied {
                    Some(v) => v,
                    None => 0,
                },
            );
            Issue { severity: Severity::Error, field: "ignore_defense", message: text }
        }
        Finding::CooldownReduction => {
            text.push_str("cooldown reduction cannot exceed 100%, got ");
            push_pct(
                &mut text,
                match cdr {
                    Some(v) => v,
                    None => 0,
                },
            );
            Issue { severity: Severity::Error, field: "cooldown_reduction_percent", message: text }
        }
        Finding::Range => {
            let (min, max) = match range {
                Some(r) => r,
                None => (0, 0),
            };
            text.push_str("damage range minimum ");
            push_uint(&mut text, min as u128);
            text.push_str(" is above the maximum ");
            push_uint(&mut text, max as u128);
            Issue { severity: Severity::Error, field: "stat_attack_min", message: text }
        }
        Finding::Negative(k) => {
            let field = PERCENT_FIELDS[k];
            text.push_str(field);
            text.push_str(" cannot be negative, got ");
            push_pct(
                &mut text,
                match percents[k] {
                    Some(v) => v,
                    None => 0,
                },
            );
            Issue { severity: Severity::Error, field, message: text }
        }
        Finding::Mismatch(k) => {
            let t = match tooltips[k] {
                Some(t) => t,
                None => Tooltip { implied: None, total: 0 },
            };
            text.push_str("tooltip implies ");
            push_uint(
                &mut text,
                match t.implied {
                    Some(i) => i as u128,
                    None => 0,
                },
            );
            text.push_str(" (floor(base × (1 + percent/100)) + flat) but the total reads ");
            push_uint(&mut text, t.total as u128);
            text.push_str("; one of them is probably misread");
            Issue { severity: Severity::Warning, field: TOOLTIP_FIELDS[k], message: text }
        }
        Finding::Overflow(k) => {
            text.push_str("tooltip values are too large to combine");
            Issue { severity: Severity::Error, field: TOOLTIP_FIELDS[k], message: text }
        }
    }
}

/// Every rule a window breaks ([`findings`]), each worded as an [`Issue`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r@.len() == findings_spec(ied, cdr, range, percents@, tooltips@).len(),
        forall|i: int| 0 <= i < r@.len() ==> {
            let f = #[trigger] findings_spec(ied, cdr, range, percents@, tooltips@)[i];
            &&& r@[i].severity == severity_of(f)
            &&& r@[i].field@ == field_of(f)
            &&& r@[i].message@ == message_of(f, ied, cdr, range, percents@, tooltips@)
        },
))]
#[must_use]
pub fn issues(
    ied: Option<i64>,
    cdr: Option<i64>,
    range: Option<(u64, u64)>,
    percents: &[Option<i64>; 19],
    tooltips: &[Option<Tooltip>; 7],
) -> Vec<Issue> {
    let fs = findings(ied, cdr, range, percents.as_slice(), tooltips.as_slice());
    proof! {
        lemma_findings_in_range(ied, cdr, range, percents@, tooltips@);
        assert(percents@.len() == 19 && tooltips@.len() == 7);
        assert forall|j: int| 0 <= j < fs@.len() implies in_range(#[trigger] fs@[j], 19, 7) by {
            assert(in_range(findings_spec(ied, cdr, range, percents@, tooltips@)[j], 19, 7));
        }
    }
    let mut out: Vec<Issue> = Vec::new();
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= fs@.len(),
            fs@ == findings_spec(ied, cdr, range, percents@, tooltips@),
            forall|j: int| 0 <= j < fs@.len() ==> in_range(#[trigger] fs@[j], 19, 7),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let f = #[trigger] fs@[j];
                &&& out@[j].severity == severity_of(f)
                &&& out@[j].field@ == field_of(f)
                &&& out@[j].message@ == message_of(f, ied, cdr, range, percents@, tooltips@)
            },
        decreases fs@.len() - i
    ))]
    while i < fs.len() {
        out.push(issue(fs[i], ied, cdr, range, percents, tooltips));
        i += 1;
    }
    out
}

/// One tooltip set against its total.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r.total as int == total.count(),
        match r.implied {
            Some(i) => i as int == crate::formula::scaled_spec(base.count(), percent_raw(percent)) + flat_count(flat),
            None => crate::formula::scaled_spec(base.count(), percent_raw(percent)) + flat_count(flat) > u64::MAX,
        },
))]
#[must_use]
pub fn tooltip_of<T: Scalable>(base: T, percent: Option<T::Percent>, flat: Option<T>, total: T) -> Tooltip {
    let implied = match breakdown_total(base, percent, flat) {
        Some(t) => Some(t.get()),
        None => None,
    };
    Tooltip { implied, total: total.get() }
}

/// One tooltip against its total, if both were captured.
fn tooltip<T: Scalable>(breakdown: Option<StatBreakdown<T>>, total: Option<T>) -> Option<Tooltip> {
    let (Some(b), Some(total)) = (breakdown, total) else { return None };
    Some(tooltip_of(b.base, b.percent, b.flat, total))
}

impl StatWindow {
    /// Checks the window for impossible and suspicious values: the rules
    /// [`findings`] proves, each worded by [`issues`].
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
        let raw = |p: Option<Pct>| p.map(Pct::raw);
        let percents = self.percentages().map(raw);
        let tooltips = self.breakdowns.map_or([None; 7], |b| {
            [
                tooltip(b.str, self.str),
                tooltip(b.dex, self.dex),
                tooltip(b.int, self.int),
                tooltip(b.luk, self.luk),
                tooltip(b.hp, self.hp),
                tooltip(b.attack_power, self.attack_power),
                tooltip(b.magic_attack, self.magic_attack),
            ]
        });
        let range = self.stat_attack_min.zip(self.stat_attack_max).map(|(a, b)| (a.get(), b.get()));
        issues(
            raw(self.ignore_defense.map(Percent::pct)),
            raw(self.cooldown_reduction_percent.map(Percent::pct)),
            range,
            &percents,
            &tooltips,
        )
    }

    /// Every percentage field that can never be negative, in [`PERCENT_FIELDS`] order.
    fn percentages(&self) -> [Option<Pct>; 19] {
        [
            self.damage.map(Percent::pct),
            self.boss_damage.map(Percent::pct),
            self.normal_damage.map(Percent::pct),
            self.final_damage.map(Percent::pct),
            self.ignore_defense.map(Percent::pct),
            self.ignore_elemental_resistance.map(Percent::pct),
            self.critical_rate.map(Percent::pct),
            self.critical_damage.map(Percent::pct),
            self.abnormal_status_damage.map(Percent::pct),
            self.buff_duration.map(Percent::pct),
            self.cooldown_reduction_percent.map(Percent::pct),
            self.cooldown_skip.map(Percent::pct),
            self.summon_duration.map(Percent::pct),
            self.weapon_mastery.map(Percent::pct),
            self.item_drop_rate.map(Percent::pct),
            self.mesos_obtained.map(Percent::pct),
            self.additional_exp.map(Percent::pct),
            self.stance.map(Percent::pct),
            self.speed.map(Percent::pct),
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

    #[test]
    fn messages_are_unchanged() {
        let window: StatWindow = serde_json::from_str(
            r#"{
                "stat_attack_min": 30, "stat_attack_max": 20,
                "ignore_defense": 100.5, "cooldown_reduction_percent": 101,
                "boss_damage": -3.25, "speed": -1,
                "luk": 38000, "str": 5,
                "breakdowns": {
                    "luk": { "base": 5000, "percent": 300, "flat": 18120 },
                    "str": { "base": 18446744073709551615, "percent": 100 }
                }
            }"#,
        )
        .unwrap();
        let got: Vec<(Severity, &str, String)> =
            window.check().into_iter().map(|i| (i.severity, i.field, i.message)).collect();
        let e = Severity::Error;
        assert_eq!(
            got,
            vec![
                (e, "ignore_defense", "Ignore Enemy Defense is always below 100%, got 100.50".to_owned()),
                (e, "cooldown_reduction_percent", "cooldown reduction cannot exceed 100%, got 101.00".to_owned()),
                (e, "stat_attack_min", "damage range minimum 30 is above the maximum 20".to_owned()),
                (e, "boss_damage", "boss_damage cannot be negative, got -3.25".to_owned()),
                (e, "speed", "speed cannot be negative, got -1.00".to_owned()),
                (e, "str", "tooltip values are too large to combine".to_owned()),
                (
                    Severity::Warning,
                    "luk",
                    "tooltip implies 38120 (floor(base × (1 + percent/100)) + flat) but the total reads 38000; one of them is probably misread".to_owned()
                ),
            ]
        );
    }
}
