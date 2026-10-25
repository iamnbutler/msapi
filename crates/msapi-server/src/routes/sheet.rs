//! `GET /v1/characters/{id}/sheet`: a character on one short Markdown page,
//! for agents and people pasting it into a chat.
//!
//! The JSON routes keep every field; the sheet keeps what answers the common
//! questions (what to enhance next, whether an item is an upgrade) and
//! flattens each item to a few lines: stars, potential, flame and totals,
//! with stat names abbreviated as players write them.

use std::fmt::Write as _;

use rusqlite::Connection;
use serde_json::{Map, Value};

use msapi_core::class::{self, Class, MainStat};

use super::{characters, equipment, stats};
use crate::auth::Principal;
use crate::error::ApiError;
use crate::http::Response;

/// `GET /v1/characters/{id}/sheet`, with or without a token.
pub fn get(conn: &Connection, principal: Option<&Principal>, id: &str) -> Result<Response, ApiError> {
    let character = characters::find_readable(conn, principal, id)?;
    let character = serde_json::to_value(&character).map_err(|_| ApiError::internal())?;
    let stat = stats::latest(conn, id)?.map(|s| s.stat);
    let stat = stat.map(|s| serde_json::to_value(s).map_err(|_| ApiError::internal())).transpose()?;
    let equipment = equipment::latest(conn, id)?.map(|s| s.equipment);
    let equipment = equipment.map(|e| serde_json::to_value(e).map_err(|_| ApiError::internal())).transpose()?;
    let text = render(&character, stat.as_ref(), equipment.as_ref());
    Ok(Response::text(200, "text/markdown; charset=utf-8", text))
}

/// The sheet for a character's JSON and its latest stat and equipment windows.
pub fn render(character: &Value, stat: Option<&Value>, equipment: Option<&Value>) -> String {
    let id = str_at(character, "id");
    let class = class::find(str_at(character, "character_class_id"));
    let stats = Stats::of(class);
    let mut out = String::new();

    let _ = writeln!(out, "# {}", str_at(character, "character_name"));
    let mut line =
        vec![format!("Lv. {} {}", num_at(character, "character_level"), str_at(character, "character_class"))];
    line.push(format!(
        "{} ({}, {} {})",
        str_at(character, "world_name"),
        title_case(str_at(character, "world_type")),
        str_at(character, "region").to_uppercase(),
        str_at(character, "data_center").to_uppercase(),
    ));
    if let Some(guild) = character.get("character_guild_name").and_then(Value::as_str) {
        line.push(format!("Guild {guild}"));
    }
    if let Some(rate) = character.get("character_exp_rate").filter(|v| !v.is_null()) {
        line.push(format!("{}% EXP", fmt_num(rate)));
    }
    let _ = writeln!(out, "{}", line.join(" · "));
    let _ = writeln!(out, "{}", stats.describe());
    if let Some(notes) = character.get("notes").and_then(Value::as_str) {
        let _ = writeln!(out, "Owner's notes: {}", notes.replace('\n', " / "));
    }
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "Key: ★ star force (now/max) · Potential and Bonus (additional potential) lines abbreviated · \
         Flame = bonus stats (green) · Total = everything the item gives (base + enhancement + flame) · \
         IED = Ignore Enemy DEF · All = All Stats.{}",
        if stats.scored() { " Flame score = main stat + 4 × ATT + 10 × All%, ignoring secondary stats." } else { "" },
    );
    let _ = writeln!(
        out,
        "Every field, as JSON: /v1/characters/{id}, /v1/characters/{id}/stat, /v1/characters/{id}/item-equipment \
         (each with /history where recorded)."
    );

    let _ = writeln!(out);
    match stat {
        Some(stat) => stat_section(&mut out, stat),
        None => {
            let _ = writeln!(out, "## Stats\nNot recorded yet.");
        }
    }
    let _ = writeln!(out);
    match equipment {
        Some(equipment) => equipment_section(&mut out, equipment, &stats),
        None => {
            let _ = writeln!(out, "## Equipment\nNot recorded yet.");
        }
    }
    out
}

/// What the class cares about, for ordering and scoring an item's stats.
struct Stats {
    /// The class's primary stats, as option keys (`str`, `max_hp`, …) and labels.
    primary: Vec<(&'static str, &'static str)>,
    /// Its secondary stats.
    secondary: Vec<(&'static str, &'static str)>,
    /// `magic_power` for magic classes, else `attack_power`.
    attack: (&'static str, &'static str),
}

impl Stats {
    fn of(class: Option<&Class>) -> Self {
        let keys = |stats: &[MainStat]| stats.iter().map(|s| main_stat(*s)).collect();
        match class {
            Some(c) => Self {
                primary: keys(c.primary),
                secondary: keys(c.secondary),
                attack: if c.uses_magic_attack { ("magic_power", "MATT") } else { ("attack_power", "ATT") },
            },
            None => Self { primary: Vec::new(), secondary: Vec::new(), attack: ("attack_power", "ATT") },
        }
    }

    /// The flame score has a common form only for one primary stat that is
    /// not HP (Xenon and Demon Avenger have none).
    fn scored(&self) -> bool {
        matches!(self.primary.as_slice(), [(key, _)] if *key != "max_hp")
    }

    fn describe(&self) -> String {
        let names = |s: &[(&str, &'static str)]| s.iter().map(|(_, l)| *l).collect::<Vec<_>>().join("/");
        let mut d = format!("Main stat {}", names(&self.primary));
        if !self.secondary.is_empty() {
            let _ = write!(d, ", secondary {}", names(&self.secondary));
        }
        let _ = write!(d, "; attacks with {}.", self.attack.1);
        d
    }

    /// The flame score of an item's bonus stats.
    fn flame_score(&self, flame: &Map<String, Value>) -> Option<f64> {
        if !self.scored() {
            return None;
        }
        let at = |k: &str| flame.get(k).and_then(Value::as_f64).unwrap_or(0.0);
        Some(at(self.primary[0].0) + 4.0 * at(self.attack.0) + 10.0 * at("all_stat"))
    }
}

fn main_stat(s: MainStat) -> (&'static str, &'static str) {
    match s {
        MainStat::Str => ("str", "STR"),
        MainStat::Dex => ("dex", "DEX"),
        MainStat::Int => ("int", "INT"),
        MainStat::Luk => ("luk", "LUK"),
        MainStat::Hp => ("max_hp", "HP"),
    }
}

fn stat_section(out: &mut String, stat: &Value) {
    let _ = writeln!(out, "## Stats{}", captured(stat));
    let rows: [&[(&str, &str, Unit)]; 9] = [
        &[("combat_power", "Combat Power", Unit::Flat), ("stat_attack_max", "Stat attack (max)", Unit::Flat)],
        &[
            ("str", "STR", Unit::Flat),
            ("dex", "DEX", Unit::Flat),
            ("int", "INT", Unit::Flat),
            ("luk", "LUK", Unit::Flat),
        ],
        &[("hp", "HP", Unit::Flat), ("mp", "MP", Unit::Flat)],
        &[("attack_power", "ATT", Unit::Flat), ("magic_attack", "MATT", Unit::Flat)],
        &[
            ("damage", "Damage", Unit::Pct),
            ("boss_damage", "Boss", Unit::Pct),
            ("normal_damage", "Normal", Unit::Pct),
            ("final_damage", "Final Damage", Unit::Pct),
            ("ignore_defense", "IED", Unit::Pct),
            ("ignore_elemental_resistance", "IER", Unit::Pct),
        ],
        &[
            ("critical_rate", "Crit Rate", Unit::Pct),
            ("critical_damage", "Crit Damage", Unit::Pct),
            ("abnormal_status_damage", "Status Damage", Unit::Pct),
            ("weapon_mastery", "Mastery", Unit::Pct),
            ("attack_speed", "Attack Speed", Unit::Flat),
        ],
        &[
            ("buff_duration", "Buff Duration", Unit::Pct),
            ("cooldown_reduction_seconds", "Cooldown −s", Unit::Flat),
            ("cooldown_reduction_percent", "Cooldown −%", Unit::Pct),
            ("cooldown_skip", "Cooldown Skip", Unit::Pct),
            ("summon_duration", "Summon Duration", Unit::Pct),
        ],
        &[
            ("star_force", "Star Force", Unit::Flat),
            ("arcane_power", "Arcane Power", Unit::Flat),
            ("sacred_power", "Sacred Power", Unit::Flat),
        ],
        &[
            ("item_drop_rate", "Drop", Unit::Pct),
            ("mesos_obtained", "Meso", Unit::Pct),
            ("additional_exp", "EXP", Unit::Pct),
            ("stance", "Stance", Unit::Pct),
            ("status_resistance", "Status Resistance", Unit::Flat),
        ],
    ];
    let breakdowns = stat.get("breakdowns");
    for row in rows {
        let parts: Vec<String> = row
            .iter()
            .filter_map(|(key, label, unit)| {
                let v = stat.get(*key).filter(|v| v.as_f64().is_some_and(|n| n != 0.0))?;
                let mut s = format!("{label} {}{}", fmt_num(v), unit.suffix());
                if let Some(b) = breakdowns.and_then(|b| b.get(*key)).filter(|b| b.is_object()) {
                    let mut why = Vec::new();
                    if let Some(base) = b.get("base").filter(|v| !v.is_null()) {
                        why.push(format!("base {}", fmt_num(base)));
                    }
                    if let Some(pct) = b.get("percent").filter(|v| !v.is_null()) {
                        why.push(format!("{}%", fmt_num(pct)));
                    }
                    if let Some(flat) = b.get("flat").filter(|v| !v.is_null()) {
                        why.push(format!("+{} flat", fmt_num(flat)));
                    }
                    if !why.is_empty() {
                        let _ = write!(s, " ({})", why.join(", "));
                    }
                }
                Some(s)
            })
            .collect();
        if !parts.is_empty() {
            let _ = writeln!(out, "- {}", parts.join(" · "));
        }
    }
}

#[derive(Clone, Copy)]
enum Unit {
    Flat,
    Pct,
}

impl Unit {
    const fn suffix(self) -> &'static str {
        match self {
            Self::Flat => "",
            Self::Pct => "%",
        }
    }
}

/// Slots in the order the sheet lists them, with their labels.
const SLOTS: [(&str, &str); 30] = [
    ("weapon", "Weapon"),
    ("secondary", "Secondary"),
    ("emblem", "Emblem"),
    ("hat", "Hat"),
    ("top", "Top"),
    ("bottom", "Bottom"),
    ("shoes", "Shoes"),
    ("gloves", "Gloves"),
    ("cape", "Cape"),
    ("shoulder", "Shoulder"),
    ("belt", "Belt"),
    ("face-accessory", "Face"),
    ("eye-accessory", "Eye"),
    ("earrings", "Earrings"),
    ("pendant-1", "Pendant"),
    ("pendant-2", "Pendant 2"),
    ("ring-1", "Ring 1"),
    ("ring-2", "Ring 2"),
    ("ring-3", "Ring 3"),
    ("ring-4", "Ring 4"),
    ("pocket", "Pocket"),
    ("heart", "Heart"),
    ("badge", "Badge"),
    ("medal", "Medal"),
    ("totem-1", "Totem 1"),
    ("totem-2", "Totem 2"),
    ("totem-3", "Totem 3"),
    ("android", "Android"),
    ("familiar-manager", "Familiar Manager"),
    ("title", "Title"),
];

fn equipment_section(out: &mut String, equipment: &Value, stats: &Stats) {
    let items = equipment.get("item_equipment").and_then(Value::as_array).map(Vec::as_slice).unwrap_or_default();
    let _ = writeln!(out, "## Equipment{} · {} items", captured(equipment), items.len());
    let rank = |item: &Value| {
        let slot = str_at(item, "item_equipment_slot");
        SLOTS.iter().position(|(s, _)| *s == slot).unwrap_or(SLOTS.len())
    };
    let mut items: Vec<&Value> = items.iter().collect();
    items.sort_by_key(|i| rank(i));
    for item in &items {
        let _ = writeln!(out);
        item_lines(out, item, stats);
    }

    let mut sets: Vec<(&str, Vec<&str>)> = Vec::new();
    for item in &items {
        if let Some(set) = item.get("item_set_name").and_then(Value::as_str) {
            let label = slot_label(str_at(item, "item_equipment_slot"));
            match sets.iter_mut().find(|(name, _)| *name == set) {
                Some((_, slots)) => slots.push(label),
                None => sets.push((set, vec![label])),
            }
        }
    }
    if !sets.is_empty() {
        sets.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(b.0)));
        let _ = writeln!(out, "\n## Sets (pieces worn; set effects are not recorded yet)");
        for (name, slots) in sets {
            let _ = writeln!(out, "- {name}: {} ({})", slots.len(), slots.join(", "));
        }
    }
}

fn slot_label(slot: &str) -> &str {
    SLOTS.iter().find(|(s, _)| *s == slot).map_or(slot, |(_, l)| l)
}

fn item_lines(out: &mut String, item: &Value, stats: &Stats) {
    let mut head = format!("**{}: {}", slot_label(str_at(item, "item_equipment_slot")), str_at(item, "item_name"));
    let most = item.get("starforce_max").and_then(Value::as_u64).unwrap_or(0);
    if most > 0 {
        let now = item.get("starforce").and_then(Value::as_u64).unwrap_or(0);
        let _ = write!(head, " ({now}★/{most})");
    }
    head.push_str("**");
    if let Some(level) = item.pointer("/item_base_option/base_equipment_level").and_then(Value::as_u64) {
        let _ = write!(head, " · Lv {level}");
    }
    if let Some(set) = item.get("item_set_name").and_then(Value::as_str) {
        let _ = write!(head, " · {set}");
    }
    let _ = writeln!(out, "{head}");

    for (grade, prefix, label) in [
        ("potential_option_grade", "potential_option_", "Potential"),
        ("additional_potential_option_grade", "additional_potential_option_", "Bonus"),
    ] {
        let lines: Vec<String> = (1..=3)
            .filter_map(|n| item.get(format!("{prefix}{n}")).and_then(Value::as_str))
            .map(potential_line)
            .collect();
        let grade = item.get(grade).and_then(Value::as_str);
        if grade.is_none() && lines.is_empty() {
            continue;
        }
        let grade = grade.map_or_else(|| "?".to_owned(), title_case);
        let _ =
            writeln!(out, "- {label}: {grade} — {}", if lines.is_empty() { "?".to_owned() } else { lines.join(", ") });
    }

    if is_weapon_like(item)
        && let Some(base) = item.get("item_base_option").and_then(Value::as_object)
    {
        let parts = option_parts(base, stats, true);
        if !parts.is_empty() {
            let _ = writeln!(out, "- Base (sets the flame's ATT tier): {}", parts.join(", "));
        }
    }
    if let Some(flame) = item.get("item_add_option").and_then(Value::as_object).filter(|m| !m.is_empty()) {
        let parts = option_parts(flame, stats, false);
        if !parts.is_empty() {
            let score = match stats.flame_score(flame) {
                Some(s) if !is_weapon_like(item) => format!(" (score {})", fmt_f64(s)),
                _ => String::new(),
            };
            let _ = writeln!(out, "- Flame{score}: {}", parts.join(", "));
        }
    }
    if let Some(ex) = item.get("item_exceptional_option").and_then(Value::as_object).filter(|m| !m.is_empty()) {
        let _ = writeln!(out, "- Exceptional: {}", option_parts(ex, stats, false).join(", "));
    }

    let mut extra = Vec::new();
    if let Some(n) = item.get("scroll_upgrade").and_then(Value::as_u64) {
        extra.push(format!("{n} scrolled"));
    }
    if let Some(n) = item.get("scroll_upgradeable_count").and_then(Value::as_u64) {
        extra.push(format!("{n} slots left"));
    }
    if let Some(n) = item.get("scroll_resilience_count").and_then(Value::as_u64) {
        extra.push(format!("{n} restorable"));
    }
    if item.get("golden_hammer_flag").and_then(Value::as_bool) == Some(true) {
        extra.push("hammered".to_owned());
    }
    if let Some(n) = item.get("cuttable_count").and_then(Value::as_u64) {
        extra.push(format!("{n} karma uses"));
    }
    if !extra.is_empty() {
        let _ = writeln!(out, "- Scrolls: {}", extra.join(", "));
    }
    if let Some(soul) = item.get("soul_name").and_then(Value::as_str) {
        let option = item.get("soul_option").and_then(Value::as_str).map(|o| format!(" — {o}")).unwrap_or_default();
        let _ = writeln!(out, "- Soul: {soul}{option}");
    }

    if let Some(total) = item.get("item_total_option").and_then(Value::as_object) {
        let parts = option_parts(total, stats, true);
        if !parts.is_empty() {
            let _ = writeln!(out, "- Total: {}", parts.join(", "));
        }
    }
}

/// Weapons, secondaries and emblems: flames there are judged by ATT tier, not score.
fn is_weapon_like(item: &Value) -> bool {
    matches!(str_at(item, "item_equipment_slot"), "weapon" | "secondary" | "emblem")
}

/// An item option's non-zero stats, the class's own first. `relevant_only`
/// drops what does not raise the class's damage (off stats, DEF, movement).
fn option_parts(option: &Map<String, Value>, stats: &Stats, relevant_only: bool) -> Vec<String> {
    let mut keys: Vec<(&str, &str, Unit)> = Vec::new();
    for (key, label) in stats.primary.iter().chain(&stats.secondary) {
        keys.push((key, label, Unit::Flat));
    }
    keys.push((stats.attack.0, stats.attack.1, Unit::Flat));
    keys.extend([
        ("boss_damage", "Boss", Unit::Pct),
        ("ignore_monster_armor", "IED", Unit::Pct),
        ("damage", "Dmg", Unit::Pct),
        ("all_stat", "All", Unit::Pct),
    ]);
    let hp_class = stats.primary.iter().any(|(k, _)| *k == "max_hp");
    let rest: [(&str, &str, Unit); 13] = [
        ("str", "STR", Unit::Flat),
        ("dex", "DEX", Unit::Flat),
        ("int", "INT", Unit::Flat),
        ("luk", "LUK", Unit::Flat),
        ("attack_power", "ATT", Unit::Flat),
        ("magic_power", "MATT", Unit::Flat),
        ("max_hp", "HP", Unit::Flat),
        ("max_mp", "MP", Unit::Flat),
        ("max_hp_rate", "HP", Unit::Pct),
        ("max_mp_rate", "MP", Unit::Pct),
        ("armor", "DEF", Unit::Flat),
        ("speed", "Speed", Unit::Flat),
        ("jump", "Jump", Unit::Flat),
    ];
    for (key, label, unit) in rest {
        if keys.iter().any(|(k, _, _)| *k == key) {
            continue;
        }
        let keep = !relevant_only || (hp_class && (key == "max_hp" || key == "max_hp_rate"));
        if keep {
            keys.push((key, label, unit));
        }
    }
    let mut parts: Vec<String> = keys
        .iter()
        .filter_map(|(key, label, unit)| {
            let v = option.get(*key)?;
            (v.as_f64()? != 0.0).then(|| format!("{}{} {label}", fmt_num(v), unit.suffix()))
        })
        .collect();
    if !relevant_only && let Some(n) = option.get("equipment_level_decrease").and_then(Value::as_u64).filter(|n| *n > 0)
    {
        parts.push(format!("−{n} level"));
    }
    parts
}

/// A potential line as players write it: `STR: +9%` is `9% STR`,
/// `Boss Damage +30%` is `30% Boss`. Lines of any other shape are kept.
fn potential_line(line: &str) -> String {
    let Some(plus) = line.rfind('+') else { return line.to_owned() };
    let (name, value) = (line[..plus].trim().trim_end_matches(':').trim(), &line[plus + 1..]);
    let number = value.trim_end_matches('%');
    if name.is_empty() || number.is_empty() || !number.chars().all(|c| c.is_ascii_digit() || c == '.') {
        return line.to_owned();
    }
    let short = match name {
        "All Stats" => "All",
        "Max HP" => "HP",
        "Max MP" => "MP",
        "Boss Damage" | "Boss Monster Damage" => "Boss",
        "Ignore Defense" | "Ignore Enemy DEF" | "Monster DEF Ignored" => "IED",
        "Attack Power" | "ATT" => "ATT",
        "Magic ATT" | "Magic Attack" => "MATT",
        "Damage" | "Total Damage" => "Dmg",
        "Critical Damage" => "Crit Dmg",
        "Critical Rate" => "Crit Rate",
        "Mesos Obtained" => "Meso",
        "Item Drop Rate" => "Drop",
        other => other,
    };
    format!("{value} {short}")
}

fn captured(window: &Value) -> String {
    window
        .get("captured_at")
        .and_then(Value::as_str)
        .map(|t| format!(" (captured {})", t.get(..10).unwrap_or(t)))
        .unwrap_or_default()
}

fn str_at<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

fn num_at(v: &Value, key: &str) -> String {
    v.get(key).map(fmt_num).unwrap_or_default()
}

fn title_case(s: &str) -> String {
    let mut chars = s.chars();
    chars.next().map(|c| c.to_uppercase().chain(chars).collect()).unwrap_or_default()
}

/// A JSON number as the game shows it: thousands separated, no trailing zeros.
fn fmt_num(v: &Value) -> String {
    match v {
        Value::Number(n) => match (n.as_i64(), n.as_f64()) {
            (Some(i), _) => group(i),
            (None, Some(f)) => fmt_f64(f),
            _ => n.to_string(),
        },
        Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

#[allow(clippy::cast_possible_truncation, reason = "checked to be a whole number well inside i64")]
fn fmt_f64(f: f64) -> String {
    if f.fract() == 0.0 && f.abs() < 1e15 {
        return group(f as i64);
    }
    let s = format!("{f:.3}");
    s.trim_end_matches('0').trim_end_matches('.').to_owned()
}

fn group(i: i64) -> String {
    let digits = i.unsigned_abs().to_string();
    let mut out = String::new();
    for (n, c) in digits.chars().enumerate() {
        if n > 0 && (digits.len() - n).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    if i < 0 { format!("-{out}") } else { out }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn potential_lines_read_as_players_write_them() {
        assert_eq!(potential_line("STR: +9%"), "9% STR");
        assert_eq!(potential_line("All Stats +6%"), "6% All");
        assert_eq!(potential_line("Boss Damage +30%"), "30% Boss");
        assert_eq!(potential_line("Max MP +125"), "125 MP");
        assert_eq!(potential_line("Critical Damage +8%"), "8% Crit Dmg");
        assert_eq!(
            potential_line("20% chance to recover 370 HP when attacking."),
            "20% chance to recover 370 HP when attacking."
        );
        assert_eq!(potential_line("Skill Cooldown -1 sec"), "Skill Cooldown -1 sec");
    }

    #[test]
    fn numbers() {
        assert_eq!(fmt_num(&json!(34_254_924)), "34,254,924");
        assert_eq!(fmt_num(&json!(145.38)), "145.38");
        assert_eq!(fmt_num(&json!(6.0)), "6");
        assert_eq!(fmt_num(&json!(-1200)), "-1,200");
    }

    #[test]
    fn an_item_flattens_to_a_few_lines() {
        let stats = Stats::of(class::find("hero"));
        let mut out = String::new();
        item_lines(
            &mut out,
            &json!({
                "item_equipment_slot": "gloves",
                "item_name": "Arcane Umbra Knight Gloves",
                "item_set_name": "Arcane Umbra Set (Warrior)",
                "starforce": 17,
                "starforce_max": 30,
                "item_total_option": { "str": 236, "dex": 110, "int": 24, "attack_power": 41, "armor": 584 },
                "item_base_option": { "str": 40, "dex": 40, "attack_power": 9, "armor": 250, "base_equipment_level": 200 },
                "item_add_option": { "str": 126, "int": 24, "max_hp": 2400, "all_stat": 6.0, "equipment_level_decrease": 20 },
                "potential_option_grade": "legendary",
                "potential_option_1": "Critical Damage +8%",
                "potential_option_2": "STR: +9%",
            }),
            &stats,
        );
        assert_eq!(
            out,
            "**Gloves: Arcane Umbra Knight Gloves (17★/30)** · Lv 200 · Arcane Umbra Set (Warrior)\n\
             - Potential: Legendary — 8% Crit Dmg, 9% STR\n\
             - Flame (score 186): 126 STR, 6% All, 24 INT, 2,400 HP, −20 level\n\
             - Total: 236 STR, 110 DEX, 41 ATT\n"
        );
    }

    #[test]
    fn a_sheet_without_windows_says_so() {
        let character = json!({
            "id": "chr_1", "character_name": "Lutoren", "character_level": 275, "character_class": "Ren",
            "character_class_id": "ren", "world_name": "Kronos", "world_type": "heroic", "region": "gms",
            "data_center": "na", "character_guild_name": null, "character_exp_rate": 59.256,
        });
        let sheet = render(&character, None, None);
        assert!(sheet.starts_with("# Lutoren\nLv. 275 Ren · Kronos (Heroic, GMS NA) · 59.256% EXP\n"), "{sheet}");
        assert!(sheet.contains("## Stats\nNot recorded yet.") && sheet.contains("## Equipment\nNot recorded yet."));
    }
}
