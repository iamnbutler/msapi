// The reference msapi client. Plain fetch calls to /v1; no framework.

const app = document.getElementById("app");
const sessionNav = document.getElementById("session");
const TOKEN_KEY = "msapi.session";

// ---------- session ----------

function loadSession() {
  try {
    const s = JSON.parse(localStorage.getItem(TOKEN_KEY) || "null");
    if (s && Date.parse(s.expires_at) > Date.now()) return s;
  } catch {}
  return null;
}

function saveSession(s) {
  try {
    if (s) localStorage.setItem(TOKEN_KEY, JSON.stringify(s));
    else localStorage.removeItem(TOKEN_KEY);
  } catch {}
}

let session = loadSession();

// ---------- API ----------

class ApiError extends Error {
  constructor(status, body) {
    super(body?.error?.message || `request failed (${status})`);
    this.status = status;
    this.body = body;
  }
}

async function api(method, path, body) {
  const headers = {};
  if (session) headers.authorization = `Bearer ${session.token}`;
  if (body !== undefined) headers["content-type"] = "application/json";
  let res;
  // A cold container answers 503 while it boots and restores; wait it out.
  for (let attempt = 0; ; attempt++) {
    res = await fetch(path, { method, headers, body: body === undefined ? undefined : JSON.stringify(body) });
    if (res.status !== 503 || attempt >= 12) break;
    await new Promise((r) => setTimeout(r, 1000 * Number(res.headers.get("retry-after") || 5)));
  }
  const text = await res.text();
  const data = text ? JSON.parse(text) : null;
  if (res.status === 401 && session && !path.startsWith("/v1/auth/")) {
    saveSession((session = null));
    go("#/");
  }
  if (!res.ok) throw new ApiError(res.status, data);
  return data;
}

const ref = {};
async function reference(kind) {
  ref[kind] ??= api("GET", `/v1/ref/${kind}`).then((r) => r[kind]);
  return ref[kind];
}

// ---------- passkeys ----------

const b64 = {
  decode(s) {
    const bin = atob(s.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((s.length + 3) % 4));
    return Uint8Array.from(bin, (c) => c.charCodeAt(0)).buffer;
  },
  encode(buf) {
    let bin = "";
    for (const b of new Uint8Array(buf)) bin += String.fromCharCode(b);
    return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  },
};

function creationOptions(o) {
  if (PublicKeyCredential.parseCreationOptionsFromJSON) return PublicKeyCredential.parseCreationOptionsFromJSON(o);
  return {
    ...o,
    challenge: b64.decode(o.challenge),
    user: { ...o.user, id: b64.decode(o.user.id) },
    excludeCredentials: (o.excludeCredentials || []).map((c) => ({ ...c, id: b64.decode(c.id) })),
  };
}

function requestOptions(o) {
  if (PublicKeyCredential.parseRequestOptionsFromJSON) return PublicKeyCredential.parseRequestOptionsFromJSON(o);
  return { ...o, challenge: b64.decode(o.challenge), allowCredentials: [] };
}

function credentialJSON(c) {
  if (typeof c.toJSON === "function") return c.toJSON();
  const r = c.response;
  const response = { clientDataJSON: b64.encode(r.clientDataJSON) };
  if (r.attestationObject) response.attestationObject = b64.encode(r.attestationObject);
  if (r.authenticatorData) response.authenticatorData = b64.encode(r.authenticatorData);
  if (r.signature) response.signature = b64.encode(r.signature);
  if (r.userHandle) response.userHandle = b64.encode(r.userHandle);
  return { id: c.id, rawId: b64.encode(c.rawId), type: c.type, response };
}

async function signUp(displayName) {
  const { publicKey } = await api("POST", "/v1/auth/passkey/register/start", { display_name: displayName });
  const credential = await navigator.credentials.create({ publicKey: creationOptions(publicKey) });
  return api("POST", "/v1/auth/passkey/register/finish", { credential: credentialJSON(credential) });
}

async function signIn() {
  const { publicKey } = await api("POST", "/v1/auth/passkey/login/start", {});
  const credential = await navigator.credentials.get({ publicKey: requestOptions(publicKey) });
  return api("POST", "/v1/auth/passkey/login/finish", { credential: credentialJSON(credential) });
}

// ---------- rendering helpers ----------

function h(tag, attrs = {}, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v == null || v === false) continue;
    if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (k === "class") el.className = v;
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat(Infinity)) if (c != null && c !== false) el.append(c.nodeType ? c : String(c));
  return el;
}

function notice(kind, text) {
  return h("p", { class: `notice ${kind}`, role: kind === "error" ? "alert" : "status" }, text);
}

function errorText(err) {
  if (err?.name === "NotAllowedError") return "The passkey prompt was cancelled or timed out.";
  const issues = err?.body?.error?.details?.issues;
  if (Array.isArray(issues) && issues.length) return `${err.message}: ${issues.map((i) => i.message || JSON.stringify(i)).join("; ")}`;
  return err?.message || String(err);
}

/** Wires a form: disables it while `action` runs and shows any error above it. */
function bind(form, action) {
  form.addEventListener("submit", async (e) => {
    e.preventDefault();
    const button = form.querySelector("button[type=submit]");
    form.querySelector(".notice")?.remove();
    button.disabled = true;
    try {
      await action(new FormData(form));
    } catch (err) {
      form.prepend(notice("error", errorText(err)));
    } finally {
      button.disabled = false;
    }
  });
  return form;
}

function fmtDate(iso) {
  return iso ? new Date(iso).toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" }) : "";
}

const nf = new Intl.NumberFormat();
function fmtNum(v) {
  if (v == null) return "—";
  return typeof v === "number" ? nf.format(v) : String(v);
}

function go(hash) {
  // Character pages live at /characters/{id}; every other page is a hash on /.
  if (location.pathname !== "/") location.assign(`/${hash}`);
  else if (location.hash === hash) render();
  else location.hash = hash;
}

function renderSession() {
  sessionNav.replaceChildren();
  if (!session) {
    if (location.pathname.startsWith("/characters/")) sessionNav.append(h("a", { href: "/#/" }, "Sign in"));
    return;
  }
  sessionNav.append(
    h("a", { href: "/#/tokens" }, "API tokens"),
    h("span", {}, session.display_name),
    h("button", {
      class: "quiet",
      onclick: async () => {
        try { await api("DELETE", `/v1/tokens/${session.token_id}`); } catch {}
        saveSession((session = null));
        go("#/");
      },
    }, "Sign out"),
  );
}

// ---------- pages ----------

function welcome() {
  const supported = window.PublicKeyCredential !== undefined;
  const signUpForm = bind(
    h("form", {},
      h("label", {}, "Display name", h("input", { name: "name", required: true, maxlength: 64, autocomplete: "nickname", placeholder: "e.g. Nate" })),
      h("button", { type: "submit" }, "Create account with a passkey"),
    ),
    async (data) => {
      const s = await signUp(String(data.get("name")).trim());
      saveSession((session = s));
      go("#/");
    },
  );
  const signInForm = bind(
    h("form", {}, h("button", { type: "submit", class: "quiet" }, "Sign in with a passkey")),
    async () => {
      const s = await signIn();
      saveSession((session = s));
      go("#/");
    },
  );
  return h("section", { class: "hero" },
    h("h1", {}, "Your MapleStory characters, in one place."),
    h("p", { class: "sub" }, "Add your accounts and characters, then log their stats and equipment over time. Tools you trust can read them through the msapi API with tokens you control."),
    supported ? null : notice("error", "This browser does not support passkeys."),
    h("div", { class: "panel" }, h("h2", {}, "New here"), signUpForm),
    h("div", { class: "panel" }, h("h2", {}, "Been here before"), signInForm),
  );
}

async function home() {
  const [{ account_list: accounts }, regions] = await Promise.all([api("GET", "/v1/accounts"), reference("regions")]);
  const form = bind(
    h("form", {},
      h("div", { class: "fields" },
        h("label", {}, "Region",
          h("select", { name: "region" }, regions.map((r) => h("option", { value: r.region, disabled: !r.supported }, r.name + (r.supported ? "" : " (soon)"))))),
        h("label", {}, "Label", h("input", { name: "label", maxlength: 100, placeholder: "main" })),
      ),
      h("button", { type: "submit" }, "Add account"),
    ),
    async (data) => {
      const account = await api("POST", "/v1/accounts", { region: data.get("region"), label: data.get("label") || null });
      go(`#/accounts/${account.id}`);
    },
  );
  return h("section", {},
    h("h1", {}, "Accounts"),
    h("p", { class: "sub" }, "One account per region login. Characters live under the account they are on."),
    h("div", { class: "grid" },
      h("div", { class: "panel" },
        accounts.length
          ? h("ul", { class: "list" }, accounts.map((a) =>
              h("li", {}, h("a", { href: `/#/accounts/${a.id}` },
                h("span", {}, a.label || a.region.toUpperCase()),
                h("span", { class: "meta" }, `${a.region.toUpperCase()} · ${a.character_list.length} character${a.character_list.length === 1 ? "" : "s"}`)))))
          : h("p", { class: "empty" }, "No accounts yet. Add your first one.")),
      h("div", { class: "panel" }, h("h2", {}, "Add an account"), form),
    ),
  );
}

async function accountPage(id) {
  const [account, worlds, classes] = await Promise.all([api("GET", `/v1/accounts/${id}`), reference("worlds"), reference("classes")]);
  const regionWorlds = worlds.filter((w) => w.region === account.region);
  const form = bind(
    h("form", {},
      h("div", { class: "fields" },
        h("label", {}, "Name", h("input", { name: "character_name", required: true, maxlength: 12, autocomplete: "off" })),
        h("label", {}, "World", h("select", { name: "world_name", required: true }, regionWorlds.map((w) => h("option", { value: w.name }, w.name)))),
        h("label", {}, "Class",
          h("select", { name: "character_class", required: true },
            [...classes].sort((a, b) => a.name.localeCompare(b.name)).map((c) => h("option", { value: c.name }, c.name)))),
        h("label", {}, "Level", h("input", { name: "character_level", type: "number", min: 1, max: 300, required: true })),
      ),
      h("button", { type: "submit" }, "Add character"),
    ),
    async (data) => {
      const c = await api("POST", `/v1/accounts/${id}/characters`, {
        character_name: data.get("character_name"),
        world_name: data.get("world_name"),
        character_class: data.get("character_class"),
        character_level: Number(data.get("character_level")),
      });
      location.assign(`/characters/${c.id}`);
    },
  );
  return h("section", {},
    h("div", { class: "crumbs" }, h("a", { href: "/#/" }, "Accounts"), " / "),
    h("h1", {}, account.label || account.region.toUpperCase()),
    h("p", { class: "sub" }, `${account.region.toUpperCase()} · added ${fmtDate(account.created_at)}`),
    h("div", { class: "grid" },
      h("div", { class: "panel" },
        h("h2", {}, "Characters"),
        account.character_list.length
          ? h("ul", { class: "list" }, account.character_list.map((c) =>
              h("li", {}, h("a", { href: `/characters/${c.id}` },
                h("span", {}, c.character_name),
                h("span", { class: "meta" }, `Lv. ${c.character_level} ${c.character_class} · ${c.world_name}`)))))
          : h("p", { class: "empty" }, "No characters on this account yet.")),
      h("div", { class: "panel" }, h("h2", {}, "Add a character"), form),
    ),
  );
}

// The stat window fields the form offers, in the order the game shows them.
const STAT_FIELDS = [
  ["combat_power", "Combat Power", "int"],
  ["stat_attack_min", "Stat attack (min)", "int"],
  ["stat_attack_max", "Stat attack (max)", "int"],
  ["hp", "HP", "int"],
  ["mp", "MP", "int"],
  ["str", "STR", "int"],
  ["dex", "DEX", "int"],
  ["int", "INT", "int"],
  ["luk", "LUK", "int"],
  ["damage", "Damage %", "pct"],
  ["boss_damage", "Boss Damage %", "pct"],
  ["final_damage", "Final Damage %", "pct"],
  ["ignore_defense", "Ignore Defense %", "pct"],
  ["critical_rate", "Critical Rate %", "pct"],
  ["critical_damage", "Critical Damage %", "pct"],
  ["attack_power", "Attack Power", "int"],
  ["magic_attack", "Magic Attack", "int"],
  ["star_force", "Star Force", "int"],
  ["arcane_power", "Arcane Power", "int"],
  ["sacred_power", "Sacred Power", "int"],
];

// ---------- equipment ----------

// Where each slot sits in the game's equipment window: [slot, row, column].
const SLOT_GRID = [
  ["ring-1", 1, 1], ["ring-2", 2, 1], ["ring-3", 3, 1], ["ring-4", 4, 1], ["belt", 5, 1], ["pocket", 6, 1],
  ["face-accessory", 1, 2], ["eye-accessory", 2, 2], ["earrings", 3, 2], ["pendant-1", 4, 2], ["pendant-2", 5, 2], ["familiar-manager", 6, 2],
  ["weapon", 5, 3], ["secondary", 5, 4], ["emblem", 5, 5],
  ["hat", 1, 6], ["top", 2, 6], ["bottom", 3, 6], ["shoulder", 4, 6], ["android", 5, 6],
  ["cape", 1, 7], ["gloves", 2, 7], ["shoes", 3, 7], ["medal", 4, 7], ["heart", 5, 7], ["badge", 6, 7],
];

const SLOT_LABEL = {
  "ring-1": "Ring", "ring-2": "Ring", "ring-3": "Ring", "ring-4": "Ring", belt: "Belt", pocket: "Pocket",
  "face-accessory": "Face", "eye-accessory": "Eye", earrings: "Earrings", "pendant-1": "Pendant", "pendant-2": "Pendant",
  "familiar-manager": "Familiar", weapon: "Weapon", secondary: "Secondary", emblem: "Emblem", hat: "Hat", top: "Top",
  bottom: "Bottom", shoulder: "Shoulder", android: "Android", cape: "Cape", gloves: "Gloves", shoes: "Shoes",
  medal: "Medal", heart: "Heart", badge: "Badge",
};

// Tooltip stat lines in the game's order: [field, label, percent?].
const OPTION_LINES = [
  ["str", "STR"], ["dex", "DEX"], ["int", "INT"], ["luk", "LUK"],
  ["max_hp", "Max HP"], ["max_mp", "Max MP"],
  ["attack_power", "Attack Power"], ["magic_power", "Magic ATT"], ["armor", "Defense"],
  ["speed", "Speed"], ["jump", "Jump"],
  ["boss_damage", "Boss Damage", true], ["ignore_monster_armor", "Enemy DEF Ignored", true],
  ["damage", "Damage", true], ["all_stat", "All Stats", true], ["max_hp_rate", "Max HP", true], ["max_mp_rate", "Max MP", true],
];

// The tooltip's colours: [field, class].
const OPTION_PARTS = [
  ["item_base_option", "base"],
  ["item_enhancement_option", "enh"],
  ["item_add_option", "add"],
  ["item_exceptional_option", "exc"],
];

const GRADE_LABEL = { rare: "Rare", epic: "Epic", unique: "Unique", legendary: "Legendary" };

function fmtOpt(v, pct) {
  const n = Number(v);
  return (Number.isInteger(n) ? nf.format(n) : String(n)) + (pct ? "%" : "");
}

function stars(item) {
  const max = item.starforce_max ?? (item.starforce ? Math.max(item.starforce, 15) : 0);
  if (!max) return null;
  const filled = item.starforce ?? 0;
  const rows = [];
  for (let r = 0; r < max; r += 15) {
    const row = [];
    for (let i = r; i < Math.min(r + 15, max); i += 5) {
      row.push(h("span", { class: "group" }, Array.from({ length: Math.min(5, max - i) }, (_, k) => h("span", { class: i + k < filled ? "star on" : "star" }, "★"))));
    }
    rows.push(h("div", { class: "stars" }, row));
  }
  return h("div", { "aria-label": `${filled} of ${max} stars` }, rows);
}

function tooltip(item) {
  const total = item.item_total_option || {};
  const lines = OPTION_LINES.filter(([key]) => total[key] != null || OPTION_PARTS.some(([p]) => item[p]?.[key] != null)).map(([key, label, pct]) => {
    const parts = OPTION_PARTS.filter(([p]) => item[p]?.[key] != null);
    const broken = parts.length > 1 || parts.some(([p]) => p !== "item_base_option");
    return h("div", { class: broken ? "line up" : "line" },
      `${label}: `, total[key] != null ? `+${fmtOpt(total[key], pct)}` : "?",
      broken
        ? [" (", parts.map(([p, cls], i) => h("span", { class: cls }, (i ? " +" : "") + fmtOpt(item[p][key], pct))), ")"]
        : null);
  });
  const level = item.item_base_option?.base_equipment_level;
  const decrease = item.item_add_option?.equipment_level_decrease;
  const potential = (grade, prefix, title) => {
    const opts = [1, 2, 3].map((n) => item[`${prefix}_${n}`]).filter(Boolean);
    if (!grade && !opts.length) return null;
    return h("div", { class: `pot ${grade || ""}` },
      h("div", { class: "pot-title" }, title, grade ? ` (${GRADE_LABEL[grade]})` : ""),
      opts.map((o) => h("div", {}, o)));
  };
  return h("div", { class: "tip" },
    stars(item),
    icon(item, "tip-icon"),
    h("div", { class: "tip-name" }, item.item_name, item.scroll_upgrade ? ` (+${item.scroll_upgrade})` : ""),
    item.item_set_name ? h("div", { class: "tip-set" }, item.item_set_name) : null,
    h("div", { class: "tip-meta" },
      [item.item_equipment_part, level != null ? `Req Lv. ${decrease ? `${level - decrease} (${level} - ${decrease})` : level}` : null].filter(Boolean).join(" · ")),
    lines.length ? h("div", { class: "tip-stats" }, lines) : null,
    item.scroll_upgradeable_count != null ? h("div", { class: "line" }, `Remaining Enhancements: ${item.scroll_upgradeable_count}`) : null,
    potential(item.potential_option_grade, "potential_option", "Potential"),
    potential(item.additional_potential_option_grade, "additional_potential_option", "Bonus Potential"),
    item.soul_name ? h("div", { class: "pot" }, h("div", { class: "pot-title" }, item.soul_name), item.soul_option ? h("div", {}, item.soul_option) : null) : null,
    item.item_description ? h("p", { class: "tip-desc" }, item.item_description) : null,
    item.notes ? h("p", { class: "tip-desc" }, item.notes) : null,
  );
}

/** An item's icon from /assets, or null when it has none. */
function icon(item, cls) {
  if (!item.item_icon) return null;
  return h("img", { class: cls, src: `/assets/${item.item_icon}`, alt: "", loading: "lazy", decoding: "async" });
}

function equipmentPanel(c, snapshot) {
  const id = c.id;
  // Only the owner is sent `account_id`.
  const owner = c.account_id != null;
  const equipment = snapshot?.equipment ?? null;
  const bySlot = new Map((equipment?.item_equipment || []).map((it) => [it.item_equipment_slot, it]));
  const detail = h("div", { class: "eq-detail" }, h("p", { class: "empty" }, bySlot.size ? "Pick an item to see its tooltip." : "No equipment logged yet."));
  let selected = null;
  const cells = SLOT_GRID.map(([slot, row, col]) => {
    const item = bySlot.get(slot);
    const cell = h(item ? "button" : "div", {
      type: item ? "button" : null,
      class: `eq-slot${item ? " filled" : ""} ${item?.potential_option_grade || ""}`,
      style: `grid-row:${row};grid-column:${col}`,
      title: item ? item.item_name : SLOT_LABEL[slot],
      "aria-label": item ? item.item_name : null,
      "aria-pressed": item ? "false" : null,
    },
      item
        ? [icon(item, "eq-icon") ?? h("span", { class: "eq-name" }, item.item_name),
           item.starforce ? h("span", { class: "eq-sf" }, `★${item.starforce}`) : null]
        : h("span", { class: "eq-empty" }, SLOT_LABEL[slot]));
    if (item) {
      cell.addEventListener("click", () => {
        selected?.setAttribute("aria-pressed", "false");
        selected = cell;
        cell.setAttribute("aria-pressed", "true");
        detail.replaceChildren(tooltip(item));
      });
    }
    return cell;
  });
  const grid = h("div", { class: "eq-window" }, cells,
    h("div", { class: "eq-figure", style: "grid-row:1/5;grid-column:3/6" },
      c.character_image ? h("img", { src: c.character_image, alt: "" }) : null,
      h("span", {}, c.character_name), h("span", { class: "meta" }, `Lv. ${c.character_level} ${c.character_class}`)));

  const importForm = bind(
    h("form", {},
      h("p", { class: "meta" }, "Paste an equipment window as JSON (", h("code", {}, '{"item_equipment": […]}'), "); see ", h("a", { href: "/v1/docs" }, "the API guide"), ". Saving replaces the whole window; the old one stays in history."),
      h("textarea", { name: "json", rows: 6, spellcheck: "false", class: "mono", placeholder: '{"item_equipment": []}' }),
      h("button", { type: "submit" }, "Save equipment"),
    ),
    async (data) => {
      let body;
      try { body = JSON.parse(String(data.get("json"))); } catch { throw new Error("That is not valid JSON."); }
      const res = await api("PUT", `/v1/characters/${id}/item-equipment`, body);
      sessionStorage.setItem("msapi.flash", JSON.stringify(res.warnings || []));
      render();
    },
  );

  return h("div", { class: "panel" },
    h("h2", {}, "Equipment"),
    h("div", { class: "eq" }, grid, detail),
    equipment ? h("p", { class: "meta" }, `Captured ${fmtDate(equipment.captured_at)}`) : null,
    owner ? h("details", {}, h("summary", {}, "Record equipment"), importForm) : null,
  );
}

async function characterPage(id) {
  const [c, latest, history, equipment] = await Promise.all([
    api("GET", `/v1/characters/${id}`),
    api("GET", `/v1/characters/${id}/stat`),
    api("GET", `/v1/characters/${id}/stat/history?limit=20`),
    api("GET", `/v1/characters/${id}/item-equipment`),
  ]);
  const current = latest.snapshot?.stat ?? latest.stat ?? null;
  const result = h("div");
  const owner = c.account_id != null;
  const isPublic = c.visibility === "public";

  const visibility = bind(
    h("form", { class: "visibility" },
      h("p", {}, isPublic
        ? "Public: anyone with the link can see this character, its stats and its equipment. Your notes and accounts stay private."
        : "Private: only you can see this character."),
      h("button", { type: "submit", class: "quiet" }, isPublic ? "Make private" : "Make public"),
    ),
    async () => {
      await api("PATCH", `/v1/characters/${id}`, { visibility: isPublic ? "private" : "public" });
      render();
    },
  );

  const form = bind(
    h("form", {},
      h("p", { class: "meta" }, "Type what the stat window shows. Leave a box empty if you did not see it; empty is not zero."),
      h("div", { class: "fields" },
        STAT_FIELDS.map(([key, label, kind]) =>
          h("label", {}, label, h("input", {
            name: key,
            inputmode: "decimal",
            type: "number",
            step: kind === "pct" ? "0.01" : "1",
            min: 0,
            value: current?.[key] ?? "",
          })))),
      h("button", { type: "submit" }, "Log stats"),
    ),
    async (data) => {
      const body = {};
      for (const [key, , kind] of STAT_FIELDS) {
        const raw = String(data.get(key) ?? "").trim();
        if (raw !== "") body[key] = kind === "pct" ? Number(raw) : Number.parseInt(raw, 10);
      }
      if (!Object.keys(body).length) throw new Error("Fill in at least one stat.");
      const res = await api("PUT", `/v1/characters/${id}/stat`, body);
      sessionStorage.setItem("msapi.flash", JSON.stringify(res.warnings || []));
      render();
    },
  );

  let flash = null;
  try { flash = JSON.parse(sessionStorage.getItem("msapi.flash") || "null"); sessionStorage.removeItem("msapi.flash"); } catch {}
  if (flash) {
    result.append(flash.length
      ? notice("warn", `Saved, with warnings: ${flash.map((w) => w.message || JSON.stringify(w)).join("; ")}`)
      : notice("ok", "Saved."));
  }

  const shown = STAT_FIELDS.filter(([key]) => current?.[key] != null);
  const rows = history.history || [];
  return h("section", {},
    owner ? h("div", { class: "crumbs" }, h("a", { href: "/#/" }, "Accounts"), " / ", h("a", { href: `/#/accounts/${c.account_id}` }, "Account"), " / ") : null,
    h("h1", {}, c.character_name),
    h("p", { class: "sub" }, `Lv. ${c.character_level} ${c.character_class} · ${c.world_name} (${c.world_type})`),
    result,
    owner ? h("div", { class: "panel" }, h("h2", {}, "Who can see this"), visibility) : null,
    h("div", { class: "panel" },
      h("h2", {}, "Current stats"),
      current
        ? [h("dl", { class: "stats" }, shown.map(([key, label]) => h("div", {}, h("dt", {}, label), h("dd", {}, fmtNum(current[key]))))),
           h("p", { class: "meta" }, `Captured ${fmtDate(current.captured_at)}`)]
        : h("p", { class: "empty" }, "No stats logged yet.")),
    equipmentPanel(c, equipment.equipment ? equipment : null),
    owner ? h("div", { class: "panel" }, h("h2", {}, "Log the stat window"), form) : null,
    h("div", { class: "panel" },
      h("h2", {}, "History"),
      rows.length
        ? h("div", { class: "scroll" }, h("table", {},
            h("thead", {}, h("tr", {}, h("th", {}, "Captured"), h("th", {}, "Combat Power"), h("th", {}, "Final Damage %"), h("th", {}, "Boss %"), h("th", {}, "IED %"))),
            h("tbody", {}, rows.map((r) => h("tr", {},
              h("td", {}, fmtDate(r.stat.captured_at)),
              h("td", {}, fmtNum(r.stat.combat_power)),
              h("td", {}, fmtNum(r.stat.final_damage)),
              h("td", {}, fmtNum(r.stat.boss_damage)),
              h("td", {}, fmtNum(r.stat.ignore_defense)))))))
        : h("p", { class: "empty" }, owner ? "Every save is kept; your history will show here." : "No history yet.")),
  );
}

// Every scope a token can hold, with what it lets the holder do.
const SCOPES = [
  ["accounts:read", "Read accounts"],
  ["accounts:write", "Add and edit accounts"],
  ["characters:read", "Read characters, stats and equipment"],
  ["characters:write", "Add and edit characters, log stats and equipment"],
  ["delete", "Delete accounts and characters"],
  ["tokens:read", "List tokens"],
  ["tokens:write", "Mint and revoke tokens"],
  ["audit:read", "Read the audit log"],
];
const DEFAULT_SCOPES = new Set(["accounts:read", "characters:read"]);

const LIFETIMES = [
  [3600, "1 hour"],
  [86400, "1 day"],
  [7 * 86400, "7 days"],
  [30 * 86400, "30 days"],
];

function tokenState(t) {
  if (t.revoked_at) return `revoked ${fmtDate(t.revoked_at)}`;
  if (t.expires_at && Date.parse(t.expires_at) <= Date.now()) return `expired ${fmtDate(t.expires_at)}`;
  return t.expires_at ? `expires ${fmtDate(t.expires_at)}` : "never expires";
}

async function tokensPage() {
  const [{ tokens }, { account_list: accounts }] = await Promise.all([api("GET", "/v1/tokens"), api("GET", "/v1/accounts")]);
  const minted = h("div");

  const form = bind(
    h("form", {},
      h("label", {}, "Label", h("input", { name: "label", required: true, maxlength: 100, placeholder: "e.g. gear planner" })),
      h("fieldset", { class: "checks" },
        h("legend", {}, "Scopes"),
        SCOPES.map(([scope, text]) =>
          h("label", {}, h("input", { type: "checkbox", name: "scopes", value: scope, checked: DEFAULT_SCOPES.has(scope) }),
            h("span", {}, h("code", {}, scope), " ", text)))),
      accounts.length
        ? h("fieldset", { class: "checks" },
            h("legend", {}, "Accounts (none ticked means all, including ones added later)"),
            accounts.map((a) =>
              h("label", {}, h("input", { type: "checkbox", name: "account_ids", value: a.id }),
                h("span", {}, `${a.label || a.region.toUpperCase()} `, h("span", { class: "meta" }, a.region.toUpperCase())))))
        : null,
      h("label", {}, "Expires after",
        h("select", { name: "expires_in_seconds" }, LIFETIMES.map(([s, text]) => h("option", { value: s, selected: s === 86400 }, text)))),
      h("button", { type: "submit" }, "Create token"),
    ),
    async (data) => {
      const scopes = data.getAll("scopes");
      if (!scopes.length) throw new Error("Pick at least one scope.");
      const ids = data.getAll("account_ids");
      const res = await api("POST", "/v1/tokens", {
        label: String(data.get("label")).trim(),
        scopes,
        account_ids: ids.length ? ids : null,
        expires_in_seconds: Number(data.get("expires_in_seconds")),
      });
      // The secret is shown once; keep it out of storage and the URL.
      const secret = h("input", { readonly: true, value: res.token, class: "secret", "aria-label": "New token" });
      const copy = h("button", { type: "button", class: "quiet" }, "Copy");
      copy.addEventListener("click", async () => {
        try { await navigator.clipboard.writeText(res.token); copy.textContent = "Copied"; }
        catch { secret.select(); }
      });
      const list = await tokenList();
      minted.replaceChildren(
        h("div", { class: "notice ok" },
          h("p", {}, `Created “${res.details.label}”. Copy it now: this is the only time it is shown.`),
          h("div", { class: "actions" }, secret, copy)));
      listPanel.replaceChildren(h("h2", {}, "Your tokens"), list);
      form.reset();
    },
  );

  async function tokenList(rows) {
    rows ??= (await api("GET", "/v1/tokens")).tokens;
    if (!rows.length) return h("p", { class: "empty" }, "No tokens.");
    return h("ul", { class: "list" }, rows.map((t) => {
      const live = !t.revoked_at && !(t.expires_at && Date.parse(t.expires_at) <= Date.now());
      const self = t.id === session.token_id;
      return h("li", {}, h("div", { class: "row" },
        h("div", {},
          h("div", {}, t.label, self ? h("span", { class: "meta" }, " · this browser") : null),
          h("div", { class: "meta" }, `${t.kind} · ${t.scopes.join(", ")}`),
          h("div", { class: "meta" },
            `${t.account_ids ? `${t.account_ids.length} account${t.account_ids.length === 1 ? "" : "s"}` : "all accounts"} · created ${fmtDate(t.created_at)} · ${tokenState(t)}`
              + (t.last_used_at ? ` · last used ${fmtDate(t.last_used_at)}` : ""))),
        live && !self
          ? h("button", {
              class: "quiet",
              onclick: async (e) => {
                if (!confirm(`Revoke “${t.label}” and every token minted from it?`)) return;
                e.target.disabled = true;
                try {
                  await api("DELETE", `/v1/tokens/${t.id}`);
                  listPanel.replaceChildren(h("h2", {}, "Your tokens"), await tokenList());
                } catch (err) {
                  e.target.disabled = false;
                  listPanel.prepend(notice("error", errorText(err)));
                }
              },
            }, "Revoke")
          : null));
    }));
  }

  const listPanel = h("div", { class: "panel" }, h("h2", {}, "Your tokens"), await tokenList(tokens));
  return h("section", {},
    h("div", { class: "crumbs" }, h("a", { href: "/#/" }, "Accounts"), " / "),
    h("h1", {}, "API tokens"),
    h("p", { class: "sub" },
      "Give a tool or agent its own token, with only the scopes and accounts it needs. Every write it makes is audited under its label. ",
      "A token cannot outlive the one that made it: this browser's session ends ", fmtDate(session.expires_at), "."),
    minted,
    h("div", { class: "grid" },
      h("div", { class: "panel" }, h("h2", {}, "New token"), form),
      listPanel,
    ),
  );
}

// ---------- router ----------

async function render() {
  renderSession();
  // A character page has a real path, so agents fetching its link get the
  // sheet (the Worker renders it in); old #/characters/ links move there.
  const hashPath = location.hash.replace(/^#/, "") || "/";
  if (hashPath.startsWith("/characters/")) {
    location.replace(`/characters/${hashPath.split("/")[2]}`);
    return;
  }
  const path = location.pathname.startsWith("/characters/") ? location.pathname : hashPath;
  let page;
  try {
    // Anyone may open a public character's page.
    if (path.startsWith("/characters/")) page = await characterPage(path.split("/")[2]);
    else if (!session) page = welcome();
    else if (path === "/") page = await home();
    else if (path === "/tokens") page = await tokensPage();
    else if (path.startsWith("/accounts/")) page = await accountPage(path.split("/")[2]);
    else page = h("p", {}, "Not found. ", h("a", { href: "/#/" }, "Go home"));
  } catch (err) {
    page = h("section", {}, notice("error", errorText(err)), h("a", { href: "/#/" }, session ? "Back to accounts" : "Go to msapi"));
  }
  app.replaceChildren(page);
}

window.addEventListener("hashchange", render);
render();
