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
  for (const c of children.flat()) if (c != null && c !== false) el.append(c.nodeType ? c : String(c));
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
  if (location.hash === hash) render();
  else location.hash = hash;
}

function renderSession() {
  sessionNav.replaceChildren();
  if (!session) return;
  sessionNav.append(
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
    h("p", { class: "sub" }, "Add your accounts and characters, then log their stat windows over time. Tools you trust can read them through the msapi API with tokens you control."),
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
              h("li", {}, h("a", { href: `#/accounts/${a.id}` },
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
      go(`#/characters/${c.id}`);
    },
  );
  return h("section", {},
    h("div", { class: "crumbs" }, h("a", { href: "#/" }, "Accounts"), " / "),
    h("h1", {}, account.label || account.region.toUpperCase()),
    h("p", { class: "sub" }, `${account.region.toUpperCase()} · added ${fmtDate(account.created_at)}`),
    h("div", { class: "grid" },
      h("div", { class: "panel" },
        h("h2", {}, "Characters"),
        account.character_list.length
          ? h("ul", { class: "list" }, account.character_list.map((c) =>
              h("li", {}, h("a", { href: `#/characters/${c.id}` },
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

async function characterPage(id) {
  const [c, latest, history] = await Promise.all([
    api("GET", `/v1/characters/${id}`),
    api("GET", `/v1/characters/${id}/stat`),
    api("GET", `/v1/characters/${id}/stat/history?limit=20`),
  ]);
  const current = latest.snapshot?.stat ?? latest.stat ?? null;
  const result = h("div");

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
    h("div", { class: "crumbs" }, h("a", { href: "#/" }, "Accounts"), " / ", h("a", { href: `#/accounts/${c.account_id}` }, "Account"), " / "),
    h("h1", {}, c.character_name),
    h("p", { class: "sub" }, `Lv. ${c.character_level} ${c.character_class} · ${c.world_name} (${c.world_type})`),
    result,
    h("div", { class: "panel" },
      h("h2", {}, "Current stats"),
      current
        ? [h("dl", { class: "stats" }, shown.map(([key, label]) => h("div", {}, h("dt", {}, label), h("dd", {}, fmtNum(current[key]))))),
           h("p", { class: "meta" }, `Captured ${fmtDate(current.captured_at)}`)]
        : h("p", { class: "empty" }, "No stats logged yet.")),
    h("div", { class: "panel" }, h("h2", {}, "Log the stat window"), form),
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
        : h("p", { class: "empty" }, "Every save is kept; your history will show here.")),
  );
}

// ---------- router ----------

async function render() {
  renderSession();
  const path = location.hash.replace(/^#/, "") || "/";
  let page;
  try {
    if (!session) page = welcome();
    else if (path === "/") page = await home();
    else if (path.startsWith("/accounts/")) page = await accountPage(path.split("/")[2]);
    else if (path.startsWith("/characters/")) page = await characterPage(path.split("/")[2]);
    else page = h("p", {}, "Not found. ", h("a", { href: "#/" }, "Go home"));
  } catch (err) {
    page = h("section", {}, notice("error", errorText(err)), h("a", { href: "#/" }, "Back to accounts"));
  }
  app.replaceChildren(page);
}

window.addEventListener("hashchange", render);
render();
