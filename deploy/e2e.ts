// Drives the hosted web app in Chrome with a virtual passkey authenticator:
// sign up, add an account and a character, log stats twice and equipment once,
// sign out, sign in
// again, and (with OPS_TOKEN set) restart the container to check the data
// survives a cold start.
//
//   bun e2e.ts [https://msapi.iamnbutler.workers.dev]

import { chromium } from "playwright-core";

const base = process.argv[2] ?? "https://msapi.iamnbutler.workers.dev";
const chrome = process.env.CHROME ?? "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
const name = `E2E ${Date.now().toString(36)}`;

function check(ok: unknown, what: string): void {
  if (!ok) throw new Error(`failed: ${what}`);
  console.log(`ok: ${what}`);
}

const browser = await chromium.launch({ executablePath: chrome, headless: true });
try {
  const context = await browser.newContext();
  const page = await context.newPage();
  const cdp = await context.newCDPSession(page);
  await cdp.send("WebAuthn.enable");
  await cdp.send("WebAuthn.addVirtualAuthenticator", {
    options: {
      protocol: "ctap2",
      transport: "internal",
      hasResidentKey: true,
      hasUserVerification: true,
      isUserVerified: true,
      automaticPresenceSimulation: true,
    },
  });
  page.on("pageerror", (e) => console.error("page error:", e.message));

  await page.goto(base);
  await page.getByLabel("Display name").fill(name);
  await page.getByRole("button", { name: "Create account with a passkey" }).click();
  await page.getByRole("heading", { name: "Accounts" }).waitFor();
  check(await page.locator("#session").textContent().then((t) => t?.includes(name)), "signed up with a passkey");

  await page.getByLabel("Label").fill("main");
  await page.getByRole("button", { name: "Add account" }).click();
  await page.getByRole("heading", { name: "main" }).waitFor();
  check(true, "created an account");

  const character = `T${Date.now().toString(36).slice(-6)}`;
  await page.getByLabel("Name").fill(character);
  await page.getByLabel("World").selectOption("Kronos");
  await page.getByLabel("Class").selectOption("Night Walker");
  await page.getByLabel("Level").fill("275");
  await page.getByRole("button", { name: "Add character" }).click();
  await page.getByRole("heading", { name: character }).waitFor();
  check(true, "added a character");

  await page.getByLabel("Combat Power").fill("123456789");
  await page.getByLabel("LUK", { exact: true }).fill("29216");
  await page.getByLabel("Final Damage %").fill("162.27");
  await page.getByRole("button", { name: "Log stats" }).click();
  await page.getByText("Saved.").waitFor();
  await page.getByLabel("Combat Power").fill("130000000");
  await page.getByRole("button", { name: "Log stats" }).click();
  await page.waitForFunction(() => document.querySelectorAll("tbody tr").length === 2);
  const rows = await page.locator("tbody tr").count();
  check(rows === 2, `logged stats twice (${rows} history rows)`);

  await page.getByText("Record equipment").click();
  await page.locator("textarea[name=json]").fill(JSON.stringify({
    item_equipment: [{
      item_equipment_slot: "belt",
      item_name: "Superior Engraved Gollux Belt",
      starforce: 18,
      starforce_max: 30,
      item_total_option: { str: 149 },
      item_base_option: { str: 60 },
      item_enhancement_option: { str: 73 },
      item_add_option: { str: 16 },
      potential_option_grade: "unique",
      potential_option_1: "STR: +9%",
    }],
  }));
  await page.getByRole("button", { name: "Save equipment" }).click();
  await page.getByText("Saved.").waitFor();
  await page.getByRole("button", { name: "Superior Engraved Gollux Belt" }).click();
  check(await page.locator(".tip").textContent().then((t) => t?.includes("STR: +149 (60 +73 +16)")), "recorded equipment and read its tooltip");
  const characterUrl = page.url();

  if (process.env.OPS_TOKEN) {
    const res = await fetch(`${base}/__ops/restart`, { method: "POST", headers: { authorization: `Bearer ${process.env.OPS_TOKEN}` } });
    check(res.status === 204, "restarted the container");
    await page.reload();
    await page.getByRole("heading", { name: character }).waitFor({ timeout: 120_000 });
    const after = await page.locator("tbody tr").count();
    check(after === 2, `history survived a cold start (${after} rows)`);
    check(await page.getByRole("button", { name: "Superior Engraved Gollux Belt" }).count() === 1, "equipment survived a cold start");
  }

  await page.getByRole("link", { name: "API tokens" }).click();
  await page.getByRole("heading", { name: "API tokens" }).waitFor();
  await page.getByLabel("Label").fill("e2e reader");
  await page.getByRole("button", { name: "Create token" }).click();
  const secret = await page.getByLabel("New token").inputValue();
  const me = await fetch(`${base}/v1/me`, { headers: { authorization: `Bearer ${secret}` } }).then((r) => r.json());
  check(me.token?.label === "e2e reader" && me.token.scopes.join() === "accounts:read,characters:read", "minted a read-only token in the UI");
  page.once("dialog", (d) => d.accept());
  await page.locator("li", { hasText: "e2e reader" }).getByRole("button", { name: "Revoke" }).click();
  await page.locator("li", { hasText: "e2e reader" }).getByText("revoked").waitFor();
  const after = await fetch(`${base}/v1/me`, { headers: { authorization: `Bearer ${secret}` } });
  check(after.status === 401, "revoked it in the UI");

  await page.getByRole("button", { name: "Sign out" }).click();
  await page.getByRole("button", { name: "Sign in with a passkey" }).click();
  await page.getByRole("heading", { name: "Accounts" }).waitFor();
  await page.goto(characterUrl);
  await page.getByRole("heading", { name: character }).waitFor();
  check(await page.locator("dd").first().textContent().then((t) => t === "130,000,000"), "signed in again and saw the latest stats");
} finally {
  await browser.close();
}
