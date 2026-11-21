import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const fixture = JSON.parse(fs.readFileSync(path.join(site, "named-logic.json")));
const port = 8812, url = `http://127.0.0.1:${port}/index.html?load=full`;
const scratch = fs.mkdtempSync(path.join(os.tmpdir(), "named-logic-browser-"));
const server = spawn("python3", ["-I", fileURLToPath(new URL("pages_server.py", import.meta.url)),
  "--root", site, "--port", String(port), "--log", path.join(scratch, "requests.jsonl")], { stdio: "ignore" });
const defaultChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
let browser;
try {
  for (let attempt = 0; attempt < 30; attempt++) {
    if (await fetch(url).then((response) => response.ok, () => false)) break;
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  browser = await chromium.launch({ executablePath: process.env.CHROME || (fs.existsSync(defaultChrome) ? defaultChrome : undefined) });
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const errors = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const sha = "bdasl-inline-sha256", b3 = "bdasl-inline-blake3";
  const screenshot = async (name) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, `${name}.png`), fullPage: true });
  };
  const open = async (row, profile = sha) => {
    await page.goto(`${url}#/named-logic/${row}/${profile}`);
    await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  };
  const body = () => page.locator("main").innerText();
  await open("hol.named-assumption");
  assert.equal(await page.locator("#named-logic-row option").count(), 7);
  assert.match(await body(), /SHA-256 matches CID bytes/);
  assert.match(await body(), /weakening and implication introduction/);
  assert.match(await body(), /does not establish this judgment/);
  const pinned = await page.locator("#named-logic-evidence a").getAttribute("href");
  assert.ok(pinned.includes(`/blob/${fixture.source.revision}/`));
  await page.locator("#named-logic-blocks details summary").first().click();
  assert.equal(await page.locator("#named-logic-blocks details[open]").count(), 1);
  await screenshot("hol-named-assumption");

  await page.locator("#named-logic-profile").selectOption(b3);
  await page.waitForFunction(() => /bdasl-inline-blake3$/.test(location.hash) && !window.explore.busy);
  assert.match(await body(), /BLAKE3 not computed in browser/);
  await page.locator("#named-logic-row").selectOption("mltt.sigma-inhabited");
  await page.waitForFunction(() => /mltt.sigma-inhabited/.test(location.hash) && !window.explore.busy);
  assert.match(await body(), /∃ term/);
  assert.doesNotMatch(await page.locator("#named-logic-blocks").innerText(), /^term$/m);
  await screenshot("mltt-sigma-inhabited");

  let supplied = structuredClone(fixture);
  await page.route("**/named-logic.json", (route) => route.fulfill({ json: supplied }));
  const first = fixture.rows[0].roots.conclusion;
  delete supplied.blocks[sha][first.cid];
  await open("hol.closed");
  assert.match(await body(), /Missing root block. The judgment is not refuted/);
  assert.match(await body(), /closedRow/);
  await screenshot("missing-root");

  supplied = structuredClone(fixture);
  supplied.blocks[sha][first.cid].hex = "d82a4100";
  await page.reload();
  await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  assert.match(await body(), /Invalid wire: unsupported tag/);
  assert.match(await body(), /SHA-256 digest mismatch/);

  supplied = structuredClone(fixture);
  supplied.profiles[sha].atomCodec = "boxed";
  await page.reload();
  await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  assert.match(await body(), /profile mismatch/);
  assert.equal(await page.locator("#named-logic-evidence").count(), 0);
  assert.deepEqual(errors, []);
  console.log("Named logic Explorer: both profiles, pinned evidence, bytes, missing root, invalid wire, digest and profile mismatch passed.");
} finally {
  if (browser) await browser.close();
  server.kill();
  fs.rmSync(scratch, { recursive: true, force: true });
}
