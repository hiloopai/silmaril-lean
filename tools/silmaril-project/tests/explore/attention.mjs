// The landing page's attention lists, the namespace browser and the status filters, in Chromium:
// the cards count what StatusSemantics classifies (status.js), deprecated problems and problems with
// an `expected_open` marking are left out of the lists but stay reachable, the browser walks dotted
// namespaces with breadcrumbs, and filters by displayed status and outcome through the URL.
//
//   node attention.mjs SITE_DIR [SHOTS_DIR]   (SITE_DIR holds index.html and project.sqlite)
//
// A copy of the database with one `expected_open` row (created here when the table is missing,
// for a database older than the marking) checks the exclusion of a marked open problem.
import { spawn, execFileSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8797;
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };

// a copy of the site whose database marks one open problem expected_open
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "attention-"));
for (const f of fs.readdirSync(site)) {
  const src = path.join(site, f);
  const dst = path.join(tmp, f);
  if (fs.statSync(src).isFile()) fs.copyFileSync(src, dst);
  else if (f === "_docs" && fs.statSync(src).isDirectory()) fs.cpSync(src, dst, { recursive: true });
}
const py = (code, ...args) => execFileSync("python3", ["-I", "-c", code, ...args], { encoding: "utf8" });
const marked = py(`
import sqlite3, sys
c = sqlite3.connect(sys.argv[1])
p = c.execute("SELECT p.name FROM problems p JOIN summary s ON s.problem = p.name WHERE s.summary = 'OPN' AND p.arity = 0 AND p.kind = 'prop' AND p.name NOT IN (SELECT problem FROM deprecated_problems) ORDER BY p.name LIMIT 1").fetchone()[0]
c.execute("CREATE TABLE IF NOT EXISTS expected_open (problem TEXT PRIMARY KEY, reason TEXT NOT NULL, note TEXT, pointer TEXT, module TEXT NOT NULL, origin TEXT NOT NULL)")
c.execute("INSERT OR REPLACE INTO expected_open VALUES (?, 'independent', 'test fixture of attention.mjs', NULL, 'Test', 'local')", (p,))
c.commit(); print(p)
`, path.join(tmp, "project.sqlite")).trim();

const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", tmp, "--port", String(port), "--log", path.join(os.tmpdir(), "attention_requests.jsonl")], { stdio: "ignore" });
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1300, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const go = async (hash) => { await p.goto(`http://127.0.0.1:${port}/index.html${hash}`); await settle(); };
  const errs = () => p.evaluate(() => [...document.querySelectorAll("#main .err")].map((e) => e.textContent.slice(0, 200)));
  const shot = async (n) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, n), fullPage: false }); } };

  // the landing page: cards from the same classification as the index
  await go("#/summary");
  const cards = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll(".att a.card")].map((a) =>
    [new URLSearchParams(a.getAttribute("href").split("?")[1]).toString(), Number(a.querySelector("b").textContent)])));
  const excludedLinks = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll(".excluded-routes a.excluded-link")].map((a) =>
    [new URLSearchParams(a.getAttribute("href").split("?")[1]).toString(), Number(a.querySelector("b").textContent)])));
  const idx = await p.evaluate(async () => {
    const idx = await problemIndex();
    const n = { contrary: 0, open: 0, weaker: 0, stronger: 0, deprecated: 0, "expected-open": 0 };
    for (const e of idx.list) if (e.kind !== "group") { if (e.st.attention.list) n[e.st.attention.list]++; else if (e.st.attention.excluded) n[e.st.attention.excluded]++; }
    return n;
  });
  check(cards["attention=contrary"] === idx.contrary && cards["attention=open"] === idx.open && cards["attention=weaker"] === idx.weaker &&
    cards["attention=stronger"] === idx.stronger, `attention cards: ${JSON.stringify(cards)}`);
  check(!("excluded=deprecated" in cards) && excludedLinks["excluded=deprecated"] >= 1 && cards["excluded=expected-open"] === 1,
    "deprecated problems are moved out of the top cards into a quiet secondary route, and expected-open problems are counted apart");
  const openList = await p.evaluate(() => [...document.querySelectorAll("#att-open + p + .tablebox a, #att-open ~ .tablebox a")].map((a) => a.textContent));
  check(!openList.includes(marked), `the expected-open problem ${marked} is not in the open list`);
  const deprecated = await p.evaluate(async () => (await problemIndex()).list.filter((e) => e.st.deprecated).map((e) => e.name));
  check(deprecated.length > 0 && !deprecated.some((n) => openList.includes(n)), `deprecated problems are not listed (${deprecated.join(", ")})`);
  check(!(await p.evaluate(() => document.querySelector("#main").textContent)).match(/·true|·false|✓/), "no truth suffixes or check marks on the landing page");
  await shot("summary-attention.png");

  // the excluded problems stay reachable
  await go("#/browse/?excluded=expected-open");
  const ex = await p.evaluate(() => [...document.querySelectorAll(".browse-problems a")].map((a) => a.textContent));
  check(ex.includes(marked), `the expected-open filter lists ${marked}`);
  await go("#/problem/" + encodeURIComponent(marked));
  check(/Expected to stay open for a metatheoretic reason \(independent\)/.test(await p.evaluate(() => document.querySelector(".status-sentence").textContent)),
    "its page names the marking and its reason");

  // namespace navigation with breadcrumbs
  await go("#/browse/");
  const top = await p.evaluate(() => [...document.querySelectorAll("#bnamespaces td.ns-name a")].map((a) => a.textContent));
  check(top.includes("silmaril.") && top.includes("formats."), `top-level namespaces: ${top.join(" ")}`);
  await p.click("#bnamespaces td.ns-name a >> text=silmaril.");
  await p.waitForFunction(() => (document.querySelector(".crumbs [aria-current]") || {}).textContent === "silmaril", null, { timeout: 30000 }).catch(() => {});
  await settle();
  await p.click("#bnamespaces td.ns-name a >> text=selftest.");
  await p.waitForFunction(() => (document.querySelector(".crumbs [aria-current]") || {}).textContent === "selftest", null, { timeout: 30000 }).catch(() => {});
  await settle();
  const crumbs = await p.evaluate(() => [...document.querySelectorAll(".crumbs a, .crumbs [aria-current]")].map((a) => a.textContent));
  check(crumbs.join(" ") === "all silmaril selftest", `breadcrumbs: ${crumbs.join(" ")}`);
  check(await p.evaluate(() => decodeURIComponent(location.hash) === "#/browse/silmaril.selftest"), "the namespace is in the URL");
  await shot("browse-selftest.png");

  // filter by displayed status through the form; the URL keeps it
  await p.check("#bfilter input[name=status][value=OPN]");
  await p.waitForFunction(() => /status=OPN/.test(location.hash) && /match the filter/.test((document.querySelector("#bsummary") || {}).textContent || ""), null, { timeout: 30000 }).catch(() => {});
  await settle();
  const f1 = await p.evaluate(() => ({ hash: location.hash, codes: [...document.querySelectorAll(".browse-problems .st")].map((e) => e.dataset.display) }));
  check(/status=OPN/.test(f1.hash) && f1.codes.length > 0 && f1.codes.every((c) => c === "OPN"), `status filter: ${f1.codes.length} OPN rows, ${f1.hash} ${f1.codes.join(",")}`);
  check(f1.codes.length > 0 && (await p.evaluate(() => [...document.querySelectorAll(".browse-problems a")].map((a) => a.textContent))).includes("silmaril.selftest.languages.wasm_accept_member"),
    "the open wasm_accept_member is among them");
  await go("#/browse/?status=CTH&q=json_number");
  const f2 = await p.evaluate(() => [...document.querySelectorAll(".browse-problems .st")].map((e) => e.dataset.display + ":" + e.dataset.code));
  check(f2.length > 0 && f2.every((c) => c.startsWith("CTH:")), `closed refutations read CTH whatever is stored: ${[...new Set(f2)].join(" ")}`);
  await go("#/browse/?outcome=match&status=TAU");
  const f3 = await p.evaluate(() => [...document.querySelectorAll(".browse-problems .st")].map((e) => e.dataset.outcome + ":" + e.dataset.display));
  check(f3.length > 0 && f3.every((c) => c === "match:TAU"), `outcome and status filters combine (${f3.length} rows)`);
  await shot("browse-filter.png");

  // the statuses page explains every displayed code
  await go("#/statuses");
  const gl = await p.evaluate(() => [...document.querySelectorAll(".glossary dt .st")].map((e) => e.textContent));
  check(["THM", "CTH", "TAU", "UNS", "SAT", "CSA", "NOC", "OPN"].every((c) => gl.includes(c)), `glossary: ${gl.join(" ")}`);

  check((await errs()).length === 0 && errors.length === 0, `no errors (${errors.join("; ")})`);
} finally {
  await b.close();
  srv.kill();
  fs.rmSync(tmp, { recursive: true, force: true });
}
console.log(fails.length ? `${fails.length} failed` : "all passed");
process.exit(fails.length ? 1 : 0);
