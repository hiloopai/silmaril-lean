// The formal rows (docs/projects/formal-rows.md), in Chromium, on a site built from silmaril's own project:
// * Formal is in the navigation and opens a table of the logics, first-order logic, PA and second-order arithmetic
//   first, with soundness and consistency statuses that link Lean-checked theorems;
// * a row's page lists its systems, interpretations, presentations (default first), role-checked properties with
//   their statements and axioms, and its concrete problems;
// * a problem's page shows its S-expression, switches presentation (kept in the URL) and lists its checked claims;
// * property and presentation pages, deep links, and the exact source of a property's theorem and of a problem's
//   sentence; a narrow (phone) viewport; no page error anywhere.
//   node formal.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8807;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "formal_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const open = async (hash, sel) => { await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`); await settle();
    if (sel) await p.waitForSelector(sel, { timeout: 60000 }); await p.waitForTimeout(300); };
  const shot = async (name, full = true) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: full }); } };
  const rows = (sel) => p.evaluate((sel) => [...document.querySelectorAll(sel + " tbody tr")].filter((tr) => !tr.hidden).map((tr) =>
    [...tr.children].map((td) => td.textContent.trim())), sel);

  // the table, first
  await open("/summary");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/formal"), "Formal is in the navigation");
  await p.click('#nav a[href="#/formal"]'); await p.waitForSelector("#fr-rows", { timeout: 60000 }); await settle();
  const t = await rows("#fr-rows");
  check(t.length === 5, `five logics (${t.length})`);
  check(/First-order/.test(t[0][0]) && /Peano/.test(t[1][0]) && /Second-order/.test(t[2][0]) && /HOL/.test(t[3][0]) && /MLTT/.test(t[4][0]),
    `first-order logic, PA and second-order arithmetic come first (${t.map((r) => r[0].slice(0, 20))})`);
  check(/proved \(2\)/.test(t[1][3]) && /proved \(3\)/.test(t[1][4]), `PA: soundness ×2, consistency ×3 (${t[1][3]}, ${t[1][4]})`);
  check(/proved \(8\)/.test(t[2][3]) && /proved \(5\)/.test(t[2][4]), `second order: soundness ×8 (full and Henkin), consistency ×5 (${t[2][3]}, ${t[2][4]})`);
  check(t[0][3] === "—" && /proved \(1\)/.test(t[0][4]) && /proved \(1\)/.test(t[0][5]), `FOL: no soundness (no derivations), consistency of consequence and a model (${t[0][3]}, ${t[0][4]}, ${t[0][5]})`);
  check(/silmaril\.fol\.formula/.test(t[0][1]) && /silmaril\.arithmetic\.formula/.test(t[1][1]) && /\+1/.test(t[1][1]), "default presentations, PA with a second one");
  await shot("formal-table");

  // a row
  await open("/formal-row/" + encodeURIComponent("logic.formal.row.second_order"), "#fr-properties");
  const props = await rows("#fr-properties");
  check(props.length === 16, `second order: 16 properties (${props.length})`);
  check(props.filter((r) => r[1] === "soundness").every((r) => /SoundFor/.test(r[3])) &&
    props.filter((r) => r[1] === "consistency").every((r) => /ConsistentWrt/.test(r[3])), "each statement has its role's shape");
  check(props.every((r) => /standard axioms only/.test(r[4])), "standard axioms only");
  check(/full/.test(await p.textContent("main")) && /henkin/.test(await p.textContent("main")), "both interpretations, full and Henkin, are listed");
  const pbs = await rows("#fr-problems");
  check(pbs.length === 2 && pbs.some((r) => /exists-set X/.test(r[1])), `the second-order problems, with their S-expressions (${pbs.length})`);
  await shot("formal-row-second-order");

  // a problem: S-expression, presentation selector, claims
  await open("/formal-problem/" + encodeURIComponent("logic.formal.pa.zero_add_zero"), "#fr-sexp");
  check((await p.textContent("#fr-sexp")).trim() === "( = ( + zero zero ) zero )", "the problem's S-expression, as Lean printed it");
  const opts = await p.evaluate(() => [...document.querySelectorAll("#fr-pres option")].map((o) => o.textContent));
  check(opts.length === 2 && opts.some((o) => /words/.test(o)), `two presentations to choose from (${opts})`);
  await p.selectOption("#fr-pres", "logic.formal.pa.sexp_words"); await p.waitForTimeout(200);
  check((await p.textContent("#fr-sexp")).trim() === "( = ( add zero zero ) zero )" && /presentation=logic\.formal\.pa\.sexp_words/.test(await p.evaluate(() => location.hash)),
    "switching presentation rewrites the S-expression and keeps it in the URL");
  const claims = await p.textContent(".fr-claims");
  check(/derived/.test(claims) && /zeroAddZero_derived/.test(claims) && /true in a model/.test(claims) && /zeroAddZero_true/.test(claims), "the derivation and truth claims, with their theorems");
  await shot("formal-problem");
  await open("/formal-problem/" + encodeURIComponent("logic.formal.pa.zero_add_zero") + "?presentation=logic.formal.pa.sexp_words", "#fr-sexp");
  check((await p.textContent("#fr-sexp")).trim() === "( = ( add zero zero ) zero )", "a deep link opens the chosen presentation");
  await open("/formal-problem/" + encodeURIComponent("logic.formal.fol.succ_irrefl"), "#fr-sexp");
  check(/rel < \( app succ/.test(await p.textContent("#fr-sexp")) && /a semantic consequence/.test(await p.textContent(".fr-claims")), "the first-order problem: entailed in every structure, true in ℕ");

  // a property and a presentation
  await open("/formal-property/" + encodeURIComponent("logic.formal.z2.consistency"), "main h2");
  const pp = await p.textContent("main");
  check(/ConsistentWrt/.test(pp) && /falsum/.test(pp) && /\.Z2/.test(pp), "a consistency property: its statement, falsity and argument");
  await open("/presentation/" + encodeURIComponent("logic.formal.pa.sexp_words"), "main h2");
  const pr = await p.textContent("main");
  check(/silmaril\.arithmetic\.formula\.words/.test(pr) && /silmaril\.arithmetic\.formula v1/.test(pr) && /add zero zero/.test(pr), "a presentation: its sibling and its problems");

  // exact sources
  if (await p.evaluate(() => document.getElementById("source-meta").textContent.trim() !== "null")) {
    for (const [decl, file] of [["Silmaril.Consequence.SecondOrder.consistent", "Silmaril/Logic/Consequence/SecondOrder/Thms.lean"],
        ["Silmaril.Consequence.Arithmetic.pa_consistent", "Silmaril/Logic/Consequence/Arithmetic/Thms.lean"],
        ["Silmaril.Consequence.FirstOrder.succIrrefl", "Silmaril/Logic/Consequence/FirstOrder/Thms.lean"]]) {
      await open("/source/" + encodeURIComponent(decl));
      await p.waitForFunction(() => !document.querySelector(".lean-src") || !/reading the Lean source/.test(document.querySelector(".lean-src").textContent), null, { timeout: 30000 });
      const v = await p.evaluate(() => ({ where: (document.querySelector(".src-permalink") || {}).textContent || "", exact: !!document.querySelector(".src-exact") }));
      check(v.where.startsWith(file) && v.exact, `source of ${decl}: ${v.where} ${v.exact ? "exact" : "not exact"}`);
    }
  }

  // a phone
  const m = await b.newPage({ viewport: { width: 390, height: 844 }, isMobile: true });
  m.on("pageerror", (e) => errors.push(e.message));
  await m.goto(`http://127.0.0.1:${port}/index.html#/formal/`);
  await m.waitForSelector("#fr-rows", { timeout: 60000 }); await m.waitForTimeout(500);
  const w = await m.evaluate(() => ({ scroll: document.documentElement.scrollWidth, rows: document.querySelectorAll("#fr-rows tbody tr").length }));
  check(w.rows === 5 && w.scroll <= 400, `narrow: the table fits (${JSON.stringify(w)})`);
  if (shots) await m.screenshot({ path: path.join(shots, "formal-phone.png"), fullPage: true });

  check(errors.length === 0, `no page errors ${JSON.stringify(errors)}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
