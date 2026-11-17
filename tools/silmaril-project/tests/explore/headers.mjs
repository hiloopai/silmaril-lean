// The explorer's Headers tab (explore/views/headers.js) on headers/index.json (header-pages).
// Checks, in a browser: the tab is in the navigation; one index row per header; a refused header
// shows the reader's reason; each prototype row shows every ABI's lowering or refusal as the data
// says; the System V scalar plan names xmm registers for floating arguments; each aggregate shows
// both data models' size and alignment as the data says; nothing is called a theorem or proved;
// no page or console errors.
//   node headers.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8803;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/headers_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const d = JSON.parse(fs.readFileSync(path.join(site, "headers", "index.json")));
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1400 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push("pageerror: " + e.message));
  p.on("console", (m) => { if (m.type() === "error") errors.push("console: " + m.text()); });
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const open = async (hash) => { await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`); await settle(); };
  check(d.schema === "silmaril.header-pages/1", "headers/index.json has the schema silmaril.header-pages/1");
  await open("/headers");
  check(await p.evaluate(() => [...document.querySelectorAll("#nav a")].some((a) => a.textContent === "Headers" && a.classList.contains("on"))), "the Headers tab is in the navigation and selected");
  const rows = await p.evaluate(() => [...document.querySelectorAll("tr[data-header]")].map((r) => r.dataset.header));
  check(JSON.stringify(rows) === JSON.stringify(d.headers.map((h) => h.id)), `index: one row per header (${rows.length})`);
  if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, "headers-index.png") }); }
  for (const h of d.headers) {
    await open("/headers/" + h.id);
    const pg = await p.evaluate(() => ({
      text: document.querySelector("main").innerText,
      refused: !!document.querySelector('[data-read="refused"]'),
      fns: Object.fromEntries([...document.querySelectorAll("tr[data-fn]")].map((r) => [r.dataset.fn,
        Object.fromEntries([...r.querySelectorAll("td[data-abi]")].map((c) => [c.dataset.abi, c.innerText]))])),
      aggs: Object.fromEntries([...document.querySelectorAll("h4[data-agg]")].map((h4) => [h4.dataset.agg,
        Object.fromEntries([...h4.nextElementSibling.querySelectorAll("td[data-dm]")].map((c) => [c.dataset.dm, c.innerText.trim()]))])) }));
    if (h.read.refused != null) { check(pg.refused && pg.text.includes(h.read.refused), `${h.id}: refused with the reader's reason`); continue; }
    let ok = true;
    for (const fn of h.prototypes) for (const [abi, l] of Object.entries(fn.lowering)) {
      const t = pg.fns[fn.name]?.[abi] || "";
      if (l.refused != null ? !t.includes("refused: " + l.refused) : !t.includes(l.ok)) ok = false;
      if (l.plan && l.plan.ok && !t.includes(l.plan.ok.result)) ok = false;
    }
    check(ok, `${h.id}: ${h.prototypes.length} prototypes, each ABI's lowering or refusal as the data says`);
    let lok = true;
    for (const a of h.aggregates || []) for (const [dm, L] of Object.entries(a.layouts)) {
      const t = pg.aggs[a.tag]?.[dm] || "";
      if (L.refused != null ? !t.includes("refused") : t !== `${L.ok.size} / ${L.ok.align}`) lok = false;
    }
    check(lok, `${h.id}: ${(h.aggregates || []).length} aggregates, size / align per data model as the data says`);
    check(!/\b(theorem proved|proved|verified)\b/i.test(pg.text.replace(/not theorems/g, "")), `${h.id}: nothing is called proved or verified`);
    if (h.id === "layout-demo") {
      check(/xmm0/.test(pg.fns.scale?.sysvScalar || "") && /refused/.test(pg.fns.scale?.sysvInt || ""), "layout-demo: double scale(double, float, int) uses xmm registers under sysvScalar, refused by sysvInt");
      check(pg.aggs.pt?.sysvX86_64 === "24 / 8" && pg.aggs.pt?.msX64 === "12 / 4", "layout-demo: struct pt is 24/8 under System V, 12/4 under Microsoft x64");
      if (shots) await p.screenshot({ path: path.join(shots, "headers-layout-demo.png"), fullPage: true });
    }
  }
  check(errors.length === 0, `no page or console errors ${errors.join("; ")}`);
} finally { await b.close(); srv.kill(); }
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
