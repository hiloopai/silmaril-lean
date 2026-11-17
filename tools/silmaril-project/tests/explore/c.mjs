// The explorer's C programs tab (explore/views/c.js) on the pages `c-pages` writes (c/…). Checks,
// in a browser:
// * the tab is in the navigation; the corpus table has one row per program of c/programs/index.json,
//   with the routes and verdicts of its report and a `compiled` tag only where a verdict exists;
// * the theorems table lists exactly the theorems of c/theorems.json, every one tagged `kernel`,
//   and no theorem whose statement is not a shape (the decoy `decoy_arithmetic_refines`, whose
//   *name* mentions a corpus program and a shape, is absent): association is by statement;
// * each profile row's theorem column is the theorems whose statement is that row, and a row with
//   no such theorem is tagged `compiled`, not `kernel`;
// * a program page shows each stage present in provenance.json with its producer, and each absent
//   stage as `missing` with its failure; "view" fetches the artifact, decompresses it when it is
//   gzip, and its SHA-256 matches provenance.json; the source links are pinned to the commit;
// * no program page claims a kernel theorem (no corpus program is a theorem's argument), recorded
//   losses (the Cerberus route's dropped asm label) and warnings are shown;
// * no page errors and no console errors.
//   node c.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8798;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/c_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const json = (rel) => JSON.parse(fs.readFileSync(path.join(site, "c", rel)));
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1100 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push("pageerror: " + e.message));
  p.on("console", (m) => { if (m.type() === "error") errors.push("console: " + m.text()); });
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: true }); } };
  const idx = json("programs/index.json"), thms = json("theorems.json"), profs = json("profiles.json");

  await open("/c");
  const navOn = await p.evaluate(() => document.querySelector("#nav a.on")?.textContent);
  check(navOn === "C programs", `the C programs tab is in the navigation and selected (${navOn})`);
  const rows = await p.evaluate(() => [...document.querySelectorAll("#cprograms tbody tr")].map((r) => ({
    name: r.dataset.program, text: r.textContent, tags: [...r.querySelectorAll(".ctag")].map((t) => t.dataset.tag) })));
  check(rows.length === idx.programs.length, `one corpus row per program (${rows.length})`);
  const st = await p.evaluate(() => [...document.querySelectorAll("#cprograms tbody tr")].map((r) => r.dataset.status));
  check(idx.programs.every((pr, i) => st[i] === pr.status), "each row shows the program's one status");
  const statusText = await p.evaluate(() => document.querySelector("#cstatuses")?.textContent || "");
  const total = [...statusText.matchAll(/ (\d+)/g)].map((m) => Number(m[1])).slice(1).reduce((a, b) => a + b, 0);
  check(total === idx.programs.length, `the status counts sum to the number of programs (${total})`);
  const blockedRows = await p.evaluate(() => [...document.querySelectorAll("#cprograms tbody tr")].filter((r) => r.querySelector(".cblocked")).map((r) => r.dataset.program));
  check(JSON.stringify(blockedRows) === JSON.stringify(idx.programs.filter((pr) => pr.blockedRoutes.length).map((pr) => pr.name)),
    `rows with a blocked route are marked (${blockedRows})`);
  for (const pr of idx.programs) {
    const r = rows.find((x) => x.name === pr.name);
    const v = Object.entries(pr.verdicts);
    check(r && v.every(([k, x]) => r.text.includes(`${k}: ${x}`)), `${pr.name}: its verdicts are shown`);
    check(r && (v.length ? r.tags.includes("compiled") && !r.tags.includes("kernel") : r.tags.includes("missing")),
      `${pr.name}: evidence tag ${v.length ? "compiled" : "missing"}, never kernel`);
    const ubOnly = v.some(([, x]) => /source UB/.test(x));
    check(r && ubOnly === r.tags.includes("only through source UB"), `${pr.name}: UB-only coverage ${ubOnly ? "is" : "is not"} flagged`);
  }
  const th = await p.evaluate(() => [...document.querySelectorAll("#cthms tbody tr")].map((r) => ({
    name: r.dataset.theorem, tags: [...r.querySelectorAll(".ctag")].map((t) => t.dataset.tag), href: r.querySelector("a.srclink")?.href })));
  check(th.length === thms.theorems.length && thms.theorems.every((t) => th.some((x) => x.name === t.name)),
    `the theorems table is exactly theorems.json (${th.length})`);
  check(th.every((x) => x.tags.length === 1 && x.tags[0] === "kernel"), "every listed theorem is tagged kernel");
  check(!thms.theorems.some((t) => /decoy/.test(t.name)) && !th.some((x) => /decoy/.test(x.name)),
    "the decoy theorem (a shape and a program in its name, neither in its statement) is not listed");
  const rowsOf = await p.evaluate(() => [...document.querySelectorAll("#cthms tbody tr")].map((r) => r.children[1].textContent.trim()));
  check(thms.theorems.filter((t) => t.row).length === rowsOf.filter((x) => x !== "—").length, "each registered row's theorem shows its row");
  check(thms.theorems.every((t) => t.shape.startsWith("silmaril.shapes.c.tv.") && t.axioms.every((a) => ["propext", "Classical.choice", "Quot.sound"].includes(a))),
    "every theorem is a C TV shape with the standard axioms only");
  check(th.every((x) => x.href && /\/blob\/[0-9a-f]{7,40}\//.test(x.href)), "theorem source links are pinned to a commit");
  for (const pr of profs) {
    const pr2 = await p.evaluate((d) => [...document.querySelectorAll(`table.cprofile[data-profile="${d}"] tbody tr`)].map((r) => ({
      scalar: r.dataset.scalar, last: r.lastElementChild.textContent, tags: [...r.lastElementChild.querySelectorAll(".ctag")].map((t) => t.dataset.tag) })), pr.decl);
    check(pr2.length === pr.scalars.length, `${pr.decl}: one row per scalar type`);
    for (const s of pr.scalars) {
      const r = pr2.find((x) => x.scalar === s.scalar);
      const ok = s.theorems.length ? s.theorems.every((t) => r.last.includes(t.name.split(".").pop())) && r.tags.every((t) => t === "kernel")
        : r.tags.length === 1 && r.tags[0] === "compiled";
      if (!ok) check(false, `${pr.decl}.${s.scalar}: theorem column matches profiles.json`);
    }
    check(true, `${pr.decl}: theorem columns match profiles.json`);
  }
  await shot("c-index");
  // A registered row's link opens its problem in the project database, with the status its theorem gives.
  const rowThm = thms.theorems.find((t) => t.row === "silmaril.c_tv.examples.overflow.refines_ub_free");
  if (rowThm) {
    await open("/problem/" + encodeURIComponent(rowThm.row));
    const body = await p.evaluate(() => document.querySelector("#main").textContent);
    check(/UNS/.test(body) && body.includes(rowThm.name.split(".").pop()), "the UB-only row's problem page shows UNS and the refuting theorem");
    await shot("c-row-overflow-ub-free");
  }

  for (const pr of idx.programs) {
    const prov = json(`programs/${pr.name}/provenance.json`);
    await open(`/c-program/${pr.name}`);
    const st = await p.evaluate(() => [...document.querySelectorAll(".cstage")].map((d) => ({ file: d.dataset.stage, present: d.dataset.present,
      tags: [...d.querySelectorAll(".ctag")].map((t) => t.dataset.tag), text: d.textContent })));
    for (const s of st) {
      const a = prov.artifacts[s.file];
      check(a ? s.present === "yes" && s.text.includes(a.sha256.slice(0, 12)) : s.present === "no" && s.tags.includes("missing"),
        `${pr.name}/${s.file}: ${a ? "present with its SHA-256" : "absent and tagged missing"}`);
    }
    const kernel = await p.evaluate(() => document.querySelector("#ckernel b")?.textContent);
    check(kernel === "0", `${pr.name}: no kernel theorem is attached (${kernel})`);
    const losses = await p.evaluate(() => [...document.querySelectorAll(".closs")].map((x) => x.dataset.blocking));
    check(losses.length === prov.losses.length && prov.losses.every((l, i) => losses[i] === String(l.blocking)),
      `${pr.name}: ${prov.losses.length} recorded losses shown, blocking ones as blocking`);
    const blockedEdges = await p.evaluate(() => document.querySelectorAll(".cstage .cblocked").length);
    check(blockedEdges === prov.edges.filter((e) => e.sourceCorrespondence && (e.relation === "produces" || e.relation === "elaborates")).length,
      `${pr.name}: every edge of a blocked route is marked in its stage`);
    const src = await p.evaluate(() => [...document.querySelectorAll("a.srclink")].map((a) => a.href).find((h) => h.endsWith("/source.c")));
    check(src && /\/blob\/[0-9a-f]{7,40}\/examples\/c-programs\//.test(src), `${pr.name}: the source link is pinned`);
    // View every present artifact: decompressed, hashed in the browser, compared with provenance.json.
    const views = await p.$$("button.cview");
    for (const v of views) await v.click();
    await p.waitForFunction(() => [...document.querySelectorAll(".csha")].every((s) => s.textContent), null, { timeout: 30000 });
    const shas = await p.evaluate(() => [...document.querySelectorAll(".csha")].map((s) => s.textContent));
    check(shas.length > 0 && shas.every((s) => s === "SHA-256 matches provenance.json"), `${pr.name}: every viewed artifact's SHA-256 matches (${shas.length})`);
    // And independently of the page.
    for (const [f, a] of Object.entries(prov.artifacts)) {
      let bytes = fs.readFileSync(path.join(site, "c", "programs", pr.name, f));
      if (f.endsWith(".gz")) bytes = zlib.gunzipSync(bytes);
      if (crypto.createHash("sha256").update(bytes).digest("hex") !== a.sha256) check(false, `${pr.name}/${f}: SHA-256 of the site file`);
    }
    const rep = fs.existsSync(path.join(site, "c", "programs", pr.name, "report.json")) ? json(`programs/${pr.name}/report.json`) : null;
    if (rep) {
      const pairs = await p.evaluate(() => [...document.querySelectorAll("#cpairs tbody tr[data-ubfree]")].map((r) => ({ ubfree: r.dataset.ubfree, text: r.textContent,
        tags: [...r.querySelectorAll(".ctag")].map((t) => t.dataset.tag) })));
      check(pairs.length === rep.pairs.length && rep.pairs.every((q, i) => pairs[i].ubfree === String(q.validatedUBFree) && pairs[i].text.includes("frontend agreement") &&
        (q.verdict === "validated" && !q.validatedUBFree) === pairs[i].tags.includes("only through source UB")),
        `${pr.name}: every pair is a frontend agreement, UB-free or flagged`);
      const ap = await p.evaluate(() => [...document.querySelectorAll("td.capplies")].map((t) => t.dataset.applies));
      const want = Object.values(rep.routes).filter((x) => x.status === "elaborated").map((x) => String(x.applicability.applies));
      check(JSON.stringify(ap.filter((x) => x !== "")) === JSON.stringify(want), `${pr.name}: per-route profile applicability shown (${want})`);
    }
    if (["asm-label", "calls", "overflow-return", "signed-narrow"].includes(pr.name)) await shot("c-program-" + pr.name);
  }
  check(errors.length === 0, `no page or console errors${errors.length ? ": " + errors.join("; ") : ""}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
