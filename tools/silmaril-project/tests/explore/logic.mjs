// The logic graph pages (docs/projects/logic-graph.md), in Chromium, on a site built from silmaril's own project
// (`make pages`):
// * Logic graph is in the navigation; the graph draws the registered institutions with typed, directed edges,
//   its legend names every edge kind and direction, and the level, edge-kind, search and go-to controls work and
//   are kept in the URL; a deep link selects and details one node or edge; Fit, zoom and Reset work;
// * the table lists every node and edge and filters and sorts; the five registries list their records, filter,
//   and link to detail pages with source declarations, endpoints, facts and crosslinks;
// * the coverage page shows the audit (with omitted declarations), the pinned Hets list and the pending families;
// * Logics in the navigation opens the table; Table | Graph are tabs (role tablist) carrying the search;
//   the #/logic-graph and #/logic-table routes keep working;
// * the source view of a registered declaration, a fact's theorem and a catalogue entry's evidence is
//   read from the declaration's own module at Lean's range (not from the registering module);
// * a narrow (phone) viewport stacks the graph and its details; no page error anywhere.
//   node logic.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8803;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "logic_requests.jsonl")], { stdio: "ignore" });
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
  const open = async (hash) => { await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`); await settle(); await p.waitForTimeout(300); };
  const shot = async (name, full = true) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: full }); } };
  const rows = (sel) => p.evaluate((sel) => [...document.querySelectorAll(sel + " tbody tr")].filter((tr) => !tr.hidden).map((tr) =>
    [...tr.children].map((td) => td.textContent.trim())), sel);
  const counts = () => p.evaluate(() => Object.fromEntries([...document.querySelectorAll(".lg-tabs a")].map((a) => [a.getAttribute("href").slice(2), +(a.querySelector("span") || { textContent: "-1" }).textContent])));

  // the entry: the navigation opens the table; Table | Graph are tabs; the search text goes along
  await open("/summary");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/logics") && !nav.includes("#/logic-graph"), `Logics is in the navigation, opening the table (${nav.filter((h) => /logic/.test(h))})`);
  // the table renders after the click's route settles: wait for its tab bar, not a fixed delay
  await p.click('#nav a[href="#/logics"]'); await settle(); await p.waitForSelector(".lg-views", { timeout: 30000 });
  const entry = await p.evaluate(() => ({ table: !!document.getElementById("lg-all"), graph: !!document.getElementById("lgcy"),
    tabs: [...document.querySelectorAll('.lg-views [role="tab"]')].map((t) => t.textContent + ":" + t.getAttribute("aria-selected")),
    list: (document.querySelector('.lg-views') || { getAttribute: () => null }).getAttribute("role") }));
  check(entry.table && !entry.graph && entry.list === "tablist" && entry.tabs.join() === "Table:true,Graph:false", `the default view is the table, with Table | Graph tabs ${JSON.stringify(entry)}`);
  await p.fill("#lg-all-q", "modal"); await p.waitForTimeout(300);
  check(/#\/logics\/\?q=modal/.test(await p.evaluate(() => location.hash)), "the table's search is in the URL");
  await p.click("#lg-tab-logic-graph"); await p.waitForSelector("#lg-q", { timeout: 60000 }); await settle(); await p.waitForTimeout(500);
  check(/#\/logic-graph\/\?q=modal/.test(await p.evaluate(() => location.hash)) && await p.inputValue("#lg-q") === "modal" &&
    await p.getAttribute("#lg-tab-logic-graph", "aria-selected") === "true", "the Graph tab opens the graph with the same search");
  await p.click("#lg-tab-logics"); await p.waitForSelector("#lg-all-q", { timeout: 60000 }); await settle(); await p.waitForTimeout(300);
  check(await p.inputValue("#lg-all-q") === "modal", "the Table tab returns with the search");
  await open("/logic-table/");
  check(await p.evaluate(() => !!document.getElementById("lg-all")) && await p.getAttribute("#lg-tab-logics", "aria-selected") === "true", "the earlier #/logic-table route still opens the table");

  // the graph
  await open("/logic-graph/");
  const n = await counts();
  check(n.institutions > 10 && n.comorphisms > 5 && n.morphisms >= 1 && n.rooms >= 1 && n.corridors >= 1, `registry counts ${JSON.stringify(n)}`);
  const g0 = await p.evaluate(() => window.explore.logicGraph);
  check(g0 && g0.level === "institution" && g0.nodes === n.institutions && g0.edges === n.comorphisms + n.morphisms, `the institution level draws every institution and institution edge ${JSON.stringify(g0)}`);
  const legend = await p.evaluate(() => document.getElementById("lg-legend").textContent);
  check(/comorphism.*sentences →, models ←/.test(legend) && /morphism.*sentences ←, models →/.test(legend) && /corridor/.test(legend), "the legend names each edge kind and its direction");
  await shot("logic-graph");
  // filters: morphisms only
  await p.uncheck("input.lg-kind[value=comorphism]");
  await p.waitForTimeout(400);
  const g1 = await p.evaluate(() => window.explore.logicGraph);
  check(g1.edges === n.morphisms, `edge-kind filter: morphisms only (${g1.edges})`);
  check(/kinds=morphism%2Ccorridor|kinds=morphism,corridor/.test(await p.evaluate(() => location.hash)), "the filter is kept in the URL");
  await p.uncheck("#lg-iso"); await p.waitForTimeout(400);
  const g2 = await p.evaluate(() => window.explore.logicGraph);
  check(g2.nodes < g1.nodes && g2.nodes >= 2, `hiding unconnected nodes (${g1.nodes} → ${g2.nodes})`);
  await p.click("#lg-reset"); await settle(); await p.waitForTimeout(400);
  check((await p.evaluate(() => window.explore.logicGraph)).edges === g0.edges, "Reset restores every edge");
  // levels
  await p.selectOption("#lg-level", "both"); await p.waitForTimeout(500);
  const g3 = await p.evaluate(() => window.explore.logicGraph);
  check(g3.nodes === n.institutions + n.rooms && g3.fibers >= 1, `both levels: rooms with their fibers ${JSON.stringify(g3)}`);
  await shot("logic-graph-both");
  // search
  await p.fill("#lg-q", "first-order"); await p.waitForTimeout(600);
  check(/match/.test(await p.textContent("#lg-count")), "search highlights matches");
  // a deep link selects an edge and details it
  const edge = await p.evaluate(() => [...document.querySelectorAll("#lg-go option")].map((o) => o.value).find((v) => v.startsWith("comorphism:")));
  await open("/logic-graph/" + encodeURIComponent(edge));
  const side = await p.textContent("#lgside");
  check(/comorphism/.test(side) && /from/.test(side) && /to/.test(side) && /declaration/.test(side), `deep link ${edge} details the edge`);
  check(await p.evaluate((id) => window.explore && document.querySelector("#lg-go").value === id, edge), "go-to shows the selection");
  await shot("logic-graph-selected");
  // go to a room switches the level
  const room = await p.evaluate(() => [...document.querySelectorAll("#lg-go option")].map((o) => o.value).find((v) => v.startsWith("room:")));
  await p.selectOption("#lg-go", room); await p.waitForTimeout(600);
  check((await p.evaluate(() => window.explore.logicGraph)).level !== "institution" && /room/.test(await p.textContent("#lgside")), "go to a room switches to the room level");
  // zoom and fit keep a graph drawn
  await p.click("#lg-zin"); await p.click("#lg-fit");
  check(await p.evaluate(() => !!document.querySelector("#lgcy canvas")), "zoom and fit keep the canvas");

  // the table
  await open("/logics/");
  const all = await rows("#lg-all");
  check(all.length === n.institutions + n.rooms + n.comorphisms + n.morphisms + n.corridors, `the table lists every node and edge (${all.length})`);
  await p.fill("#lg-all-q", "morphism"); await p.waitForTimeout(200);
  const fm = await rows("#lg-all");
  check(fm.length > 0 && fm.length < all.length && /of/.test(await p.textContent("#lg-all-n")), `filter (${fm.length})`);
  check(/q=morphism/.test(await p.evaluate(() => location.hash)), "the table filter is kept in the URL");
  await p.fill("#lg-all-q", ""); await p.click("#lg-all th[data-j='1'] button");
  check(await p.getAttribute("#lg-all th[data-j='1']", "aria-sort") === "ascending", "sorting by a column");
  await shot("logic-table");

  // the registries and a detail page each
  for (const [route, kind] of [["institutions", "institution"], ["comorphisms", "comorphism"], ["morphisms", "morphism"], ["rooms", "room"], ["corridors", "corridor"]]) {
    await open("/" + route);
    const rs = await rows(`#lg-${route}`);
    check(rs.length === n[route], `${route}: ${rs.length} rows`);
    const href = await p.evaluate((t) => document.querySelector(`#lg-${t} tbody tr a`).getAttribute("href"), route);
    await open(href.slice(1));
    const dl = await p.textContent("main");
    check(dl.includes("Lean declaration") && dl.includes(kind) && (kind === "institution" || kind === "room" ? /outgoing/.test(dl) : /from/.test(dl) && /direction/.test(dl)),
      `${kind} page ${href} has its declaration, ${kind === "institution" || kind === "room" ? "edges" : "endpoints and direction"}`);
    if (route === "comorphisms") await shot("logic-comorphism");
  }
  await open("/institutions");
  await shot("logic-institutions");

  // the source view: a registered declaration is shown from its own module (Lean's range), not from the
  // module of the record that registers it; likewise a fact's theorem and a catalogue entry's evidence
  if (await p.evaluate(() => document.getElementById("source-meta").textContent.trim() !== "null")) {
    for (const [decl, file] of [["Silmaril.SSA.LambdaRTL.Institution.rtlObs", "Silmaril/SSA/LambdaRTL/Institution/Defs.lean"],
        ["Silmaril.Logic.Institution.Examples.plToFol_modelExpansive", "Silmaril/Logic/Institution/Examples/Comorphisms.lean"],
        ["Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.sourceInst", "Silmaril/Proofs/Logic/Algebraic/InitialMatching/FiniteSortedInstitution.lean"],
        ["Silmaril.Logic.Metamath.Peano.ZF.ZF0", "Silmaril/Logic/Metamath/Peano/ZFC.lean"]]) {
      await open("/source/" + encodeURIComponent(decl));
      await p.waitForFunction(() => !document.querySelector(".lean-src") || !/reading the Lean source/.test(document.querySelector(".lean-src").textContent), null, { timeout: 30000 });
      const v = await p.evaluate(() => ({ where: (document.querySelector(".src-permalink") || {}).textContent || "", exact: !!document.querySelector(".src-exact"),
        sel: (document.querySelector(".sl-sel") || {}).textContent || "", text: (document.querySelector(".lean-src") || {}).textContent || "" }));
      const last = decl.split(".").pop();
      check(v.where.startsWith(file) && v.exact && v.sel.includes(last) && !/No declaration of/.test(v.text),
        `source of ${decl}: ${v.where} ${v.exact ? "exact" : "not exact"}; the marked line names ${last}`);
    }
    // from the institution's page: its declaration in its own module
    await open("/institution/" + encodeURIComponent("ssa.lambda_rtl.institution.rtl_obs"));
    await p.click("main button.srcview"); await p.waitForTimeout(300);
    await p.waitForFunction(() => { const d = document.querySelector("dialog.dlg .lean-src"); return d && !/reading the Lean source/.test(d.textContent); }, null, { timeout: 30000 });
    const dv = await p.evaluate(() => ({ where: document.querySelector("dialog.dlg .src-permalink").textContent, exact: !!document.querySelector("dialog.dlg .src-exact") }));
    check(dv.where.startsWith("Silmaril/SSA/LambdaRTL/Institution/Defs.lean") && dv.exact, `the institution page's "view" shows ${dv.where}`);
    await p.keyboard.press("Escape");
  }

  // consequence systems of the logics: a tab, a table of systems with their rooms and readings, and the
  // proved relations (soundness of derivability for semantic consequence, inclusions, the structural laws)
  await open("/logics/");
  check(await p.evaluate(() => !!document.querySelector('.lg-tabs a[href="#/logic-consequence"]')), "the logic pages link the consequence systems");
  await open("/logic-consequence/"); await p.waitForSelector("#lg-cons-rel", { timeout: 60000 });
  const cs = await rows("#lg-cons");
  const csText = cs.map((r) => r.join(" | ")).join("\n");
  check(cs.length >= 18, `consequence systems of the logics (${cs.length})`);
  for (const t of ["PA (peano.mm)", "ZF (set.mm)", "ZFC (set.mm)", "Metamath over set.mm's grammar", "HOL: the kernel", "Extensional MLTT", "Intensional MLTT"])
    check(csText.includes(t), `the table lists ${t}`);
  check(cs.filter((r) => r[1] === "semantic").every((r) => /room/.test(r[2])), "every semantic reading names its room");
  const rel = await rows("#lg-cons-rel");
  const sound = rel.filter((r) => r[1] === "is sound for");
  check(sound.length >= 9 && sound.every((r) => /proved/.test(r[3])), `soundness relations, all proved (${sound.length})`);
  check(rel.some((r) => /ZF \(set\.mm\): derivability/.test(r[0]) && r[1] === "is included in" && /ZFC \(set\.mm\): derivability/.test(r[2])), "ZF's consequences are ZFC's (an inclusion, not soundness)");
  check(!rel.some((r) => /complete/.test(r[1])), "no completeness is claimed");
  await p.fill("#lg-cons-q", "zfc");
  await p.waitForTimeout(200);
  check(/q=zfc/.test(await p.evaluate(() => location.hash)) && (await rows("#lg-cons")).length >= 2, "the search is kept in the URL");
  // the coverage matrix: every family against every feature, no completeness claimed, absences explained
  const mx = await p.evaluate(() => {
    const t = document.getElementById("lg-matrix"); if (!t) return null;
    const heads = [...t.querySelectorAll("thead th")].map((th) => th.textContent);
    const rowsM = [...t.querySelectorAll("tbody tr")].map((tr) => ({ fam: tr.querySelector("th").textContent,
      cells: [...tr.querySelectorAll("td")].map((td) => ({ s: td.dataset.strength || "", note: (td.querySelector(".lg-mx-note") || {}).textContent || "",
        links: td.querySelectorAll(".lg-mx-decls a").length })) }));
    return { heads, rows: rowsM };
  });
  check(mx && mx.rows.length === 8 && mx.heads.length === 14, `the coverage matrix: 8 families, 13 features (${mx && mx.rows.length}, ${mx && mx.heads.length - 1})`);
  if (mx) {
    const ci = mx.heads.indexOf("completeness") - 1;
    check(mx.rows.every((r) => r.cells.every((c) => c.s && c.links > 0)), "every cell has a status and names its declarations");
    check(ci >= 0 && mx.rows.every((r) => r.cells[ci].s === "not claimed"), "completeness is not claimed for any family");
    check(mx.rows.every((r) => r.cells.every((c) => c.s !== "absent" || c.note)), "every absent cell says why");
    const hol = mx.rows.find((r) => r.fam === "HOL"), si = mx.heads.indexOf("concrete syntax") - 1;
    check(hol && hol.cells[si].s === "proved", "HOL's concrete syntax is proved to round-trip");
    // formal definition and explorer registration are separate columns
    const ea = mx.heads.indexOf("explorer: abstract") - 1, ec = mx.heads.indexOf("explorer: concrete") - 1;
    check(ea >= 0 && ec >= 0, "the matrix separates registering abstract and concrete systems from defining them");
    const concreteRegistered = mx.rows.filter((r) => r.cells[ec].s === "registered").map((r) => r.fam).sort();
    check(JSON.stringify(concreteRegistered) === JSON.stringify(["HOL", "extensional MLTT"]), `concrete systems are registered for exactly HOL and extensional MLTT (${concreteRegistered})`);
  }
  const noteLinks = await p.evaluate(() => [...document.querySelectorAll("#lg-matrix td.lg-mx[data-strength=registered] .lg-mx-note a")].map((a) => a.getAttribute("href")));
  check(["#/institution/logic.consequence.concrete.hol.institution", "#/comorphism/logic.consequence.concrete.mltt.to_abstract",
    "#/system/logic.consequence.concrete.hol.kernel"].every((h) => noteLinks.includes(h)), "the matrix links the registered concrete records");

  // the concrete systems and their relations to the abstract ones
  await p.fill("#lg-cons-q", "S-expressions"); await p.waitForTimeout(200);
  const conc = await rows("#lg-cons");
  check(conc.length === 5, `five consequence systems over S-expressions (${conc.length})`);
  const crel = (await rows("#lg-cons-rel")).filter((r) => /S-expressions/.test(r[0]) || /S-expressions/.test(r[2]));
  const kinds = (k) => crel.filter((r) => r[1] === k && /proved/.test(r[3])).length;
  check(kinds("translates into") === 6 && kinds("translates conservatively (reflects) into") === 4 && kinds("is sound for") === 2,
    `concrete translations to and from the abstract systems, reflection and soundness, all proved (${crel.length})`);
  check(crel.some((r) => /HOL over S-expressions: the kernel/.test(r[0]) && r[1] === "translates into" && /HOL: the kernel on propositions/.test(r[2])),
    "the concrete HOL kernel translates into the abstract kernel");
  await p.fill("#lg-cons-q", "");
  await shot("logic-consequence");
  await open("/system/" + encodeURIComponent("logic.consequence.metamath.zfc.entails"));
  await p.waitForFunction(() => /over the sentences of/.test(document.querySelector("main").textContent), null, { timeout: 60000 });
  const sysText = await p.textContent("main");
  check(/semantic consequence/.test(sysText) && /logic\.institution\.metatheory\.metamath\.room/.test(sysText) && /Silmaril\.Consequence\.Metamath\.zf/.test(sysText),
    "a system's page shows its reading and its room");
  await open("/room/" + encodeURIComponent("logic.institution.metatheory.metamath.room"));
  await p.waitForFunction(() => /consequence systems/.test(document.querySelector("main").textContent), null, { timeout: 60000 });
  const roomText = await p.textContent("main");
  check(/consequence systems/.test(roomText) && /PA \(peano\.mm\)/.test(roomText) && /ZFC \(set\.mm\)/.test(roomText), "the Metamath room lists its consequence systems");

  // the concrete institutions in the logic graph: their pages, the comorphisms to the abstract institutions, the graph
  await open("/logics/?q=concrete.hol");
  const concNodes = (await rows("#lg-all")).filter((r) => /logic\.consequence\.concrete\./.test(r[1]));
  check(concNodes.length === 4, `the concrete HOL institution, room, corridor and comorphism are in the table (${concNodes.length})`);
  await open("/institution/" + encodeURIComponent("logic.consequence.concrete.mltt.institution"));
  const ci = await p.textContent("main");
  check(/logic\.consequence\.concrete\.mltt\.to_abstract/.test(ci) && /logic\.type_theory\.extensional_mltt\.institution\.bundled/.test(ci),
    "the concrete MLTT institution's page shows its comorphism to abstract MLTT");
  await open("/comorphism/" + encodeURIComponent("logic.consequence.concrete.hol.to_abstract"));
  const cc = await p.textContent("main");
  check(/logic\.consequence\.concrete\.hol\.institution/.test(cc) && /logic\.institution\.metatheory\.hol\.institution/.test(cc) && /model_expansive/.test(cc),
    "the HOL comorphism goes from concrete to abstract HOL, model-expansive");
  await open("/corridor/" + encodeURIComponent("logic.consequence.concrete.mltt.corridor"));
  check(/logic\.type_theory\.extensional_mltt\.institution\.room/.test(await p.textContent("main")), "the MLTT corridor goes to the abstract MLTT room");
  await open("/logic-graph/" + encodeURIComponent("comorphism:logic.consequence.concrete.hol.to_abstract"));
  check(/to_abstract/.test(await p.textContent("#lgside")), "the graph selects the concrete-to-abstract comorphism");
  await open("/room/" + encodeURIComponent("logic.consequence.concrete.mltt.room"));
  check(/Extensional MLTT over S-expressions: derivability/.test(await p.textContent("main")), "the concrete MLTT room lists its consequence systems");
  // the source of the concrete declarations and of the parser examples
  if (await p.evaluate(() => document.getElementById("source-meta").textContent.trim() !== "null")) {
    for (const [decl, file] of [["Silmaril.Consequence.Concrete.holToAbstract", "Silmaril/Logic/Consequence/Concrete/Defs.lean"],
        ["Silmaril.Logic.HOLLight.SExp.parseTm_printTm", "Silmaril/Logic/HOLLight/SExp/Thms.lean"],
        ["Silmaril.Logic.HOLLight.SExp.Examples.idEqId", "Silmaril/Logic/HOLLight/SExp/Examples.lean"],
        ["Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Examples.polyId", "Silmaril/Logic/TypeTheory/ExtensionalMLTT/SExp/Examples.lean"]]) {
      await open("/source/" + encodeURIComponent(decl));
      await p.waitForFunction(() => !document.querySelector(".lean-src") || !/reading the Lean source/.test(document.querySelector(".lean-src").textContent), null, { timeout: 30000 });
      const v = await p.evaluate(() => ({ where: (document.querySelector(".src-permalink") || {}).textContent || "", exact: !!document.querySelector(".src-exact"),
        text: (document.querySelector(".lean-src") || {}).textContent || "" }));
      check(v.where.startsWith(file) && v.exact && (!/Examples/.test(file) || /#guard/.test(v.text)), `source of ${decl}: ${v.where} ${v.exact ? "exact" : "not exact"}`);
    }
  }

  // coverage
  await open("/logic-coverage/");
  const cov = await p.textContent("main");
  check(/Audit of Lean declarations/.test(cov) && /declarations/.test(cov) && /omitted/.test(cov), "coverage: the audit");
  check((await rows("#lg-hets")).length === 39 + 75, "coverage: the pinned Hets list (39 logics, 75 comorphisms)");
  const catRows = await rows("#lg-catalogue");
  const catDb = await p.evaluate(() => document.querySelectorAll("#lg-catalogue tbody tr").length);
  check(catDb === 295 || catDb === 0, `coverage: the curated catalogue, entry by entry (${catDb} rows)`);
  if (catDb) {
    const statuses = new Set(catRows.map((r) => r[3]));
    check(["registered", "represented", "not-institution-typed", "prospective"].every((x) => statuses.has(x)), `catalogue statuses ${[...statuses]}`);
    check(catRows.filter((r) => r[3] === "not-institution-typed").every((r) => r[6].length > 0), "every entry that is not institution-typed says why");
    check(catRows.filter((r) => r[3] === "registered").every((r) => r[4].length > 0), "every registered entry names its records");
  }
  const exRows = await rows("#lg-exclusions");
  check(exRows.length > 0 && exRows.every((r) => r[3].length > 0), `coverage: what the graph leaves out, each with a reason (${exRows.length})`);
  check(["unregistrable-declaration", "fixture-dependent", "out-of-scope"].every((c) => exRows.some((r) => r[0] === c)), "all three exclusion categories are listed");
  check(/Logic families not yet in this repository/.test(cov) && (/pending-port|in-review/.test(cov) || /None listed/.test(cov)),
    "coverage: the pending families (or that none is listed)");
  await shot("logic-coverage");

  // a phone
  const m = await b.newPage({ viewport: { width: 390, height: 844 }, isMobile: true });
  m.on("pageerror", (e) => errors.push(e.message));
  await m.goto(`http://127.0.0.1:${port}/index.html#/logic-graph/` + encodeURIComponent(edge));
  await m.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  await m.waitForTimeout(600);
  const box = await m.evaluate(() => { const a = document.getElementById("lgcy").getBoundingClientRect(), s = document.getElementById("lgside").getBoundingClientRect();
    return { cyW: a.width, sideTop: s.top, cyBottom: a.bottom, scrollW: document.documentElement.scrollWidth }; });
  check(box.cyW <= 390 && box.sideTop >= box.cyBottom - 1, `narrow: the details stack under the graph ${JSON.stringify(box)}`);
  if (shots) await m.screenshot({ path: path.join(shots, "logic-graph-phone.png"), fullPage: true });
  await m.goto(`http://127.0.0.1:${port}/index.html#/comorphisms`);
  await m.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  if (shots) await m.screenshot({ path: path.join(shots, "logic-comorphisms-phone.png"), fullPage: false });

  check(errors.length === 0, `no page errors ${JSON.stringify(errors)}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
