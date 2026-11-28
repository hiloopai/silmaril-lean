// The explorer's grouped graph, evidence and source views, in Chromium. The page must have been
// generated with `--source-url` and `--source-rev` (as `make pages` does); the source and byte
// views read GitHub's raw files at that commit, so this test needs the network.
//   * the graph stacks leaves by parent and status, keeps counts, expands a stack on request, and
//     draws every problem on request; problems that need attention are never stacked;
//   * a THM problem names its evidence (the answer theorem, its tier and axioms) with a source link
//     pinned to the commit, and "view" shows the declaration's line, escaped;
//   * a statement written by a `silmaril instance` command (json_format_eq_json) is found: the
//     source view (dialog and `#/source/<decl>` page) frames its lines, marks its name, highlights
//     the Lean and says that a text search found it; with a `decl_locations` row (a copy of the
//     database, served on the next port) the same view says the range is Lean's, exact;
//   * an artifact's bytes are shown bounded, as text or hex, with the registry's SHA-256 checked;
//   * a Wasm module's WAT is shown highlighted.
//
//   node provenance.mjs SITE_DIR [SHOTS_DIR]
import { spawn, execFileSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8797;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "provenance_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const sql = (q) => JSON.parse(execFileSync("python3", ["-I", "-c",
  "import sqlite3,sys,json;c=sqlite3.connect(sys.argv[1]);c.row_factory=sqlite3.Row;print(json.dumps([dict(r) for r in c.execute(sys.argv[2])]))",
  path.join(site, "project.sqlite"), q]).toString());
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 900 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const shot = async (n) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, n) }); } };
  const go = async (h) => { await p.evaluate((h) => { location.hash = h; }, h); await p.waitForTimeout(20); await settle(); };
  await p.goto(`http://127.0.0.1:${port}/index.html#/graph`);
  await settle();
  const source = await p.evaluate(() => SOURCE && { repo: SOURCE.repo, rev: SOURCE.rev, n: Object.keys(SOURCE.modules).length });
  // Without sources (a page generated outside a Git checkout) the source and byte views are skipped.
  if (source) check(source.n > 0, `the page knows its sources: ${source.repo} at ${source.rev}, ${source.n} modules`);
  else console.log("skip the page has no sources (generated without --source-url): no source or byte views to check");

  await go("#/summary");
  const docs = p.getByRole("link", { name: "Project documentation", exact: true });
  const hasPackagedDocs = await p.evaluate(() => !!(PROJECT_META && PROJECT_META.docsIndex));
  if (hasPackagedDocs) {
    check(await docs.getAttribute("href") === "#/docs/projects/README.md",
      "the Summary links to the inline project documentation view");
    if (source?.repo.toLowerCase() === "https://github.com/hiloopai/silmaril-lean") {
      const gh = p.getByRole("link", { name: "on GitHub", exact: true });
      check(await gh.getAttribute("href") === `${source.repo}/blob/${source.rev}/docs/projects/README.md`,
        "the Summary also links to the project documentation on GitHub at the source commit");
    }
  } else if (source?.repo.toLowerCase() === "https://github.com/hiloopai/silmaril-lean") {
    check(await docs.getAttribute("href") === `${source.repo}/blob/${source.rev}/docs/projects/README.md`,
      "the Summary links to the project documentation at the source commit");
  } else {
    check(await docs.count() === 0, "the Silmaril documentation link is absent on other builds");
  }
  await go("#/graph");

  // 1. the grouped graph
  await p.waitForFunction(() => window.explore.graph, null, { timeout: 30000 });
  const g = await p.evaluate(() => Object.assign({}, window.explore.graph, { nodes: cy.nodes().length,
    stackNodes: cy.nodes("[stack = 1]").map((n) => n.data("label")), att: cy.nodes("[att = 'bad']").length }));
  check(g.stacks > 0 && g.drawn + g.stacked >= g.problems && g.nodes < g.problems, `leaves are stacked: ${g.problems} problems, ${g.drawn} drawn, ${g.stacked} in ${g.stacks} stacks, ${g.nodes} nodes`);
  check(g.stackNodes.every((l) => /^\d+ × [A-Za-z/]+$/.test(l)), `stack labels count and name the status: ${g.stackNodes.slice(0, 4).join(", ")}`);
  const inStacks = await p.evaluate(() => window.explore.graph.stackMembers.map((n) => (statusInfo(statusOf.get(n)) || {}).cls || ""));
  check(inStacks.length === g.stacked && !inStacks.some((c) => c === "bad"), `no stacked problem needs attention (${g.att} drawn alone)`);
  await shot("graph-grouped.png");
  const id = await p.evaluate(() => cy.nodes("[stack = 1]").sort((a, b) => b.data("label").localeCompare(a.data("label")))[0].id());
  await p.evaluate((id) => { cy.getElementById(id).emit("tap"); }, id);
  await p.waitForSelector("#gexpand");
  const listed = await p.evaluate(() => document.querySelectorAll("#side td a").length);
  const want = await p.evaluate((id) => +cy.getElementById(id).data("label").split(" ")[0], id);
  check(listed === want, `a stack lists its ${want} problems (${listed})`);
  await shot("graph-stack.png");
  await p.click("#gexpand");
  await p.waitForFunction((n) => window.explore.graph && window.explore.graph.drawn > n, g.drawn, { timeout: 30000 });
  const g2 = await p.evaluate(() => window.explore.graph);
  check(g2.drawn > g.drawn && g2.problems === g.problems, `expanding draws them: ${g.drawn} -> ${g2.drawn} drawn`);
  await p.check("#gevery");
  await p.waitForFunction(() => window.explore.graph && window.explore.graph.stacks === 0, null, { timeout: 30000 });
  const g3 = await p.evaluate(() => Object.assign({}, window.explore.graph, { nodes: cy.nodes().length }));
  check(g3.drawn === g3.problems && g3.nodes === g3.problems, `"every problem" draws all ${g3.problems}`);
  await p.uncheck("#gevery");

  // 2. evidence and the source view
  if (source) {
    const thm = sql("SELECT p.name, a.decl, a.module FROM problems p JOIN summary s ON s.problem = p.name JOIN statuses st ON st.problem = p.name AND st.status = 'THM' " +
      "JOIN answers a ON a.decl = st.via WHERE s.summary = 'THM' AND st.via_kind IN ('answers', 'solves') ORDER BY p.name LIMIT 1")[0];
    await go("#/problem/" + encodeURIComponent(thm.name));
    const ev = await p.evaluate(() => { const u = [...document.querySelectorAll("ul.evidence li")]; return { text: u.map((l) => l.textContent).join(" | "),
      links: u.flatMap((l) => [...l.querySelectorAll("a[href^='https://github.com/']")].map((a) => a.href)) }; });
    check(ev.text.includes(thm.decl) && /kernel tier/.test(ev.text), `THM names its evidence: ${ev.text.slice(0, 160)}`);
    check(ev.links.length > 0 && ev.links.every((h) => h.includes("/blob/" + source.rev + "/")), "evidence links are pinned to the commit");
    await p.click("ul.evidence button.srcview");
    await p.waitForFunction(() => document.querySelector("dialog.dlg pre.code, dialog.dlg .err"), null, { timeout: 30000 });
    const sv = await p.evaluate(() => { const d = document.querySelector("dialog.dlg"); return { text: d.textContent, link: (d.querySelector("a") || {}).href || "",
      scripts: d.querySelectorAll("pre script, pre img").length }; });
    const last = thm.decl.split(".").pop();
    check(/#L\d+(-L\d+)?$/.test(sv.link) && sv.text.includes(last) && sv.scripts === 0, `the source view shows ${last} at ${sv.link.split("/").slice(-2).join("/")}`);
    await shot("source-view.png");
    await p.keyboard.press("Escape");

    // 2b. a statement that a command generates (`silmaril instance …`): the problem page's source
    // view finds the command, frames the whole declaration and highlights it; then the same with
    // Lean's ranges from a `decl_locations` row (a copy of the database, served apart)
    const JSON_DECL = "silmaril.selftest.languages.json_format_eq_json";
    const jp = sql(`SELECT name, decl, module FROM problems WHERE name = '${JSON_DECL}' AND decl IS NOT NULL`)[0];
    if (jp) {
      const raw = await p.evaluate((m) => (moduleFile(m) || {}).raw || null, jp.module);
      const want = raw && (await (await fetch(raw)).text()).split("\n").findIndex((l) => l.startsWith(`silmaril instance ${jp.decl} `)) + 1;
      check(want > 0, `${jp.decl} is written at line ${want} of ${raw && raw.split("/").slice(-2).join("/")}`);
      const view = (root) => p.evaluate((root) => {
        const d = document.querySelector(root), pre = d && d.querySelector("pre.lean"), g = pre && pre.querySelector(".src-decl");
        if (!g) return null;
        const pr = pre.getBoundingClientRect(), gr = g.getBoundingClientRect();
        return { link: d.querySelector("a.src-permalink").href, rows: [...g.querySelectorAll(".sl")].map((r) => +r.dataset.line), current: g.getAttribute("aria-current"),
          sel: (pre.querySelector(".lean-sel") || {}).textContent, kinds: [...new Set([...pre.querySelectorAll("[class^=lt-]")].map((s) => s.className))],
          exact: !!d.querySelector(".src-exact"), approx: !!d.querySelector(".src-approx"), note: (d.querySelector(".src-note") || {}).textContent || "",
          label: pre.getAttribute("aria-label") || "", described: !!document.getElementById(pre.getAttribute("aria-describedby") || "-"), focusable: pre.tabIndex === 0,
          visible: gr.top >= pr.top - 1 && gr.top < pr.bottom, unsafe: d.querySelectorAll("pre script, pre img, pre [onclick]").length };
      }, root);
      const expectView = (v, exact, what) => {
        check(!!v, `${what}: the source view frames a declaration`);
        if (!v) return;
        check(v.link.endsWith(`/blob/${source.rev}/examples/project/ProjectSelfTest/Languages.lean#L${want}-L${want + 2}`), `${what}: permalink to its lines (${v.link.split("/").pop()})`);
        check(v.rows.join() === [want, want + 1, want + 2].join() && v.current === "location", `${what}: lines ${v.rows.join(", ")} framed, aria-current=${v.current}`);
        check(v.sel === jp.decl, `${what}: the name is marked (${v.sel})`);
        check(["lt-command", "lt-decl-name", "lt-string", "lt-operator"].every((k) => v.kinds.includes(k)), `${what}: highlighted (${v.kinds.join(" ")})`);
        check(exact ? v.exact && !v.approx : v.approx && !v.exact, `${what}: marked ${exact ? "exact" : "approximate"}`);
        check(v.note.startsWith(`Lines ${want}–${want + 2}`) && v.described && v.focusable && /Lean source/.test(v.label), `${what}: labelled, focusable, described: ${v.note.slice(0, 60)}`);
        check(v.visible && v.unsafe === 0, `${what}: the declaration is in sight, nothing active in the code`);
      };
      // a database written by `make pages` has Lean's ranges already; an older one has none
      const ranged = sql("SELECT count(*) AS n FROM sqlite_master WHERE name = 'decl_locations'")[0].n > 0 &&
        sql(`SELECT count(*) AS n FROM decl_locations WHERE decl = '${jp.decl}'`)[0].n > 0;
      await go("#/problem/" + encodeURIComponent(jp.name));
      await shot("problem-json-format.png");
      await p.click(`button.srcview[data-decl="${jp.decl}"]`);
      await p.waitForSelector("dialog.dlg pre.lean, dialog.dlg .err", { timeout: 30000 });
      expectView(await view("dialog.dlg"), ranged, ranged ? "decl_locations of the database" : "text search");
      await shot("source-view-json-format.png");
      await p.keyboard.press("Escape");
      await go("#/source/" + encodeURIComponent(jp.decl));
      await p.waitForSelector("#main pre.lean, #main .lean-src .err", { timeout: 30000 });
      expectView(await view("#main"), ranged, "source page");
      await shot("source-page-json-format.png");

      const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "provenance-ranges-"));
      for (const f of ["index.html", "explore-sw.js"]) if (fs.existsSync(path.join(site, f))) fs.copyFileSync(path.join(site, f), path.join(tmp, f));
      fs.copyFileSync(path.join(site, "project.sqlite"), path.join(tmp, "project.sqlite"));
      execFileSync("python3", ["-I", "-c", "import sqlite3,sys;c=sqlite3.connect(sys.argv[1]);" +
        "c.execute('CREATE TABLE IF NOT EXISTS decl_locations(decl TEXT PRIMARY KEY, module TEXT NOT NULL, line INTEGER NOT NULL, col INTEGER NOT NULL, " +
        "end_line INTEGER NOT NULL, end_col INTEGER NOT NULL, sel_line INTEGER NOT NULL, sel_col INTEGER NOT NULL, sel_end_line INTEGER NOT NULL, sel_end_col INTEGER NOT NULL)');" +
        "c.execute('INSERT OR REPLACE INTO decl_locations VALUES (?,?,?,0,?,72,?,18,?,65)', (sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[4]) + 2, int(sys.argv[4]), int(sys.argv[4])));c.commit()",
        path.join(tmp, "project.sqlite"), jp.decl, jp.module, String(want)]);
      const srv2 = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
        "--root", tmp, "--port", String(port + 1), "--log", path.join(tmp, "requests.jsonl")], { stdio: "ignore" });
      try {
        await new Promise((r) => setTimeout(r, 800));
        await p.goto(`http://127.0.0.1:${port + 1}/index.html#/problem/${encodeURIComponent(jp.name)}`);
        await settle();
        await p.click(`button.srcview[data-decl="${jp.decl}"]`);
        await p.waitForSelector("dialog.dlg pre.lean, dialog.dlg .err", { timeout: 30000 });
        expectView(await view("dialog.dlg"), true, "decl_locations");
        await shot("source-view-exact.png");
        await p.keyboard.press("Escape");
      } finally { srv2.kill(); fs.rmSync(tmp, { recursive: true, force: true }); }
      await p.goto(`http://127.0.0.1:${port}/index.html#/graph`);
      await settle();
    } else console.log(`skip no problem ${JSON_DECL} with a declaration in this database`);

    // 3. an artifact's bytes
    const art = sql("SELECT a.cid, a.sha256, ap.path FROM artifacts a JOIN artifact_paths ap ON ap.artifact = a.sid WHERE ap.path LIKE '%.txt' OR ap.path LIKE '%.wasm' ORDER BY a.size LIMIT 1")[0];
    await go("#/artifact/" + encodeURIComponent(art.cid));
    await p.click("button[data-bytes]");
    await p.waitForFunction(() => document.querySelector("dialog.dlg .viewer, dialog.dlg .err"), null, { timeout: 30000 });
    const av = await p.evaluate(() => ({ text: document.querySelector("dialog.dlg").textContent, views: [...document.querySelectorAll("dialog.dlg .viewer button")].map((b) => b.textContent) }));
    check(/SHA-256 of these bytes matches the registry/.test(av.text) && av.views.includes("Hex"), `${art.path}: bytes shown (${av.views.join("/")}), SHA-256 matches`);
    await p.click("dialog.dlg .viewer button[data-v=hex]");
    check(/^00000000 {2}[0-9a-f]{2}/.test(await p.evaluate(() => document.querySelector("dialog.dlg pre").textContent)), "the hex view starts at offset 0");
    await shot("artifact-bytes.png");
    await p.keyboard.press("Escape");

  }

  // 4. WAT, highlighted
  // (a site written without `lake build wasm-pages` has none: skipped)
  const idxFile = path.join(site, "wasm", "index.json");
  const idx = fs.existsSync(idxFile) ? JSON.parse(fs.readFileSync(idxFile, "utf8")) : null;
  const mod = idx && idx.modules.find((m) => fs.existsSync(path.join(site, "wasm", "wat", m.slug + ".wat")));
  if (mod) {
    await go("#/wasm-module/" + encodeURIComponent(mod.slug));
    await p.click("button[data-lang=wat]");
    await p.waitForSelector("dialog.dlg pre .hl-k", { timeout: 30000 });
    const w = await p.evaluate(() => ({ kinds: [...new Set([...document.querySelectorAll("dialog.dlg pre span")].map((s) => s.className))], pressed: document.querySelector("dialog.dlg button[aria-pressed=true]").textContent }));
    check(w.pressed === "WAT" && w.kinds.includes("hl-k") && w.kinds.includes("hl-t"), `WAT is highlighted (${w.kinds.join(" ")})`);
    await shot("wat-view.png");
    await p.keyboard.press("Escape");
  } else if (idx) check(false, "no Wasm module with WAT in the site");
  else console.log("skip the site has no wasm/index.json: no WAT view to check");
  check(errors.length === 0, "no page errors " + errors.join("; "));
} finally {
  await b.close(); srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all ok");
