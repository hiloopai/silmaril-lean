// Exercise the generated Explorer against the project's golden SQLite fixture plus
// deliberately unaudited and out-of-profile display cases. No proofs are created.
// node profiles.mjs SILMARIL_PROJECT_BINARY [SHOTS_DIR]
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const here = path.dirname(fileURLToPath(import.meta.url));
const binary = path.resolve(process.argv[2]);
const shots = process.argv[3] && path.resolve(process.argv[3]);
const siteRoot = fs.mkdtempSync(path.join(os.tmpdir(), "explorer-profiles-"));
const site = path.join(siteRoot, "silmaril-lean");
fs.mkdirSync(site, { recursive: true });
const db = path.join(site, "project.sqlite");
const port = 8822;
const rev = "0123456789abcdef0123456789abcdef01234567";
let server, browser;
try {
  execFileSync("python3", ["-I", "-c", `
import json, pathlib, sqlite3, sys
db, legacy, nodoc_db, fixture, markings_fixture = sys.argv[1:]
with sqlite3.connect(db) as c:
    c.executescript(pathlib.Path(fixture).read_text())
    c.execute("UPDATE projects SET name = 'Explorer fixture' WHERE origin = 'local'")
    for decl, tier in [("Fixture.empty", "kernel"), ("Fixture.outside", "kernel"), ("Fixture.unknown", "external")]:
        c.execute("INSERT INTO answers (decl, problem, status, source, module, tier) VALUES(?, 'ok.a', 'THM', 'answers', 'Fixture', ?)", (decl, tier))
    for axiom in ["«test, name with <b>markup</b>»", "sorryAx", "propext"]:
        c.execute("INSERT INTO answer_axioms VALUES ('Fixture.outside', ?)", (axiom,))
    for name, axioms in [("fixture.standard", '["Classical.choice"]'), ("fixture.empty", '[]'),
                         ("fixture.unknown", 'null'), ("fixture.unreadable", '{"invalid":true}'),
                         ("fixture.outside", '["Fixture.extra"]')]:
        c.execute("INSERT INTO logic_properties (name, decl, role, statement, axioms, module, origin) VALUES(?, ?, 'consistency', 'Fixture statement', ?, 'Fixture', 'local')",
                  (name, name, axioms))
    c.executescript("""
        INSERT INTO ir_families (sid, name, title, module, origin)
          VALUES ('f', 'fixture.ir', 'Example IR', 'Fixture', 'local');
        INSERT INTO ir_syntax_kinds (sid, name, title, module, origin)
          VALUES ('k', 'fixture.syntax', 'Blocks', 'Fixture', 'local');
        INSERT INTO ir_subsets (sid, name, family, syntax_kind, decl, title, module, origin)
          VALUES ('s', 'fixture.subset', 'fixture.ir', 'fixture.syntax', 'Fixture.Block', 'Blocks', 'Fixture', 'local');
        INSERT INTO institutions (sid, name, decl, arity, type, levels, title, module, origin)
          VALUES ('i', 'fixture.logic', 'Fixture.inst', 0, 'Inst', '', 'Example institution', 'Fixture', 'local');
        INSERT INTO ir_models (sid, name, subset, semantics, decl, institution, title, module, origin)
          VALUES ('m', 'fixture.denote', 'fixture.subset', 'denotational', 'Fixture.denote', 'fixture.logic',
                  'Denotation', 'Fixture', 'local');
    """)
    # Add 45 open problems and 1 deprecated problem so search-before-cap, pagination and deprecation exclusion are exercised.
    for idx in range(1, 46):
        pname = f"fixture.open.p{idx:02d}"
        ptitle = f"Open obligation {idx:02d}" + (" needle-target" if idx == 45 else "")
        c.execute("INSERT INTO problems (sid, name, kind, decl, arity, module, origin, detached, title) VALUES (?, ?, 'prop', ?, 0, 'Fixture', 'local', 0, ?)",
                  (f"sid_open_{idx:02d}", pname, f"Fixture.open_{idx:02d}", ptitle))
        c.execute("INSERT INTO summary (problem, summary, verdict, tier) VALUES (?, 'OPN', 'unknown', 'tool')", (pname,))
    c.execute("INSERT INTO problems (sid, name, kind, decl, arity, module, origin, detached, title) VALUES ('sid_dep_1', 'fixture.old_bad', 'prop', 'Fixture.old_bad', 0, 'Fixture', 'local', 0, 'Deprecated statement')")
    c.execute("INSERT INTO summary (problem, summary, verdict, tier) VALUES ('fixture.old_bad', 'OPN', 'unknown', 'tool')")
    c.execute("INSERT INTO deprecations (name, kind, reason, module, origin) VALUES ('fixture.old_bad', 'problem', 'wrong assumption', 'Fixture', 'local')")
    c.execute("INSERT INTO deprecated_problems (problem, via_kind, via) VALUES ('fixture.old_bad', 'self', 'fixture.old_bad')")
    with sqlite3.connect(legacy) as old:
        c.commit()
        c.backup(old)
        for table in ["answer_axioms", "ir_models", "ir_subsets", "ir_syntax_kinds", "ir_families"]:
            old.execute(f"DROP TABLE {table}")
    with sqlite3.connect(nodoc_db) as nd:
        c.backup(nd)
        nd.execute("UPDATE projects SET description = NULL WHERE origin = 'local'")
`, db, path.join(site, "legacy.sqlite"), path.join(site, "nodoc.sqlite"), path.join(here, "../project/ok/project.sql"), path.join(here, "../project/markings/project.sql")]);
  execFileSync(binary, [
    "explore", "--db", db, "--out", path.join(site, "index.html"),
    "--source-url", "https://github.com/hiloopai/silmaril-lean", "--source-rev", rev,
  ]);
  // Add a packaged SVG asset under docs/projects/ to test relative image asset rendering inside the subpath.
  fs.writeFileSync(path.join(site, "docs/projects/fixture-badge.svg"),
    '<svg xmlns="http://www.w3.org/2000/svg" width="40" height="16"><rect width="40" height="16" fill="#2f5d9e"/></svg>');
  fs.writeFileSync(path.join(site, "docs/projects/fixture-guide.md"),
    `# Fixture guide\n\n![Fixture badge](fixture-badge.svg)\n\n\`\`\`mermaid\nflowchart LR\n  A[Start] --> B[Finish]\n\`\`\`\n\n\`\`\`mermaid\nsequenceDiagram\n  A->>B: Fallback\n\`\`\`\n`);

  // Also generate a custom project fixture (with project-specific help in silmaril.toml) and a no-docs/no-description project fixture.
  const customProj = path.join(siteRoot, "custom-proj");
  const customSite = path.join(siteRoot, "custom-site");
  fs.mkdirSync(path.join(customProj, "docs"), { recursive: true });
  fs.mkdirSync(customSite, { recursive: true });
  fs.copyFileSync(path.join(site, "nodoc.sqlite"), path.join(customSite, "project.sqlite"));
  fs.writeFileSync(path.join(customProj, "silmaril.toml"),
    `schema = "silmaril.project.v0.1"\nsid = "${"2".repeat(64)}"\nname = "custom-demo"\ndescription = "Manifest description fallback"\nhelp = "docs/custom-help.md"\n`);
  fs.writeFileSync(path.join(customProj, "docs/custom-help.md"),
    `# Custom Project Help\n\nUse \`sil project check\` to verify **custom-demo**.\n`);
  execFileSync(binary, [
    "explore", "--dir", customProj, "--db", path.join(customSite, "project.sqlite"),
    "--out", path.join(customSite, "index.html"),
  ]);

  const bareProj = path.join(siteRoot, "bare-proj");
  const bareSite = path.join(siteRoot, "bare-site");
  fs.mkdirSync(bareProj, { recursive: true });
  fs.mkdirSync(bareSite, { recursive: true });
  fs.copyFileSync(path.join(site, "nodoc.sqlite"), path.join(bareSite, "project.sqlite"));
  fs.writeFileSync(path.join(bareProj, "silmaril.toml"),
    `schema = "silmaril.project.v0.1"\nsid = "${"3".repeat(64)}"\nname = "bare-demo"\n`);
  execFileSync(binary, [
    "explore", "--dir", bareProj, "--db", path.join(bareSite, "project.sqlite"),
    "--out", path.join(bareSite, "index.html"),
  ]);

  // Match the ELF sidecar's contract while testing the contradictory and missing metadata cases.
  const theorem = (name, axioms, status = "checked", kernelOnly = true) => ({
    decl: `Fixture.${name}`, short: name, label: name, axioms, status, kernelOnly, module: "Fixture",
    file: "Fixture.lean", kind: "part", windows: [],
  });
  fs.mkdirSync(path.join(site, "elf/f"), { recursive: true });
  fs.writeFileSync(path.join(site, "elf/f/fixture.json"), JSON.stringify({
    title: "ELF fixture", slug: "fixture", path: "fixture.bin", size: 16, sha256: "0",
    header: { type: "EXEC", machine: "Machine" },
    theorems: [
      theorem("checked", ["propext"]), theorem("missing", undefined), theorem("outside", ["Fixture.extra"]),
      theorem("unconfirmed", ["Quot.sound"], "unknown", false),
    ],
  }));
  server = spawn("python3", ["-I", path.join(here, "pages_server.py"),
    "--root", siteRoot, "--port", String(port), "--log", path.join(siteRoot, "requests.jsonl")], { stdio: "inherit" });
  const base = `http://127.0.0.1:${port}/silmaril-lean`;
  for (let attempt = 0; ; attempt++) {
    // The readiness check only needs headers. An unread GET body can leave
    // Node 22's fetch parser paused when the server closes the connection.
    if (await fetch(`${base}/index.html`, { method: "HEAD" }).then((r) => r.ok, () => false)) break;
    if (attempt === 49) throw new Error("Explorer test server did not start");
    await new Promise((resolve) => setTimeout(resolve, 100));
  }

  browser = await chromium.launch({ executablePath: process.env.CHROME ||
    (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome")
      ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
  const errors = [];
  const desktop = await browser.newPage({ viewport: { width: 1440, height: 950 } });
  const mobile = await browser.newPage({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
  for (const page of [desktop, mobile]) page.on("pageerror", (err) => errors.push(err.message));
  const settle = (page, view) => page.waitForFunction((id) =>
    window.explore?.ready && !window.explore.busy && window.explore.view === id && window.explore.hash === location.hash, view, { timeout: 30000 });
  const open = async (page, hash, view, query = "") => {
    await page.goto(`${base}/index.html${query}#/${hash}`);
    await settle(page, view);
    assert.equal(await page.locator("main .err").count(), 0, await page.locator("main").innerText());
  };
  const shot = async (page, name) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, name + ".png") });
  };
  const details = (page) => page.locator(".axiom-tooltip");
  const answer = (page, name) => page.locator("main tr").filter({ hasText: name }).locator(".axiom-chip");

  await open(desktop, "summary", "summary");
  assert.equal(await desktop.locator("header #nav").count(), 0);
  assert.equal(await desktop.locator("#nav a[aria-current=page]").innerText(), "Summary");
  assert.equal(await desktop.getByRole("region", { name: "Explore the project" }).getByRole("link", { name: "Formal" }).count(), 1);
  // Front-page checks: description, stats strip, search before cap, pagination, deprecation exclusion, help dialog
  assert.match(await desktop.locator(".project-description").innerText(), /Golden case: every record kind/);
  assert.equal(await desktop.locator(".project-facts .fact-item").count(), 3);
  assert.ok(!(await desktop.locator("main").innerText()).includes("(not counted above)"));
  assert.equal(await desktop.locator(".att a.card[href*='excluded=deprecated']").count(), 0);
  assert.equal(await desktop.locator(".excluded-routes a[href*='excluded=deprecated']").count(), 1);
  assert.match(await desktop.locator("#open-count").innerText(), /showing 1–40 of 51 open problems/);
  await desktop.fill("#open-search", "needle-target");
  assert.match(await desktop.locator("#open-count").innerText(), /showing 1–1 of 1 matching \(51 total open\)/);
  assert.match(await desktop.locator("#open-results").innerText(), /fixture\.open\.p45/);
  await desktop.fill("#open-search", "");
  assert.match(await desktop.locator("#open-count").innerText(), /showing 1–40 of 51 open problems/);
  await desktop.click("#open-next");
  assert.match(await desktop.locator("#open-count").innerText(), /showing 41–51 of 51 open problems/);
  assert.match(await desktop.locator("#open-results").innerText(), /fixture\.open\.p45/);
  await desktop.click("#open-prev");
  assert.match(await desktop.locator("#open-count").innerText(), /showing 1–40 of 51 open problems/);

  // Help dialog on main site (general Silmaril Projects help, keyboard Escape)
  await desktop.click("#help-btn");
  await desktop.waitForSelector("dialog.dlg[open]");
  assert.match(await desktop.locator("dialog.dlg").innerText(), /Silmaril Projects Help/);
  assert.equal(await desktop.locator("dialog.dlg [data-general-help]").count(), 1);
  await desktop.keyboard.press("Escape");
  await desktop.waitForFunction(() => !document.querySelector("dialog.dlg"));
  await shot(desktop, "desktop-index");

  // Inline project docs under URL subpath: Summary -> Docs index -> nested RVSDG & Sea of Nodes -> Mermaid SVG -> fragments -> back/refresh
  const docLink = desktop.getByRole("link", { name: "Project documentation", exact: true });
  assert.equal(await docLink.getAttribute("href"), "#/docs/projects/README.md");
  await docLink.click();
  await settle(desktop, "docs");
  assert.match(await desktop.locator("#doc-content h1").innerText(), /Projects/);
  // Navigate to nested RVSDG topic index
  await desktop.locator("#doc-content").getByRole("link", { name: "RVSDG", exact: true }).click();
  await settle(desktop, "docs");
  assert.equal(await desktop.evaluate(() => location.hash), "#/docs/projects/rvsdg/README.md");
  assert.match(await desktop.locator("#doc-content h1").innerText(), /RVSDG/);
  // Navigate to RVSDG overview
  await desktop.locator("#doc-content").getByRole("link", { name: "RVSDG overview", exact: true }).click();
  await settle(desktop, "docs");
  assert.equal(await desktop.evaluate(() => location.hash), "#/docs/projects/rvsdg/overview.md");
  // Navigate to legacy pointer with fragment forwarding (rvsdg.md#coloured-firing-semantics -> rvsdg/overview.md#coloured-firing-semantics)
  await open(desktop, "docs/projects/rvsdg.md#coloured-firing-semantics", "docs");
  await desktop.locator("#doc-content").getByRole("link", { name: "Coloured firing semantics", exact: true }).click();
  await settle(desktop, "docs");
  assert.equal(await desktop.evaluate(() => location.hash), "#/docs/projects/rvsdg/overview.md#coloured-firing-semantics");
  assert.equal(await desktop.locator("#doc-content #coloured-firing-semantics").count(), 1);
  // Navigate to nested Sea of Nodes topic index and a leaf guide
  await open(desktop, "docs/projects/sea-of-nodes/README.md", "docs");
  assert.match(await desktop.locator("#doc-content h1").innerText(), /Sea of Nodes/);
  await desktop.locator("#doc-content").getByRole("link", { name: "source-to-Lean coverage ledger", exact: true }).click();
  await settle(desktop, "docs");
  assert.equal(await desktop.evaluate(() => location.hash), "#/docs/projects/sea-of-nodes/coverage.md");
  // Real document with Mermaid diagram, repo source links and external links
  await open(desktop, "docs/projects/sqlite-track-d/README.md#observation-maps-and-their-limits", "docs");
  assert.equal(await desktop.locator("#doc-content figure.doc-mermaid[data-mermaid-status='rendered'] svg").count(), 2);
  await shot(desktop, "desktop-real-mermaid");
  const coreLink = desktop.locator("#doc-content").getByRole("link", { name: "Core", exact: true });
  assert.equal(await coreLink.getAttribute("href"), `https://github.com/hiloopai/silmaril-lean/blob/${rev}/Silmaril/Semantics/SQLite/Relational/All.lean`);
  const extLink = desktop.locator("#doc-content").getByRole("link", { name: "Architecture", exact: true });
  assert.equal(await extLink.getAttribute("href"), "https://sqlite.org/arch.html");
  // Browser back and reload preserve the deep link and re-render
  await desktop.goBack();
  await settle(desktop, "docs");
  assert.equal(await desktop.evaluate(() => location.hash), "#/docs/projects/sea-of-nodes/coverage.md");
  await desktop.reload();
  await settle(desktop, "docs");
  assert.match(await desktop.locator("#doc-content h1").innerText(), /Sea of Nodes/);
  // Fixture guide with local SVG image, Mermaid diagram and Mermaid fallback
  await open(desktop, "docs/projects/fixture-guide.md", "docs");
  assert.equal(await desktop.locator("#doc-content img.doc-img").getAttribute("src"), "docs/projects/fixture-badge.svg");
  assert.equal(await desktop.locator("#doc-content figure[data-mermaid-status='rendered'] svg").count(), 1);
  assert.equal(await desktop.locator("#doc-content figure[data-mermaid-status='fallback'] pre.code").count(), 1);
  await shot(desktop, "desktop-docs");

  // Custom project fixture: manifest description fallback and project-specific help doc
  await desktop.goto(`http://127.0.0.1:${port}/custom-site/index.html#/summary`);
  await settle(desktop, "summary");
  assert.equal(await desktop.locator(".project-description").innerText(), "Manifest description fallback");
  await desktop.click("#help-btn");
  await desktop.waitForSelector("dialog.dlg[open]");
  assert.equal(await desktop.locator("dialog.dlg [data-project-help='doc']").count(), 1);
  assert.match(await desktop.locator("dialog.dlg").innerText(), /Custom Project Help/);
  await desktop.keyboard.press("Escape");

  // Bare project fixture: no description placeholder, no docs link, general help only, missing doc fallback
  await desktop.goto(`http://127.0.0.1:${port}/bare-site/index.html#/summary`);
  await settle(desktop, "summary");
  assert.equal(await desktop.locator(".project-description").count(), 0);
  assert.equal(await desktop.locator(".index-docs").count(), 0);
  await desktop.click("#help-btn");
  await desktop.waitForSelector("dialog.dlg[open]");
  assert.equal(await desktop.locator("dialog.dlg [data-project-help]").count(), 0);
  assert.equal(await desktop.locator("dialog.dlg [data-general-help]").count(), 1);
  await desktop.keyboard.press("Escape");
  await desktop.goto(`http://127.0.0.1:${port}/bare-site/index.html#/docs/projects/README.md`);
  await settle(desktop, "docs");
  assert.match(await desktop.locator("main").innerText(), /No packaged documentation was found/);

  await open(desktop, "summary", "summary");

  await desktop.locator("#nav").getByRole("link", { name: "IR", exact: true }).click();
  await settle(desktop, "ir");
  const ir = desktop.locator("#ir-registry tbody tr");
  assert.equal(await ir.count(), 1);
  assert.match(await ir.innerText(), /fixture\.ir.*fixture\.subset.*fixture\.denote.*denotational/s);
  assert.equal(await ir.getByRole("link", { name: "Fixture.Block" }).getAttribute("href"), "#/source/Fixture.Block");
  await ir.getByRole("link", { name: "Fixture.denote", exact: true }).click();
  await settle(desktop, "source");
  assert.match(await desktop.locator("main h2").innerText(), /Fixture\.denote/);
  await open(desktop, "ir/", "ir");
  await ir.getByRole("link", { name: "Example institution" }).click();
  await settle(desktop, "institution");
  assert.match(await desktop.locator("main").innerText(), /Fixture\.inst/);
  await open(desktop, "ir/", "ir", "?db=legacy.sqlite");
  assert.match(await desktop.locator("main").innerText(), /This database predates the IR registry/);

  await open(desktop, "problem/ok.a", "problem");
  const standard = answer(desktop, "Ok.a_sol");
  const outside = answer(desktop, "Fixture.outside");
  assert.equal(await standard.innerText(), "Lean standard");
  assert.equal(await outside.innerText(), "Outside profile");
  assert.equal(await answer(desktop, "Fixture.empty").innerText(), "None");
  assert.equal(await answer(desktop, "Fixture.unknown").innerText(), "Unaudited");
  await outside.hover();
  assert.match(await details(desktop).innerText(), /«test, name with <b>markup<\/b>» \(outside profile\)/);
  assert.match(await details(desktop).innerText(), /sorryAx \(outside profile, sorry placeholder\)/);
  assert.equal(await details(desktop).locator("b").count(), 0);
  assert.equal(await desktop.locator("main tr").filter({ hasText: "Fixture.outside" }).locator("td").nth(5).innerText(), "Outside profile");
  await details(desktop).hover();
  await desktop.waitForTimeout(200);
  assert.ok(await details(desktop).isVisible(), "hover remains visible while reading");
  await answer(desktop, "Fixture.unknown").focus();
  await desktop.keyboard.press("Tab");
  assert.ok(await standard.evaluate((button) => button === document.activeElement));
  assert.match(await details(desktop).innerText(), /Quot.sound \(Lean standard\).*propext \(Lean standard\)/s);
  const id = await standard.getAttribute("aria-describedby");
  assert.match(await desktop.locator(`[id="${id}"]`).textContent(), /Quot.sound/);
  await shot(desktop, "desktop-profiles");
  await desktop.keyboard.press("Escape");
  assert.ok(!(await details(desktop).isVisible()));
  assert.ok(await standard.evaluate((button) => button === document.activeElement));

  await open(desktop, "problem/ok%2Flegacy", "problem");
  assert.match(await desktop.locator("main h2").first().innerText(), /ok\/legacy/);
  assert.equal(await desktop.locator("#nav a.on").innerText(), "Problems");
  assert.equal(await desktop.locator("#nav a.on").getAttribute("aria-current"), "true");

  await open(desktop, "problem/ok.a", "problem", "?db=legacy.sqlite");
  assert.equal(await answer(desktop, "Ok.a_sol").innerText(), "Unaudited");

  for (const [name, label] of Object.entries({ standard: "Lean standard", empty: "None", unknown: "Unaudited",
    unreadable: "Unaudited", outside: "Outside profile" })) {
    await open(desktop, `formal-property/fixture.${name}`, "formal-property");
    assert.equal(await desktop.locator("main .axiom-chip").innerText(), label);
  }

  await open(desktop, "elf-file/fixture/theorems", "elf-file");
  assert.deepEqual(await desktop.locator("main table .axiom-chip").allTextContents(),
    ["kernel ✓", "Unaudited", "Outside profile", "Lean standard"]);
  assert.equal(await desktop.locator("main > p .axiom-chip").first().innerText(), "Outside profile · unaudited");

  await open(mobile, "summary", "summary");
  assert.equal(await mobile.locator("#nav").isVisible(), false);
  assert.equal(await mobile.evaluate(() => document.documentElement.scrollWidth), 390);
  const toggle = mobile.getByRole("button", { name: "Browse views" });
  await toggle.tap();
  assert.equal(await toggle.getAttribute("aria-expanded"), "true");
  await shot(mobile, "mobile-navigation");
  await mobile.locator("#nav").getByRole("link", { name: "Problems", exact: true }).tap();
  await settle(mobile, "problems");
  assert.equal(await toggle.getAttribute("aria-expanded"), "false");
  assert.equal(await mobile.evaluate(() => document.activeElement.id), "main");

  await open(mobile, "problem/ok.a", "problem");
  await answer(mobile, "Fixture.outside").tap();
  assert.ok(await details(mobile).isVisible());
  assert.match(await details(mobile).innerText(), /sorryAx/);
  const bounds = await details(mobile).boundingBox();
  assert.ok(bounds.x >= 0 && bounds.x + bounds.width <= 390 && bounds.y >= 0 && bounds.y + bounds.height <= 844);
  await shot(mobile, "mobile-profiles");
  await answer(mobile, "Fixture.outside").tap();
  assert.ok(!(await details(mobile).isVisible()), "second tap dismisses the details");

  assert.deepEqual(errors, []);
  console.log("Explorer index, deep links, IR registry, axiom data, hover, focus and touch profiles passed");
} finally {
  if (browser) await browser.close();
  if (server) server.kill();
  fs.rmSync(siteRoot, { recursive: true, force: true });
}
