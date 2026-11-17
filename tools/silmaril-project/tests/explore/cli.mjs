// The explorer's CLI tab (explore/views/cli.js) on elf/cli.json (written by elf-pages). Checks, in
// a browser:
// * the CLI tab is in the navigation; the verified-I/O table has one row per record, and a
//   record's verdict follows its declarations: "verified under the stated model" only when a
//   "proves" declaration is proved, with the count of open obligations; otherwise "no verified
//   input/output pair";
// * hello-gcc: stdout `hello, world\n` and exit 0, the glibc process model (Open9, the loader
//   relation, glibc contracts trusted), and its open obligations shown as not proved;
// * every declaration row's status is the data's, and open obligations are never shown as proved;
// * the specifications tab keeps specification, implementation and refinement apart (wasm-wac's
//   main_refines proved; wasm-tools has no refinement);
// * no page or console errors.
//   node cli.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8798;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/cli_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const d = JSON.parse(fs.readFileSync(path.join(site, "elf/cli.json")));
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push("pageerror: " + e.message));
  p.on("console", (m) => { if (m.type() === "error") errors.push("console: " + m.text()); });
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: false }); } };

  // Data invariants (independent of the page).
  check(d.io.every((r) => r.edges.every((e) => !e.role.startsWith("open") || !(e.status === "proved" || e.status.startsWith("proved by")))),
    "no open obligation is proved in the data (they would not be open)");
  check(d.io.flatMap((r) => r.edges).concat(d.specs.flatMap((r) => r.edges)).every((e) => e.kind !== "theorem" ||
      e.status === (e.role.startsWith("conditional") ? "proved implication; hypotheses open" : "proved")),
    "every linked theorem is proved with the standard axioms (a conditional one as an implication)");
  const helloEdges = d.io.find((r) => r.id === "hello-gcc").edges;
  check(helloEdges.some((e) => e.decl.endsWith("helloGcc_real") && e.status === "proved implication; hypotheses open") &&
      helloEdges.filter((e) => e.role.startsWith("proves")).every((e) => !/concrete glibc/.test(e.note) || /not concrete glibc/.test(e.note)),
    "hello-gcc: real execution is a conditional implication, the proved claims are about the process model");
  check(helloEdges.some((e) => e.decl.endsWith("hello_start") && !e.role.startsWith("proves") && /not a statement about runs/.test(e.note)) &&
      helloEdges.some((e) => e.decl.endsWith("cli_of_main")) && helloEdges.some((e) => e.decl.endsWith("hello_via_start")),
    "hello-gcc: the start-up row is a checked description, linked to its execution consequence (cli_of_main, hello_via_start)");
  check(helloEdges.some((e) => e.decl.endsWith("GlibcRuntime") && e.role.startsWith("shape") && e.status === "uninstantiated shape" && /no instance/.test(e.note)) &&
      helloEdges.filter((e) => e.role.startsWith("open")).every((e) => /assumption of helloGcc_real/.test(e.role)),
    "hello-gcc: glibc_runtime is an uninstantiated shape, apart from the concrete open assumptions (Task.helloGccCrt, HelloLib)");
  const counting = d.io.concat(d.specs).flatMap((r) => r.edges).filter((e) => /^(proves|refinement|checks)/.test(e.role));
  check(counting.length > 0 && counting.every((e) => e.association === "checked" && e.about.length > 0),
    `every proving or refinement edge is checked to be about its record (${counting.length})`);

  await open("/cli");
  check(await p.evaluate(() => document.querySelector("#nav a.on")?.textContent) === "CLI", "the CLI tab is in the navigation and selected");
  const rows = await p.evaluate(() => [...document.querySelectorAll("tr[id^=cli-io-]")].map((r) => [r.id.slice(7), r.cells[4].textContent]));
  check(rows.length === d.io.length, `one verified-I/O row per record (${rows.length})`);
  for (const r of d.io) {
    const proved = r.edges.some((e) => e.role.startsWith("proves") && e.status === "proved");
    const nOpen = r.edges.filter((e) => e.role.startsWith("open")).length;
    const got = rows.find(([id]) => id === r.id)?.[1] || "";
    const want = proved ? "verified under the stated model" : "no verified input/output pair";
    check(got.includes(want) && (!proved || nOpen === 0 || got.includes(`${nOpen} open obligation`)), `${r.id}: verdict "${got.trim()}"`);
  }
  const hello = await p.evaluate(() => {
    const h = document.getElementById("cli-rec-hello-gcc"); let t = ""; let e = h;
    while ((e = e.nextElementSibling) && e.tagName !== "H2") t += e.textContent + "\n";
    return t;
  });
  check(hello.includes("hello, world") && /exit\s*0/.test(hello), "hello-gcc: stdout hello, world and exit 0");
  check(/Open9/.test(hello) && /Dyn\.Loader|ld\.so/.test(hello) && /trusted/.test(hello), "hello-gcc: the model names Open9, the loader relation and the trusted glibc contracts");
  const pills = await p.evaluate(() => [...document.querySelectorAll("table.cli-edges tbody tr")].map((r) => [r.dataset.role, r.cells[1].querySelector("code").getAttribute("title"), r.cells[2].textContent]));
  const all = d.io.flatMap((r) => r.edges).concat(d.specs.flatMap((r) => r.edges));
  check(pills.length === d.io.reduce((n, r) => n + r.edges.length, 0), `declaration rows on the I/O page: ${pills.length}`);
  check(pills.every(([role, decl, st]) => all.some((e) => e.decl === decl && e.role === role && e.status === st.trim())), "every declaration's status on the page is the data's");
  check(pills.filter(([role]) => role.startsWith("open")).every(([, , st]) => !/^proved/.test(st.trim())), "open obligations are not shown as proved");
  await shot("cli-io");
  await p.click('button[data-go="cli-rec-hello-gcc"]');
  await p.waitForTimeout(300);
  check(await p.evaluate(() => location.hash === "#/cli"), "jumping to a record keeps the route");
  await shot("cli-io-hello");

  await open("/cli-specs");
  const specs = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("tr[id^=cli-spec-]")].map((r) => [r.id.slice(9), r.cells[4].textContent])));
  check(Object.keys(specs).length === d.specs.length, `one row per specification (${Object.keys(specs).length})`);
  check(/proved/.test(specs["wasm-wac"]) && /main_refines/.test(specs["wasm-wac"]), "wasm-wac: main_refines shown as a proved refinement");
  check(specs["wasm-tools"].trim() === "none", "wasm-tools: no refinement proof, shown as none");
  check(/hello_cli/.test(specs["hello"]), "hello: its refinement is hello-gcc's row");
  await shot("cli-specs");
  check(errors.length === 0, `no page or console errors ${errors.join("; ")}`);
} finally {
  await b.close(); srv.kill();
}
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
