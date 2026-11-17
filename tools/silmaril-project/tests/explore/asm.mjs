// The explorer's assembly tab (explore/views/asm.js) on elf/asm.json and elf/asm-decls.json
// (written by elf-pages from examples/elf-asm/samples.json). Checks, in a browser:
// * the Assembly tab is in the navigation; its index has one row per function record;
// * every record's page: one evidence row per dimension whose status is the one computed here
//   from the record's evidence array alone (no dimension read from another), "none" for a
//   dimension without evidence, a separate ABI conformance row ("no conformance row"), no overall
//   "verified" badge, abiRef labelled metadata, display lines labelled unchecked, one decoding
//   column per model with its DecodesAs declaration, the exact bytes, every reference with its
//   origin, unknown extent fields shown as unknown, and source links for declarations;
// * links: the ELF tab's function table links a symbol to its records (one record: the function;
//   two records of one name: a chooser), and a record links back to the ELF tab and to the
//   unverified objdump view;
// * no page or console errors.
//   node asm.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8799;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/asm_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const json = (rel) => JSON.parse(fs.readFileSync(path.join(site, "elf", rel)));
const d = json("asm.json"), decls = json("asm-decls.json").decls, ix = json("index.json");

// The status of each dimension, from the record's own evidence (independent of the page).
const DIMS = { arch: [["arch"], ["notArch"]], bytes: [["bytes"], ["notBytes"]], sectionBytes: [["sectionBytes"], []], code: [["code"], []],
  symbol: [["symbol"], []], lines: [["lineTiles"], []], refs: [["refs"], []], unrelocated: [["unrelocated"], []], present: [["present"], []],
  contract: [["contract"], []] };
const statusOf = (pos, neg) => pos.length && neg.length ? "conflicting" : neg.length ? "does not hold" : !pos.length ? "none"
  : pos.some((e) => e.applicability ? e.applicability === "unconditional" : !e.hypotheses.length) ? "holds" : "holds under premises";
function expected(fn) {
  const out = [];
  for (const [dim, [p, n]] of Object.entries(DIMS))
    out.push([dim, null, statusOf(fn.evidence.filter((e) => p.includes(e.kind)), fn.evidence.filter((e) => n.includes(e.kind)))]);
  const models = [...new Set(fn.decodings.map((x) => x.model).concat(fn.evidence.filter((e) => e.kind === "decode" || e.kind === "noDecode").map((e) => e.model)))];
  if (!models.length) out.push(["decode", null, "none"]);
  for (const m of models) out.push(["decode", m, statusOf(fn.evidence.filter((e) => e.kind === "decode" && e.model === m), fn.evidence.filter((e) => e.kind === "noDecode" && e.model === m))]);
  const rows = Array.isArray(fn.abiRows) ? fn.abiRows : Array.isArray(fn.abi) ? fn.abi : [];
  out.push(["abi", null, rows.length ? "rows" : "none"]);
  return out;
}

try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push("pageerror: " + e.message));
  p.on("console", (m) => { if (m.type() === "error") errors.push("console: " + m.text()); });
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const open = async (hash) => { await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`); await settle(); };
  const shot = async (name, sel) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    if (sel) await p.evaluate((s) => document.querySelector(s)?.scrollIntoView({ block: "start" }), sel);
    await p.screenshot({ path: path.join(shots, name + ".png") });
  };

  check(d.schema === "silmaril.elf.asm/1", "asm.json has the schema silmaril.elf.asm/1");
  const named = new Set(d.files.map((f) => f.decl).concat(d.functions.flatMap((f) => [f.decl, f.file, ...f.decodings.map((x) => x.decl), ...f.evidence.map((e) => e.decl)])));
  check([...named].every((n) => decls[n] && decls[n].file && decls[n].line), `asm-decls.json locates every declaration asm.json names (${named.size})`);

  await open("/asm");
  check(await p.evaluate(() => document.querySelector("#nav a.on")?.textContent) === "Assembly", "the Assembly tab is in the navigation and selected");
  const rows = await p.evaluate(() => [...document.querySelectorAll("table.asm-index tbody tr")].map((r) => ({ decl: r.dataset.decl, href: r.querySelector("td:nth-child(2) a").getAttribute("href") })));
  check(rows.length === d.functions.length && d.functions.every((f) => rows.some((r) => r.decl === f.decl)), `index: one row per record (${rows.length})`);
  check(!(await p.evaluate(() => /\bverified\b/i.test(document.querySelector("main").textContent))), "index: no overall verified badge");
  await shot("asm-index");

  for (const fn of d.functions) {
    const href = rows.find((r) => r.decl === fn.decl).href;
    await open(href.slice(1));
    const pg = await p.evaluate(() => {
      const m = document.querySelector("main");
      return {
        title: m.querySelector("h2")?.textContent || "",
        text: m.textContent,
        dims: [...m.querySelectorAll("table.asm-ev tbody")].map((t) => [t.dataset.dim, t.dataset.model || null, t.dataset.status, t.textContent]),
        hex: [...m.querySelectorAll("table.asm-hex tbody tr td:last-child")].map((t) => t.textContent.replace(/ /g, "")).join(""),
        models: [...m.querySelectorAll("table.asm-side th.model")].map((t) => [t.dataset.model, t.textContent]),
        disp: m.querySelector("table.asm-side th.disp")?.textContent || "",
        refs: [...m.querySelectorAll("table.asm-refs tbody tr")].map((r) => [r.dataset.origin, r.cells[7].textContent]),
        meta: [...m.querySelectorAll(".asm-meta")].map((e) => e.textContent),
        extent: Object.fromEntries([...m.querySelectorAll("dl dt")].map((dt) => [dt.textContent, dt.nextElementSibling.textContent])),
        links: [...m.querySelectorAll("a")].map((a) => a.getAttribute("href")),
        sources: [...m.querySelectorAll("table.asm-ev a[target=_blank]")].map((a) => a.getAttribute("href")),
      };
    });
    const tag = `${fn.name} (${fn.decl.split(".").pop()})`;
    check(pg.title.includes(fn.name), `${tag}: its page`);
    const want = expected(fn);
    const got = pg.dims.filter(([dim]) => dim !== "other").map(([dim, m, st]) => [dim, m, st]);
    check(JSON.stringify(got.map((x) => x.join("|")).sort()) === JSON.stringify(want.map((x) => x.join("|")).sort()),
      `${tag}: one evidence row per dimension, status from its own evidence (${got.map(([a, m, s]) => `${a}${m ? ":" + m.split(".").slice(-2)[0] : ""}=${s}`).join(", ")})`);
    for (const [dim, , st, text] of pg.dims) if (st === "none" && dim !== "abi") check(/none/.test(text), `${tag}: ${dim} with no evidence shows none`);
    // The demo the dimensions exist for: a contract on one machine does not make a decoder accept the bytes.
    const dec = (model) => pg.dims.find(([dim, m]) => dim === "decode" && m === model)?.[2];
    if (fn.name === "crc32_z" && fn.arch?.machine === 62)
      check(dec("x86-64/Silmaril.X86.Open.decode") === "holds" && dec("x86-64/Silmaril.X86.Ext.decode") === "does not hold" &&
        pg.dims.some(([dim, , st]) => dim === "contract" && st === "holds"),
        `${tag}: decoded by Open, not by Ext (proved), its contract on Open shown separately`);
    if (fn.name === "adler32_z")
      check(dec("x86-64/Silmaril.X86.Open9.decode") === "holds" && dec("x86-64/Silmaril.X86.Open.decode") === "does not hold" &&
        pg.dims.some(([dim, , st]) => dim === "contract" && st === "holds"),
        `${tag}: decoded by Open9, not by Open (proved), its contract on Open9 shown separately`);
    // each row names exactly its own declarations
    const decRows = pg.dims.filter(([dim]) => dim in DIMS);
    check(decRows.every(([dim, , , text]) => fn.evidence.filter((e) => DIMS[dim][0].concat(DIMS[dim][1]).includes(e.kind)).every((e) => text.includes(e.decl.split(".").slice(-2).join(".")))),
      `${tag}: every evidence declaration is listed in its dimension's row`);
    const abiRs = Array.isArray(fn.abiRows) ? fn.abiRows : [];
    check(pg.dims.some(([dim, , st, text]) => dim === "abi" && st === (abiRs.length ? "rows" : "none") &&
      (abiRs.length ? abiRs.every((r) => text.includes(r.problemId) && text.includes(r.bridge.split(".").pop()) && /checked/.test(text)) : /no conformance row/.test(text))),
      `${tag}: ABI conformance is its own row (${abiRs.length ? abiRs.map((r) => r.problemId).join(", ") + ", each with its bridge" : '"no conformance row"'})`);
    check(!/\bverified\b/i.test(pg.text.replace(/\(unverified\)/g, "")), `${tag}: no overall verified badge`);
    check(pg.meta.some((t) => t === "metadata (not evidence)") && pg.extent.abiRef.includes(fn.abiRef ?? "unknown"), `${tag}: abiRef shown as metadata (not evidence)`);
    check(/display only, not checked/.test(pg.disp) && /display only, not checked/.test(pg.text), `${tag}: display lines labelled display only, not checked`);
    check(pg.hex === fn.bytesHex, `${tag}: the exact bytes (${fn.bytesHex.length / 2} B)`);
    check(pg.models.length === fn.decodings.length && fn.decodings.every((x) => pg.models.some(([m, t]) => m === x.model &&
      (fn.evidence.some((e) => e.kind === "decode" && e.model === x.model) ? /decoder accepted/.test(t) : /no DecodesAs evidence/.test(t)))),
      `${tag}: one decoding column per model, each with its DecodesAs evidence or its absence`);
    check(pg.refs.length === fn.refs.length && fn.refs.every((r, i) => pg.refs[i][0] === r.origin.kind &&
      (r.origin.kind === "display" ? /not grounded/.test(pg.refs[i][1]) : fn.evidence.some((e) => e.kind === "refs") ? /^grounded/.test(pg.refs[i][1].trim()) : /not grounded/.test(pg.refs[i][1]))),
      `${tag}: ${fn.refs.length} references with origin and grounding`);
    for (const [k, label] of [["fileOff", "file offset"], ["segment", "segment"], ["shndx", "section"]])
      if (fn.extent[k] == null) check(pg.extent[label] === "unknown", `${tag}: ${label} unknown`);
    check(pg.sources.length > 0 && pg.sources.every((h) => /^https:\/\/github\.com\/.+\/blob\/[0-9a-f]+\/Silmaril\/.+\.lean#L\d+$/.test(h)), `${tag}: declarations link to their source lines (${pg.sources.length})`);
    const file = d.files.find((f) => f.decl === fn.file);
    const slug = ix.files.find((f) => f.path === file.path)?.slug;
    if (slug) check(pg.links.includes(`#/elf-file/${slug}`) && (fn.extent.segment == null || pg.links.includes(`#/elf-disasm/${slug}/${fn.extent.vaddr}`)),
      `${tag}: links back to the ELF tab (${slug}) and to the unverified objdump view`);
    else check(/no page in the ELF tab/.test(pg.text), `${tag}: says its file has no ELF tab page`);
    if (fn.name === "adler32") { await shot("asm-adler32"); await shot("asm-adler32-lines", "table.asm-side"); }
    if (fn.name === "scaled_plus_bias") { await shot("asm-reloc"); await shot("asm-reloc-lines", "table.asm-side"); }
    if (fn.decl.endsWith("otherMachine")) await shot("asm-other-machine");
  }

  // From the ELF tab's function table to the assembly tab and back.
  const zf = d.files.find((f) => f.path === ix.files.find((x) => x.slug === "zlib-checksums")?.path);
  check(!!zf, "zlib-checksums has assembly records");
  await open("/elf-funcs/zlib-checksums");
  await p.fill("#elf-fq", "crc32");
  await p.waitForTimeout(200);
  const links = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("table.elf-fns tbody tr")].map((r) => [r.dataset.fn, r.querySelector("a.elf-asm")?.getAttribute("href") || null])));
  const recs = (n) => d.functions.filter((f) => f.file === zf.decl && f.name === n).length;
  check(Object.entries(links).every(([n, h]) => (recs(n) > 0) === (h != null)), `ELF function table: a symbol links to the assembly tab exactly when it has a record (${Object.entries(links).map(([n, h]) => `${n}:${h ? "yes" : "no"}`).join(", ")})`);
  await shot("elf-funcs-asm-links");
  await p.click('tr[data-fn="crc32_z"] a.elf-asm');
  await p.waitForFunction(() => location.hash.startsWith("#/asm/") && document.querySelector("main h2")?.textContent.includes("crc32_z"), null, { timeout: 30000 }).catch(() => {});
  await settle();
  check(await p.evaluate(() => location.hash === "#/asm/zlib-checksums/crc32_z" && document.querySelector("main h2").textContent.includes("crc32_z")), "the link opens crc32_z's record");
  await p.click('main a[href="#/elf-file/zlib-checksums"]');
  await p.waitForFunction(() => location.hash === "#/elf-file/zlib-checksums" && window.explore.view === "elf-file", null, { timeout: 30000 }).catch(() => {});
  await settle();
  check(await p.evaluate(() => location.hash === "#/elf-file/zlib-checksums" && document.querySelector("#nav a.on")?.textContent === "ELF"), "the record links back to the ELF tab");
  await open("/asm/zlib-checksums/crc32");
  const choose = await p.evaluate(() => [...document.querySelectorAll("ul.asm-choose li > a:first-child")].map((a) => a.getAttribute("href")));
  check(choose.length === recs("crc32"), `two records named crc32 (another e_machine): a chooser (${choose.length})`);
  await shot("asm-chooser");
  check(errors.length === 0, `no page or console errors ${errors.join("; ")}`);
} finally {
  await b.close(); srv.kill();
}
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
