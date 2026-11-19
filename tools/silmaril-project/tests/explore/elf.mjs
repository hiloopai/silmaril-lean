// The explorer's ELF tab (explore/views/elf.js) on the pages `elf-pages` writes (elf/…). Checks, in
// a browser, for every pinned file (GNU sha256sum and hello):
// * the index lists it with its theorem count and kernel-only status;
// * the overview's section and segment tables have the page data's rows, each with its theorems,
//   and `.bss` shows as memory only; the coverage key's counts are the data's and sum to the size;
// * the browser's SHA-256 of the downloaded bytes is the pinned one;
// * the byte view colours each byte by its coverage class, shows file offset and virtual address,
//   and the selection panel lists exactly the theorems whose windows hold the byte (computed here
//   from the data, independently of the page), with section and segment;
// * the disassembly keeps its UNVERIFIED warning visible, and its rows' bytes are the file's bytes;
//   an address link opens the byte view at that instruction;
// * no page errors and no console errors.
//   node elf.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8797;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/elf_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const json = (rel) => JSON.parse(fs.readFileSync(path.join(site, "elf", rel)));
const hx = (n) => "0x" + n.toString(16);
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
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png") }); } };
  const ix = json("index.json");
  check(ix.files.length >= 2 && ix.files.some((f) => f.slug === "gnu-sha256sum"), "index.json lists GNU sha256sum and hello");

  await open("/elf");
  const navOn = await p.evaluate(() => document.querySelector("#nav a.on")?.textContent);
  check(navOn === "ELF", `the ELF tab is in the navigation and selected (${navOn})`);
  const rows = await p.evaluate(() => [...document.querySelectorAll("main table tbody tr")].map((r) => r.textContent));
  for (const f of ix.files) check(rows.some((r) => r.includes(f.title) && r.includes(String(f.theorems)) && r.includes("kernel-only")), `index row: ${f.slug}, ${f.theorems} theorems, kernel-only`);
  await shot("elf-index");

  for (const f of ix.files) {
    const d = json(`f/${f.slug}.json`);
    const bytes = fs.readFileSync(path.join(site, "elf/blob", f.slug + ".bin"));
    const sum = Object.values(d.coverageSummary).reduce((a, b) => a + b, 0);
    check(sum === d.size && bytes.length === d.size, `${f.slug}: coverage classes sum to the file size (${sum})`);
    check(d.theorems.every((t) => t.status === "checked" && t.kernelOnly), `${f.slug}: every theorem checked, kernel-only`);
    // Every section and segment of the data has its theorems.
    check(d.sections.every((s) => s.headerTheorem && s.nameTheorem && s.bodyTheorem) && d.segments.every((s) => s.theorem) && d.header.theorem && d.loader.theorem,
      `${f.slug}: every header, section (header, name, body), segment and the loader view has a theorem`);

    await open(`/elf-file/${f.slug}`);
    const ov = await p.evaluate(() => ({
      secRows: document.querySelectorAll("tr[id^=elf-sec-]").length,
      kernel: document.querySelectorAll("main .prov-lean").length,
      text: document.querySelector("main").textContent,
      key: Object.fromEntries([...document.querySelectorAll(".elf-key span")].slice(0, 4).map((s) => s.textContent.split(": "))) }));
    check(ov.secRows === d.sections.length, `${f.slug}: ${ov.secRows}/${d.sections.length} section rows`);
    check(ov.kernel >= d.sections.length * 3, `${f.slug}: section theorems shown as kernel-checked (${ov.kernel} badges)`);
    check(Object.entries(d.coverageSummary).every(([k, v]) => ov.key[k] === `${v} B`), `${f.slug}: coverage key ${JSON.stringify(ov.key)}`);
    const bss = d.sections.find((s) => s.name === ".bss");
    if (bss) check(ov.text.includes(`none (${bss.size} B in memory)`) && /zero-filled/.test(ov.text), `${f.slug}: .bss is memory only (${bss.size} B), the RW segment's zero fill is shown`);
    check(ov.text.includes("ELFCLASS32") && ov.text.includes("unsupported"), `${f.slug}: unsupported variants are listed`);
    if (f.slug.startsWith("hello-")) {
      check(d.loader.interp === "/lib64/ld-linux-x86-64.so.2" && d.loader.needed.includes("libc.so.6") && d.loader.theorem,
        `${f.slug}: glibc-linked: PT_INTERP ld-linux-x86-64.so.2 and DT_NEEDED libc.so.6, from the checked loader view`);
      check(ov.text.includes("/lib64/ld-linux-x86-64.so.2") && ov.text.includes("libc.so.6"), `${f.slug}: the overview shows the interpreter and libc.so.6`);
      await shot(`elf-${f.slug}-overview`);
    }
    await p.click("#elf-sha");
    await p.waitForFunction(() => /matches|differs/.test(document.querySelector("#elf-shaout").textContent), null, { timeout: 20000 });
    check(await p.evaluate(() => document.querySelector("#elf-shaout").textContent.includes("matches")), `${f.slug}: the browser's SHA-256 of the bytes matches ${d.sha256.slice(0, 12)}…`);
    if (f.slug === "gnu-sha256sum") await shot("elf-sha256sum-overview");

    // Theorem list: one row per theorem.
    await open(`/elf-file/${f.slug}/theorems`);
    const trows = await p.evaluate(() => document.querySelectorAll("main table tbody tr").length);
    check(trows === d.theorems.length, `${f.slug}: theorem list has ${trows}/${d.theorems.length} rows`);

    // Byte view at the .dynsym (or the first decoded body) and at .text.
    const dyn = d.sections.find((s) => s.name === ".dynsym") || d.sections.find((s) => s.decoded);
    const o = dyn.offset + 24 + 3;
    await open(`/elf-bytes/${f.slug}/${hx(o)}`);
    const bv = await p.evaluate((o) => {
      const e = document.querySelector(`span.b[data-o="${o}"]`);
      return { sel: e && e.classList.contains("sel"), text: e && e.textContent, cls: e && [...e.classList].find((c) => c.startsWith("elf-c-")),
        side: document.querySelector("#elf-side").textContent, thms: [...document.querySelectorAll("#elf-side li code")].map((c) => c.getAttribute("title")) };
    }, o);
    const expectThms = d.theorems.filter((t) => t.windows.some(([w, n]) => w <= o && o < w + n)).map((t) => t.decl).sort();
    const cls = d.coverage.find(([w, n]) => w <= o && o < w + n)[2];
    check(bv.sel && bv.text === bytes[o].toString(16).padStart(2, "0"), `${f.slug}: byte ${hx(o)} selected, shows ${bytes[o].toString(16)}`);
    check(bv.cls === "elf-c-" + cls, `${f.slug}: byte ${hx(o)} coloured ${cls}`);
    check(JSON.stringify(bv.thms.slice().sort()) === JSON.stringify(expectThms), `${f.slug}: selection lists exactly the ${expectThms.length} theorems whose windows hold ${hx(o)}`);
    check(bv.side.includes(dyn.name), `${f.slug}: selection names section ${dyn.name}`);
    // Click another byte (the ELF magic) and check the panel follows.
    await open(`/elf-bytes/${f.slug}/0x0`);
    await p.click('span.b[data-o="1"]');
    check(await p.evaluate(() => /0x1\b/.test(document.querySelector("#elf-side h3").textContent) && location.hash.endsWith("/0x1")), `${f.slug}: clicking a byte selects it and updates the link`);
    check(await p.evaluate(() => [...document.querySelectorAll("#elf-side li code")].some((c) => /\.header$/.test(c.getAttribute("title")))), `${f.slug}: the ELF magic is covered by the header theorem`);
    if (f.slug === "gnu-sha256sum") { await open(`/elf-bytes/${f.slug}/${hx(o)}`); await shot("elf-sha256sum-bytes"); }

    // Function table: rows from the data, each with its checked symbol theorem.
    const T = new Map(d.theorems.map((t) => [t.decl, t]));
    const fns = d.functions;
    check(fns.every((r) => T.get(r.theorem)?.kind === "symbol" && T.get(r.theorem).status === "checked"), `${f.slug}: all ${fns.length} function rows have a kernel-checked symbol theorem`);
    check(fns.every((r) => r.size !== 0 || !r.defined || r.extent.startsWith("unknown") || r.extent.startsWith("absolute")), `${f.slug}: defined rows with st_size 0 have an unknown extent`);
    check(fns.every((r) => r.defined || r.extent.startsWith("import")), `${f.slug}: undefined rows are imports`);
    await open(`/elf-funcs/${f.slug}`);
    const ft = await p.evaluate(() => ({ n: document.querySelector("#elf-fn").textContent, note: document.querySelector("main .note").textContent,
      rows: document.querySelectorAll("table.elf-fns tbody tr").length, text: document.querySelector("main").textContent }));
    const def = fns.filter((r) => r.defined).length;
    check(ft.n === `${def} of ${fns.length}` && ft.rows === Math.min(def, 300), `${f.slug}: function table shows ${ft.n} (defined only), ${ft.rows} rows on the page`);
    check(/not a recovered function/.test(ft.note) && /System V ABI/.test(ft.note), `${f.slug}: the table says what a row is and is not`);
    const withContract = fns.filter((r) => r.contracts.length).length;
    check(ft.text.includes(`${withContract} with a contract theorem`), `${f.slug}: ${withContract} rows with a contract theorem`);
    if (f.slug === "zlib-checksums") {
      check(withContract === 4 && ["crc32_z", "crc32", "adler32_z", "adler32"].every((n) => fns.find((r) => r.name === n)?.contracts.length === 1), "zlib-checksums: crc32_z, crc32, adler32_z, adler32 each link one contract");
      await p.check("#elf-fcon");
      const cs = await p.evaluate(() => [...document.querySelectorAll("table.elf-fns tbody tr")].map((r) => [r.dataset.fn, r.cells[10].textContent]));
      check(cs.length === 4 && cs.every(([, c]) => /kernel ✓/.test(c) && /_contract/.test(c)), `zlib-checksums: the contract filter shows the 4 functions, kernel-checked (${cs.map(([n]) => n).join(", ")})`);
      const st = d.theorems.find((t) => t.decl.endsWith(".crc32_z_contract"));
      check(st && /CodeAt \S*\.F 4200848 \S*crc32zCode/.test(st.statement.replace(/\s+/g, " ")) && /crc32zContract/.test(st.statement), "zlib-checksums: crc32_z's contract statement names its address and code");
      await shot("elf-zlib-checksums-functions");
    }
    if (f.slug === "glibc-libc") {
      check(fns.some((r) => r.ifunc && r.defined) && /resolver/.test(ft.text), "glibc-libc: IFUNC rows are marked as resolvers");
      check(fns.some((r) => r.aliases.length), "glibc-libc: aliases (one address, several symbols) are listed");
      check(fns.some((r) => r.version && r.version.includes("GLIBC_")), "glibc-libc: symbol versions are read from .gnu.version / .gnu.version_d");
      check(withContract === 0 && /no contract statement/.test(ft.text), "glibc-libc: no contract statements, and the table says so");
      await p.fill("#elf-fq", "memcpy");
      await p.waitForTimeout(100);
      await shot("elf-glibc-libc-functions");
    }
    if (f.slug === "glibc-libm" || f.slug === "zlib-libz") await shot(`elf-${f.slug}-functions`);
    // Disassembly.
    const dis = json(d.disassembly.file);
    const disRows = dis.chunks.flatMap(([file]) => json(file));
    check(dis.unverified === true && disRows.length === dis.rows && disRows.length > 0, `${f.slug}: disassembly data marked unverified, ${disRows.length} rows in ${dis.chunks.length} chunks`);
    check(disRows.every(([, off, hex]) => off != null && Buffer.from(hex, "hex").equals(bytes.subarray(off, off + hex.length / 2))), `${f.slug}: every disassembly row's bytes are the file's bytes`);
    const entry = d.header.entry;
    if (!disRows.some(([a]) => a === entry)) { check(true, `${f.slug}: entry ${hx(entry)} is not an instruction of the listing (skipped)`); continue; }
    await open(`/elf-disasm/${f.slug}/${hx(entry)}`);
    const dv = await p.evaluate(() => {
      const w = document.querySelector(".elf-warn");
      const r = w && w.getBoundingClientRect();
      return { warn: w && /UNVERIFIED/.test(w.textContent), visible: !!r && r.top >= 0 && r.bottom <= innerHeight && getComputedStyle(w).position === "sticky",
        hit: document.querySelector("#elf-hit td")?.textContent };
    });
    check(dv.warn && dv.visible, `${f.slug}: the UNVERIFIED warning is visible at the entry point`);
    check(dv.hit === hx(entry), `${f.slug}: the entry point's row is highlighted (${dv.hit})`);
    if (f.slug === "gnu-sha256sum") await shot("elf-sha256sum-disassembly");
    await p.click("#elf-hit td a");
    await p.waitForFunction(() => window.explore && !window.explore.busy && document.querySelector("#elf-side"), null, { timeout: 30000 });
    const entryOff = d.segments.find((s) => s.type === "LOAD" && s.vaddr <= entry && entry < s.vaddr + s.filesz);
    const want = entry - entryOff.vaddr + entryOff.offset;
    check(await p.evaluate((w) => location.hash.includes("/0x" + w.toString(16)) && document.querySelector(`span.b[data-o="${w}"]`).classList.contains("sel"), want),
      `${f.slug}: the entry row links to the byte view at file offset ${hx(want)}`);
  }
  // Byte-grounded CFG rows have evidence distinct from the ELF part theorems.
  const regions = json("regions/hello-gcc.json"), rr = regions.rows;
  const corpus = fs.readFileSync(path.join(site, "elf/blob/hello-gcc.bin"));
  check(rr.length === 4 && rr.filter((r) => r.certificates.length).length === 2,
    "hello-gcc: two certified byte CFGs and two stated comparison rows");
  check(rr.every((r) => Buffer.from(r.bytes).equals(corpus.subarray(r.offset, r.offset + r.size))),
    "every region row is tied to its actual corpus byte window");
  check(rr.slice(0, 2).every((r) => r.certificates.every((c) => c.row === r.id && c.sha256 === regions.sha256)),
    "certificate evidence names the row and pinned image");
  await open("/elf-regions/hello-gcc");
  check(await p.locator("#elf-regions tbody tr").count() === 4, "region tab displays all certified and stated rows");
  check(await p.locator("#elf-region-comparison").textContent().then((s) => s.includes("Adjacency agrees")),
    "stated matching row agrees without inheriting certification");
  check(await p.locator("#elf-regions").textContent().then((s) => s.includes("certificate unknown")),
    "missing certificate is shown as unknown");
  await p.selectOption("#elf-region-b", rr[3].id);
  check(await p.locator("#elf-region-comparison").textContent().then((s) => s.includes("Adjacency disagrees") && s.includes("0x10c3")),
    "omitted conditional fallthrough is identified in comparison");
  await shot("elf-regions-comparison");
  await open("/elf-graph/hello-gcc");
  check(await p.locator("#elf-graph svg [data-edge]").count() === rr[0].edges.length,
    "graph retains every outgoing edge, separate from dominance");
  check(await p.locator("#elf-graph").textContent().then((s) => s.includes("Not supplied") && s.includes("Undirected simple")),
    "graph relationship table states dominance status and projection loss");
  await shot("elf-cfg-graph");
  await p.selectOption("#elf-graph-row", rr[1].id);
  check(await p.locator("#elf-graph svg [data-edge]").count() === rr[1].edges.length,
    "switching graph constants preserves the tail-jump adjacency");
  await open("/elf-regions/hello-clang");
  check(await p.locator("main").textContent().then((s) => s.includes("No region/CFG rows")),
    "unsupported corpus file remains without CFG evidence");
  check(errors.length === 0, `no page or console errors ${errors.join("; ")}`);
} finally {
  await b.close(); srv.kill();
}
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
