// The explorer's Headers tab (explore/views/headers.js) on headers/index.json (header-pages).
// Checks, in a browser: the tab is in the navigation; one index row per header; on the subset
// route, a refused header shows the reader's reason, each prototype row shows every ABI's lowering
// or refusal as the data says, the System V scalar plan names xmm registers for floating
// arguments, and each aggregate shows both data models' size and alignment as the data says. On
// the clang route: the provenance, the counts and every entry's name, convention, symbol and
// status for each ABI as the data says; probe.h shows its clang entries although its subset route
// is refused; glibc string.h has a page with strerror_r and its asm label. A layout column names
// a theorem exactly when the data carries its `proof`: demo.h's 14 columns name their layout and
// padding theorems as the data says (linked to their source lines), every other column says
// "computed, not a theorem" and has no theorem link; nothing is called proved. A tampered copy of
// the data (markup in names, types, reasons, paths and theorem names; a dropped and a non-proved
// proof) is shown as text and runs nothing. No page or console errors.
//   node headers.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8803, tport = 8804;
const here = path.dirname(new URL(import.meta.url).pathname);
const serve = (root, p, log) => spawn("python3", ["-I", path.join(here, "pages_server.py"),
  "--root", root, "--port", String(p), "--log", log], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const d = JSON.parse(fs.readFileSync(path.join(site, "headers", "index.json")));

// The tampered copy: the page and the database, and a header whose strings carry markup.
const P1 = "<img src=x onerror=window.__pwn=1>", P2 = '"><script>window.__pwn=2</script>';
const tdir = fs.mkdtempSync(path.join(os.tmpdir(), "headers-tamper-"));
for (const f of ["index.html", "explore-sw.js", "project.sqlite"])
  if (fs.existsSync(path.join(site, f))) fs.copyFileSync(path.join(site, f), path.join(tdir, f));
const t = structuredClone(d);
const probe = t.headers.find((h) => h.id === "probe");
const bad = structuredClone(probe);
Object.assign(bad, { id: "tamper", title: P1 + P2, note: P2 + P1, root: P1 });
bad.files = [{ name: P1, path: P2 }];
bad.read = { refused: P1 + " " + P2 };
Object.assign(bad.clang, { value: P1, literal: P2, relation: P2 + P1 });
Object.assign(bad.clang.provenance, { image: P1, clang: P2, command: P1, defines: [P2], source: P1,
  inputs: [{ file: P2, sha256: P1 }], artifact: P1 });
bad.clang.counts.total = P1;
const be = bad.clang.entries.find((e) => e.kind === "function");
Object.assign(be, { name: P1 + P2, decl: { ok: P2 + " " + P1 }, cc: P1, attrs: [P2], symbol: P1, asmLabel: P2,
  loc: { file: P1 + P2, line: P2 } });
be.status.sysvInt = { status: "unsupported", why: P1 + " " + P2 };
be.status.sysvScalar = { status: "claimable" };
be.lowering = { sysvScalar: { ok: P2, plan: { ok: { arguments: [P1], result: P2, stackSize: 0 } } } };
const be2 = bad.clang.entries.find((e, i) => e.kind === "function" && e !== be);
be2.decl = { unsupported: P1 + P2 };
be2.status.win64Int = { status: "internal", why: P2 };
t.headers.push(bad);
const bad2 = structuredClone(t.headers.find((h) => h.id === "layout-demo"));
Object.assign(bad2, { id: P2, title: P1 });
bad2.prototypes[0].c = P1; bad2.prototypes[0].lowering.sysvInt = { refused: P2 };
bad2.aggregates[0].members[0].name = P2; bad2.aggregates[0].members[0].type = P1;
bad2.aggregates[0].layouts.sysvX86_64.proof = null; bad2.aggregates[0].layouts.sysvX86_64.proofNote = P1;
bad2.aggregates[1].layouts.sysvX86_64.proof.status = "sorry";
Object.assign(bad2.aggregates[2].layouts.msX64.proof, { decl: P1 + P2, file: P2, statement: P1, axioms: [P2] });
bad2.aggregates[2].layouts.msX64.proof.padding.decl = P2;
t.headers.push(bad2);
fs.mkdirSync(path.join(tdir, "headers"));
fs.writeFileSync(path.join(tdir, "headers", "index.json"), JSON.stringify(t));

const srv = serve(site, port, "/tmp/headers_requests.jsonl"), tsrv = serve(tdir, tport, "/tmp/headers_tamper_requests.jsonl");
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
const statusText = (s) => !s ? "—" : s.status === "claimable" ? "claimable" : s.status === "notFunction" ? "not a function" : `${s.status}: ${s.why}`;
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1400 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push("pageerror: " + e.message));
  p.on("console", (m) => { if (m.type() === "error") errors.push("console: " + m.text()); });
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const open = async (hash, at = port) => { await p.goto(`http://127.0.0.1:${at}/index.html#${hash}`); await settle(); };
  check(d.schema === "silmaril.header-pages/2", "headers/index.json has the schema silmaril.header-pages/2");
  await open("/headers");
  check(await p.evaluate(() => [...document.querySelectorAll("#nav a")].some((a) => a.textContent === "Headers" && a.classList.contains("on"))), "the Headers tab is in the navigation and selected");
  const rows = await p.evaluate(() => [...document.querySelectorAll("tr[data-header]")].map((r) => [r.dataset.header, r.querySelector("td[data-clang-total]").innerText]));
  check(JSON.stringify(rows.map((r) => r[0])) === JSON.stringify(d.headers.map((h) => h.id)), `index: one row per header (${rows.length})`);
  check(d.headers.every((h, i) => h.clang ? rows[i][1] === `${h.clang.value}: ${h.clang.counts.total} entries` : rows[i][1] === "—"),
    "index: each header's clang route and entry count as the data says");
  if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, "headers-index.png") }); }
  for (const h of d.headers) {
    await open("/headers/" + encodeURIComponent(h.id));
    const pg = await p.evaluate(() => ({
      text: document.querySelector("main").innerText,
      refused: !!document.querySelector('[data-read="refused"]'),
      none: !!document.querySelector('[data-read="none"]'),
      fns: Object.fromEntries([...document.querySelectorAll("tr[data-fn]")].map((r) => [r.dataset.fn,
        Object.fromEntries([...r.querySelectorAll("td[data-abi]")].map((c) => [c.dataset.abi, c.innerText]))])),
      pads: Object.fromEntries([...document.querySelectorAll("h4[data-agg]")].map((h4) => [h4.dataset.agg,
        Object.fromEntries([...h4.nextElementSibling.querySelectorAll("td[data-pad]")].map((c) => [c.dataset.pad, c.innerText.trim()]))])),
      proofs: Object.fromEntries([...document.querySelectorAll("h4[data-agg]")].map((h4) => [h4.dataset.agg,
        Object.fromEntries([...h4.nextElementSibling.querySelectorAll("td[data-proof]")].map((c) => [c.dataset.proof, {
          text: c.innerText.trim(), computed: !!c.querySelector("[data-computed]"),
          links: [...c.querySelectorAll("a[data-thm]")].map((a) => ({ what: a.dataset.thm, decl: a.dataset.decl, text: a.innerText, href: a.getAttribute("href") })),
          names: c.querySelectorAll("[data-thm-name]").length }]))])),
      aggs: Object.fromEntries([...document.querySelectorAll("h4[data-agg]")].map((h4) => [h4.dataset.agg,
        Object.fromEntries([...h4.nextElementSibling.querySelectorAll("td[data-dm]")].map((c) => [c.dataset.dm, c.innerText.trim()]))])),
      counts: Object.fromEntries([...document.querySelectorAll("[data-clang-counts] [data-count]")].map((s) => [s.dataset.count, s.innerText])),
      abiCounts: Object.fromEntries([...document.querySelectorAll("tr[data-abi-count]")].map((r) => [r.dataset.abiCount,
        Object.fromEntries([...r.querySelectorAll("td[data-n]")].map((c) => [c.dataset.n, c.innerText]))])),
      ccsNotes: Object.fromEntries([...document.querySelectorAll("tr[data-abi-count]")].map((r) => [r.dataset.abiCount,
        r.querySelector("[data-ccs-note]")?.innerText ?? null])),
      prov: Object.fromEntries([...document.querySelectorAll("tr[data-prov]")].map((r) => [r.dataset.prov, r.querySelector("td").innerText])),
      entries: [...document.querySelectorAll("tr[data-entry]")].map((r) => ({ i: r.dataset.entry, name: r.dataset.name,
        cc: r.querySelector("td[data-cc]").innerText, symbol: r.querySelector("td[data-symbol]").innerText,
        attrs: r.querySelector("td[data-attrs]").innerText, row: r.innerText,
        st: Object.fromEntries([...r.querySelectorAll("td[data-cabi]")].map((c) => [c.dataset.cabi, { s: c.dataset.status, t: c.innerText }])) })) }));
    // The subset route.
    if (h.read == null) check(pg.none && !pg.refused && Object.keys(pg.fns).length === 0, `${h.id}: no subset-reader route, said so`);
    else if (h.read.refused != null) check(pg.refused && pg.text.includes(h.read.refused), `${h.id}: refused by the subset reader with its reason`);
    else {
      let ok = true;
      for (const fn of h.prototypes) for (const [abi, l] of Object.entries(fn.lowering)) {
        const tx = pg.fns[fn.name]?.[abi] || "";
        if (l.refused != null ? !tx.includes("refused: " + l.refused) : !tx.includes(l.ok)) ok = false;
        if (l.plan && l.plan.ok && !tx.includes(l.plan.ok.result)) ok = false;
      }
      check(ok, `${h.id}: ${h.prototypes.length} prototypes, each ABI's lowering or refusal as the data says`);
      let lok = true;
      for (const a of h.aggregates || []) for (const [dm, L] of Object.entries(a.layouts)) {
        const tx = pg.aggs[a.tag]?.[dm] || "";
        if (L.refused != null ? !tx.includes("refused") : tx !== `${L.ok.size} / ${L.ok.align}`) lok = false;
      }
      check(lok, `${h.id}: ${(h.aggregates || []).length} aggregates, size / align per data model as the data says`);
      const padText = (L) => !L || L.refused != null ? "" : (L.ok.padding.length === 0 ? "none" :
        `${L.ok.paddingBytes} B: ` + L.ok.padding.map(([lo, hi]) => `[${lo}, ${hi})`).join(" ")) + ` (${L.ok.paddingBits} padding bits)`;
      check((h.aggregates || []).every((a) => d.dataModels.every((dm) => { const L = a.layouts[dm];
        return !L || L.refused != null || L.ok.padding.reduce((n, [lo, hi]) => n + hi - lo, 0) === L.ok.paddingBytes; })),
        `${h.id}: the padding ranges add up to the library's paddingBytes`);
      check((h.aggregates || []).every((a) => d.dataModels.every((dm) => (pg.pads[a.tag]?.[dm] ?? "") === padText(a.layouts[dm]))),
        `${h.id}: each aggregate's padding per data model as the data says`);
      // theorem links: exactly where the data has a proof, with its names and source lines
      const linkOk = (l, t, what) => l && l.what === what && l.decl === t.decl && l.text === t.decl &&
        l.href.includes("/blob/") && l.href.endsWith("/" + t.file + "#L" + t.line);
      let nThm = 0, nComp = 0, bad3 = "";
      for (const a of h.aggregates || []) for (const dm of d.dataModels) {
        const L = a.layouts[dm], c = pg.proofs[a.tag]?.[dm];
        const ok = !c ? false : L.proof ? (nThm++, !c.computed && c.links.length === 2 && linkOk(c.links[0], L.proof, "layout") &&
            linkOk(c.links[1], L.proof.padding, "padding") && L.proof.status === "proved" && L.proof.padding.status === "proved")
          : (nComp++, c.computed && c.text === "computed, not a theorem" && c.links.length === 0 && c.names === 0);
        if (!ok) bad3 ||= `${a.tag}/${dm}`;
      }
      check(!bad3, `${h.id}: ${nThm} layout columns name their layout and padding theorems as the data says (linked to their source lines), ${nComp} say "computed, not a theorem" with no link ${bad3}`);
      if (h.id === "layout-demo") {
        const want = (h.aggregates || []).flatMap((a) => [["sysvX86_64", "sysv"], ["msX64", "ms"]].map(([dm, s]) =>
          [a.layouts[dm].proof?.decl, a.layouts[dm].proof?.padding?.decl, `Silmaril.Data.Layout.Header.Demo.${a.tag}_${s}`]));
        check(want.length === 14 && want.every(([l, p, n]) => l === n && p === n + "_padding") && h.text === "Silmaril.Data.Layout.Header.Demo.demoH",
          `layout-demo: all 14 layout columns carry a proof (Header.Demo.<tag>_<sysv|ms> and _padding), read from Header.Demo.demoH`);
      } else check((h.aggregates || []).every((a) => d.dataModels.every((dm) => a.layouts[dm].proof == null)), `${h.id}: no layout carries a proof`);
    }
    // The clang route.
    if (!h.clang) check(!!(await p.$('[data-clang="none"]')) && pg.entries.length === 0, `${h.id}: no clang route, said so`);
    else {
      const c = h.clang, pv = c.provenance;
      check(Object.entries(c.counts).every(([k, v]) => pg.counts[k] === String(v)) && Object.keys(pg.counts).length === 4,
        `${h.id}: clang counts as the data says (${JSON.stringify(c.counts)})`);
      check(d.abis.every((a) => ["interface", "claimable", "unsupported"].every((k) => pg.abiCounts[a.name]?.[k] === String(c.abiCounts[a.name][k]))),
        `${h.id}: per-ABI interface / claimable / unsupported counts as the data says`);
      check(d.abis.every((a) => pg.ccsNotes[a.name] === a.clangCcsNote) && /default C convention is System V/.test(pg.ccsNotes.win64Int || ""), `${h.id}: each ABI's accepted conventions carry their note (win64Int: the Linux target's default is System V)`);
      check(pg.prov.image === pv.image && pg.prov.clang === pv.clang && pg.prov.target === pv.target && pg.prov.std === pv.std &&
        pv.inputs.every((i) => pg.prov.inputs.includes(i.file) && pg.prov.inputs.includes(i.sha256)) &&
        pg.prov.JSON.includes(pv.jsonSha256) && pv.defines.every((x) => pg.prov.defines.includes(x)),
        `${h.id}: provenance (image, clang, target, std, defines, inputs with SHA-256, JSON SHA-256) as the data says`);
      let eok = pg.entries.length === c.entries.length, bad1 = "";
      c.entries.forEach((e, i) => {
        const r = pg.entries[i];
        const ok = r && r.name === e.name && r.cc === (e.cc ?? "") && r.symbol.startsWith(e.symbol ?? "") &&
          (e.asmLabel == null || r.symbol.includes("asm label " + e.asmLabel)) && r.attrs === (e.attrs || []).join(", ") &&
          (!e.loc || r.row.includes(`${e.loc.file}:${e.loc.line}`)) &&
          (e.decl.ok != null ? r.row.includes(e.decl.ok) : r.row.includes("import: " + e.decl.unsupported)) &&
          d.abis.every((a) => r.st[a.name]?.s === e.status[a.name].status && r.st[a.name].t.startsWith(statusText(e.status[a.name])) &&
            (e.status[a.name].status !== "claimable" || !e.lowering?.[a.name]?.ok || r.st[a.name].t.includes(e.lowering[a.name].ok)) &&
            (a.name !== "sysvScalar" || e.status[a.name].status !== "claimable" || !e.lowering?.sysvScalar?.plan?.ok || r.st[a.name].t.includes("result: " + e.lowering.sysvScalar.plan.ok.result)));
        if (!ok) { eok = false; bad1 ||= `#${i} ${e.name}`; }
      });
      check(eok, `${h.id}: ${c.entries.length} clang entries: name, location, declaration, convention, attributes, symbol, and each ABI's status (and claimable plans) as the data says ${bad1}`);
    }
    check(!/\b(theorem proved|proved|verified)\b/i.test(pg.text.replace(/not theorems/g, "")), `${h.id}: nothing is called proved or verified`);
    if (h.id === "arith" || h.id.startsWith("zlib")) check((h.aggregates || []).every((a) => d.dataModels.every((dm) => !a.layouts[dm].proof)) &&
      !(await p.$("a[data-thm], [data-thm-name]")), `${h.id}: no theorem is named (${(h.aggregates || []).length} aggregates, all computed)`);
    const st = (n) => pg.entries.find((e) => e.name === n)?.st || {};
    if (h.id === "probe") {
      check(pg.refused && pg.entries.length > 0, "probe: the subset route is refused, the clang route shows entries");
      const ccOf = (n) => pg.entries.find((e) => e.name === n)?.cc;
      check(ccOf("win") === "ms_abi" && ccOf("sysv") === "sysv_abi" && ccOf("rc") === "regcall", "probe: win ms_abi, sysv sysv_abi, rc regcall");
      check(st("win").win64Int?.s === "claimable" && st("win").sysvInt?.t === "unsupported: calling convention ms_abi" &&
        st("rc").sysvScalar?.t === "unsupported: calling convention regcall" && st("sysv").sysvScalar?.s === "claimable",
        "probe: the ms_abi function is claimable only under win64Int; regcall is unsupported; sysv_abi is claimable under sysvScalar");
      const ren = pg.entries.find((e) => e.name === "renamed");
      check(ren && ren.symbol.includes("renamed_v2") && ren.symbol.includes("asm label renamed_v2") && /^unsupported: asm label/.test(ren.st.sysvInt?.t || ""),
        "probe: renamed has symbol and asm label renamed_v2, unsupported for the asm label");
      if (shots) await p.screenshot({ path: path.join(shots, "headers-probe.png"), fullPage: true });
    }
    if (h.id === "glibc-string") {
      const s = pg.entries.find((e) => e.name === "strerror_r");
      check(!!s && s.symbol.includes("asm label __xpg_strerror_r") && Object.values(s.st).every((x) => x.s === "unsupported"),
        "glibc-string: strerror_r with asm label __xpg_strerror_r, unsupported under every ABI");
      check(pg.entries.some((e) => /^internal: implicit/.test(e.st.sysvInt?.t || "")), "glibc-string: clang's implicit builtin declarations are internal");
      if (shots) await p.screenshot({ path: path.join(shots, "headers-glibc-string.png"), fullPage: true });
    }
    if (h.id === "layout-demo") {
      check(/xmm0/.test(pg.fns.scale?.sysvScalar || "") && /refused/.test(pg.fns.scale?.sysvInt || ""), "layout-demo: double scale(double, float, int) uses xmm registers under sysvScalar, refused by sysvInt");
      check(pg.aggs.pt?.sysvX86_64 === "24 / 8" && pg.aggs.pt?.msX64 === "12 / 4", "layout-demo: struct pt is 24/8 under System V, 12/4 under Microsoft x64");
      check(pg.pads.pt?.sysvX86_64 === "13 B: [1, 8) [18, 24) (104 padding bits)" && pg.pads.pt?.msX64 === "5 B: [1, 4) [10, 12) (40 padding bits)",
        `layout-demo: struct pt's padding: System V [1,8) [18,24), Microsoft x64 [1,4) [10,12) (${JSON.stringify(pg.pads.pt)})`);
      check(/args: rcx\[0\.\.8\)/.test(pg.fns.rec_size?.win64Int || "") && /result: rax\[0\.\.4\)/.test(pg.fns.rec_size?.win64Int || "") &&
        /outgoing stack: 32 B/.test(pg.fns.rec_size?.win64Int || "") && /shadow space/.test(pg.fns.rec_size?.win64Int || ""),
        "layout-demo: long rec_size(struct rec *) under win64Int: rcx → eax (LLP64 long is 4 bytes), 32 B outgoing (shadow space)");
      if (shots) await p.screenshot({ path: path.join(shots, "headers-layout-demo.png"), fullPage: true });
    }
  }
  check(errors.length === 0, `no page or console errors ${errors.join("; ")}`);

  // The tampered copy: markup in the data is text.
  const terr = [];
  const tp = await b.newPage({ viewport: { width: 1500, height: 1400 } });
  tp.on("pageerror", (e) => terr.push("pageerror: " + e.message));
  tp.on("console", (m) => { if (m.type() === "error") terr.push("console: " + m.text()); });
  const tsettle = () => tp.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const injected = () => tp.evaluate(() => ({ pwn: window.__pwn, imgs: document.querySelectorAll("main img").length,
    scripts: document.querySelectorAll("main script").length, text: document.querySelector("main").innerText }));
  for (const [hash, what, must] of [["/headers", "index", [P1]], ["/headers/tamper", "header page (both routes)", [P1, P2, P1 + P2, P2 + " " + P1, P1 + " " + P2]],
    ["/headers/" + encodeURIComponent(P2), "header page (subset route)", [P1, P2]]]) {
    await tp.goto("about:blank"); await tp.goto(`http://127.0.0.1:${tport}/index.html#${hash}`); await tsettle();
    await new Promise((r) => setTimeout(r, 500));
    const r = await injected();
    check(r.pwn === undefined && r.imgs === 0 && r.scripts === 0, `tamper ${what}: no injected element runs (window.__pwn ${r.pwn}, img ${r.imgs}, script ${r.scripts})`);
    check(must.every((s) => r.text.includes(s)), `tamper ${what}: the markup is shown literally`);
    if (shots && hash === "/headers/tamper") await tp.screenshot({ path: path.join(shots, "headers-tamper.png"), fullPage: true });
  }
  // the tampered layout-demo copy: a dropped and a non-proved proof are "computed", markup in a theorem name is text
  const tc = await tp.evaluate(() => Object.fromEntries([...document.querySelectorAll("h4[data-agg]")].map((h4) => [h4.dataset.agg,
    Object.fromEntries([...h4.nextElementSibling.querySelectorAll("td[data-proof]")].map((c) => [c.dataset.proof,
      { text: c.innerText.trim(), links: c.querySelectorAll("a[data-thm], [data-thm-name]").length }]))])));
  const [a0, a1, a2] = bad2.aggregates.map((a) => a.tag);
  check(tc[a0]?.sysvX86_64?.text === "computed, not a theorem" && tc[a0].sysvX86_64.links === 0 &&
    tc[a1]?.sysvX86_64?.text === "computed, not a theorem" && tc[a1].sysvX86_64.links === 0,
    `tamper: a dropped proof and a proof whose status is not "proved" show "computed, not a theorem", no link (${JSON.stringify([tc[a0]?.sysvX86_64, tc[a1]?.sysvX86_64])})`);
  check((tc[a2]?.msX64?.text || "").includes(P1 + P2) && (tc[a2]?.msX64?.text || "").includes(P2), "tamper: markup in theorem names is shown literally");
  check(terr.length === 0, `tamper: no page or console errors ${terr.join("; ")}`);
} finally { await b.close(); srv.kill(); tsrv.kill(); fs.rmSync(tdir, { recursive: true, force: true }); }
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
