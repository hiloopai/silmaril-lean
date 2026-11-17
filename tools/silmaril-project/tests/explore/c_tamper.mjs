// Negative tests of the explorer's C tab (explore/views/c.js) on a tampered copy of a pages site:
// * a corpus file whose bytes changed: the stage viewer reports a SHA-256 MISMATCH with
//   provenance.json, never a match;
// * a provenance.json whose recorded hashes were changed: the page reports that it differs from
//   the artifact registered in the project database;
// * hostile text in a source file and in provenance metadata (HTML and script): rendered as text,
//   no element injected, no script run;
// * a gzip bomb in place of a .gz artifact: the viewer stops at its decompression bound with an
//   error instead of exhausting memory.
//   node c_tamper.mjs SITE_DIR [SHOTS_DIR]     (SITE_DIR is copied; it is not modified)
import { spawn } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import zlib from "node:zlib";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const orig = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const site = fs.mkdtempSync(path.join(os.tmpdir(), "c-tamper-"));
fs.cpSync(orig, site, { recursive: true });
const progs = (n) => path.join(site, "c", "programs", n);
const idx = JSON.parse(fs.readFileSync(path.join(site, "c", "programs", "index.json")));
const elaborated = idx.programs.filter((p) => fs.existsSync(path.join(progs(p.name), "cerberus.core.sexp.gz")) || fs.existsSync(path.join(progs(p.name), "clang.core.sexp.gz")));
const [A, B, C, D] = [elaborated[0].name, elaborated[1].name, elaborated[2].name, elaborated[3].name];
// A: change source.c's bytes, leave provenance.json alone.
fs.appendFileSync(path.join(progs(A), "source.c"), "/* tampered */\n");
// B: change provenance.json's record of source.c (and so its own bytes).
{ const f = path.join(progs(B), "provenance.json"); const j = JSON.parse(fs.readFileSync(f)); j.artifacts["source.c"].sha256 = "0".repeat(64); fs.writeFileSync(f, JSON.stringify(j)); }
// C: hostile text in source.c (re-recorded so its hash matches) and in provenance metadata.
{ const hostile = '<img src=x onerror="window.__cxss=1"><script>window.__cxss=2</script>\n';
  fs.writeFileSync(path.join(progs(C), "source.c"), hostile);
  const f = path.join(progs(C), "provenance.json"); const j = JSON.parse(fs.readFileSync(f));
  j.artifacts["source.c"].sha256 = crypto.createHash("sha256").update(hostile).digest("hex");
  j.losses = [{ route: "<b>r</b>", construct: '<img src=x onerror="window.__cxss=3">', blocking: true, rule: "<script>window.__cxss=4</script>", why: "x" }];
  j.warnings = ['<img src=x onerror="window.__cxss=5">'];
  fs.writeFileSync(f, JSON.stringify(j)); }
// D: a gzip bomb (40 MiB of zeros) in place of a Core document.
const bombName = fs.existsSync(path.join(progs(D), "cerberus.core.sexp.gz")) ? "cerberus.core.sexp.gz" : "clang.core.sexp.gz";
fs.writeFileSync(path.join(progs(D), bombName), zlib.gzipSync(Buffer.alloc(40 << 20)));

const port = 8799;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/c_tamper_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1100 } });
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const view = async (file) => {
    await p.click(`button.cview[data-file="${file}"]`);
    await p.waitForFunction((f) => document.querySelector(`button.cview[data-file="${f}"]`)?.parentElement.querySelector(".csha")?.textContent, file, { timeout: 30000 });
    return p.evaluate((f) => { const s = document.querySelector(`button.cview[data-file="${f}"]`).parentElement.querySelector(".csha"); return { m: s.dataset.match, t: s.textContent }; }, file);
  };
  await open(`/c-program/${A}`);
  const a = await view("source.c");
  check(a.m === "false" && /MISMATCH/.test(a.t), `${A}: changed source.c bytes are reported as a mismatch (${a.t.slice(0, 60)})`);
  if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, "c-tamper-bytes.png"), fullPage: true }); }

  await open(`/c-program/${B}`);
  const bdb = await p.evaluate(() => [...document.querySelectorAll("#cdb li")].map((l) => ({ k: l.dataset.db, ok: l.dataset.ok })));
  check(bdb.length === 2 && bdb.every((x) => x.ok === "false"), `${B}: a changed provenance.json differs from the registered artifact, and so does its source record`);

  await open(`/c-program/${C}`);
  await view("source.c");
  const c = await p.evaluate(() => ({ xss: window.__cxss, imgs: document.querySelectorAll("#main img").length, scripts: document.querySelectorAll("#main script").length,
    text: [...document.querySelectorAll("pre.cbody")].map((x) => x.textContent).join("") }));
  check(c.xss === undefined && c.imgs === 0 && c.scripts === 0, `${C}: hostile source and metadata injected no element and ran no script`);
  check(c.text.includes("<img src=x"), `${C}: the hostile source is shown as text`);
  const cdb = await p.evaluate(() => [...document.querySelectorAll("#cdb li")].map((l) => l.dataset.ok));
  check(cdb.every((x) => x === "false"), `${C}: re-recorded hashes in provenance.json still differ from the project database`);

  await open(`/c-program/${D}`);
  const d = await view(bombName);
  check(/exceeds the 32 MiB bound/.test(d.t), `${D}: a gzip bomb stops at the decompression bound (${d.t.slice(0, 80)})`);
} finally {
  await b.close();
  srv.kill();
  fs.rmSync(site, { recursive: true, force: true });
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
