// The explorer reads one snapshot of a lazily read database, in Chromium, against pages_server.py
// (GitHub-Pages-like: a strong ETag from mtime and length on range responses). The database file
// is replaced on the server while the page has it open, as `sil project sqlite` or a deploy does:
//   1. by a larger file, during repeated graph navigation: no "malformed" error and no rows of the
//      new file; the page says the database changed, marks the source button, and opens the new
//      version on request;
//   2. by a different file of the same length (a new mtime only tells them apart);
//   3. while a query is in flight;
//   4. recovery by choosing a local file after a change;
//   5. a damaged file that is NOT replaced is reported as damage of the file itself, not as a
//      version change;
//   6. servers without a strong ETag (a weak one, Last-Modified only, none): the page reads the
//      file whole, in one response, so a same-size replacement within the same second cannot mix
//      into it; past the size limit it asks before reading a file whole.
// Before the per-read check, (1) failed with "SQLite: database disk image is malformed".
//
//   node snapshot.mjs SITE_DIR [SHOTS_DIR]   (SITE_DIR holds index.html, explore-sw.js and project.sqlite;
//   it is copied, not changed)
import { spawn, execFileSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "explore-snapshot-"));
const root = path.join(work, "site");
fs.mkdirSync(root);
for (const f of ["index.html", "explore-sw.js", "project.sqlite"]) fs.copyFileSync(path.join(site, f), path.join(root, f));
const v1 = path.join(work, "v1.sqlite"), v2 = path.join(work, "v2.sqlite"), v3 = path.join(work, "v3.sqlite"), bad = path.join(work, "bad.sqlite");
fs.copyFileSync(path.join(site, "project.sqlite"), v1);
// Use a compact project-only copy for transport mutation cases. The complete
// combined deployed DB is exercised by shell/corpus/compiler browser checks.
// Removing additive corpus tables here keeps weak-validator whole-file tests
// bounded and makes the same-size replacement independent of prior free pages.
// v2: 400 more problems (a longer file); v3: the same length, other titles; bad: v1 with the
// edges table's pages overwritten.
execFileSync("python3", ["-I", "-c", `
import sqlite3, shutil, sys, os
v1, v2, v3, bad = sys.argv[1:5]
c = sqlite3.connect(v1)
for (name,) in c.execute("select name from sqlite_master where type='table' and name glob 'corpus_*'").fetchall():
    c.execute('DROP TABLE "' + name.replace('"', '""') + '"')
c.commit(); c.execute("vacuum"); c.close()
for out in (v2, v3): shutil.copy(v1, out)
c = sqlite3.connect(v2)
cols = [r[1] for r in c.execute("pragma table_info(problems)")]
row = c.execute("select * from problems limit 1").fetchone()
for i in range(400):
    r = list(row); r[cols.index("name")] = "aaa.snapshot%04d" % i; r[cols.index("sid")] = "%064x" % (i + 1)
    c.execute("insert into problems values (%s)" % ",".join("?" * len(r)), r)
c.commit(); c.execute("vacuum"); c.close()
c = sqlite3.connect(v3)
c.execute("update problems set title = upper(title)"); c.commit(); c.execute("vacuum"); c.close()
assert os.path.getsize(v3) == os.path.getsize(v1), (os.path.getsize(v3), os.path.getsize(v1))
shutil.copy(v1, bad)
c = sqlite3.connect(v1)
pages = [r[0] for r in c.execute("select pageno from dbstat where name in ('edges', 'edges_parent', 'edges_child')")] if False else []
c.close()
data = bytearray(open(bad, "rb").read())
ps = int.from_bytes(data[16:18], "big")
n = len(data) // ps
# the schema's pages (sqlite_schema): a grown schema can have a page anywhere, even last
c = sqlite3.connect(v1)
schema = {r[0] for r in c.execute("select pageno from dbstat where name = 'sqlite_schema'")}
c.close()
for p in range(n // 3, n):            # leave the schema and the first tables, overwrite the rest
    if p + 1 not in schema:           # dbstat numbers pages from 1
        data[p * ps:(p + 1) * ps] = bytes([0x5a]) * ps
open(bad, "wb").write(bytes(data))
`, v1, v2, v3, bad]);

fs.copyFileSync(v1, path.join(root, "project.sqlite"));
const port = 8796;
const log = path.join(work, "requests.jsonl");
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", root, "--port", String(port), "--log", log], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
// Replace the served file as a rebuild does (a new file renamed into place), with a new mtime.
let bump = 0;
const replace = (from) => {
  const dst = path.join(root, "project.sqlite"), tmp = dst + ".tmp";
  fs.copyFileSync(from, tmp);
  const t = new Date(Date.now() + 60000 * ++bump);
  fs.utimesSync(tmp, t, t);
  fs.renameSync(tmp, dst);
};
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const ctx = await b.newContext({ viewport: { width: 1400, height: 900 } });
  const p = await ctx.newPage();
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message + " " + (e.stack || "").split("\n").slice(0, 4).join(" | ")));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const shot = async (n) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, n) }); } };
  const pageText = () => p.evaluate(() => document.body.innerText);
  const go = async (h) => { await p.evaluate((h) => { location.hash = h; }, h); await p.waitForTimeout(20); await settle(); };
  const names = execFileSync("python3", ["-I", "-c",
    "import sqlite3,sys;print('\\n'.join(r[0] for r in sqlite3.connect(sys.argv[1]).execute('select name from problems order by name desc limit 40')))", v1])
    .toString().trim().split("\n");
  // problems whose v3 title differs (v3 upper-cases titles), from the end of the name order
  const titled = JSON.parse(execFileSync("python3", ["-I", "-c",
    "import sqlite3,sys,json;print(json.dumps([dict(name=r[0],title=r[1]) for r in sqlite3.connect(sys.argv[1]).execute(\"select name, title from problems where title <> upper(title) order by name desc limit 12\")]))", v1]).toString());
  let loads = 0;
  const open = async () => {
    // a new query each time, so that it is a real page load (not a same-document hash change)
    await p.goto(`http://127.0.0.1:${port}/index.html?cache=off&vfs-chunk=page&n=${++loads}#/graph`);
    await settle();
    const mode = await p.evaluate(() => window.explore.mode);
    check(/^lazy/.test(mode), "opened lazily: " + mode);
  };
  const walk = async (list) => {
    for (const n of list) { await go("#/graph/" + encodeURIComponent(n)); await go("#/problem/" + encodeURIComponent(n)); }
  };
  const sawMalformed = async () => /malformed/i.test(await pageText());

  // 1. a longer file, during graph navigation
  await open();
  await walk(names.slice(0, 3));
  replace(v2);
  await walk(names.slice(3, 15));
  let st = await p.evaluate(() => ({ changed: window.explore.changed, warn: !!document.querySelector("#source .src-warn"),
    notice: !!document.querySelector("#reopen"), text: document.body.innerText }));
  check(!(await sawMalformed()), "1. no malformed error after the file was replaced");
  check(st.changed && st.changed.now && st.changed.now !== st.changed.was, `1. the change is detected: ${JSON.stringify(st.changed)}`);
  check(st.warn && st.notice, "1. the source button is marked and the view offers the new version");
  check(!/aaa\.snapshot/.test(st.text), "1. no row of the new file is shown under the old version");
  await shot("snapshot-changed.png");
  await p.click("#reopen");
  await p.waitForFunction(() => window.explore.changed === null && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  await go("#/problems");
  await p.fill("#filter", "aaa.snapshot0001");
  await p.waitForFunction(() => /aaa\.snapshot0001/.test(document.querySelector("#list").innerText), null, { timeout: 20000 });
  await walk(names.slice(15, 20));
  check(!(await sawMalformed()) && !(await p.evaluate(() => window.explore.changed)), "1. the new version opens and reads cleanly");

  // 2. the same length, another file
  replace(v1);
  await open();
  await walk(names.slice(0, 2));
  replace(v3);
  await walk(names.slice(20, 32));
  st = await p.evaluate(() => window.explore.changed);
  check(!(await sawMalformed()) && st && st.now && st.now !== st.was && st.now.endsWith(st.was.slice(st.was.indexOf("-"))), `2. a same-length replacement is detected: ${JSON.stringify(st)}`);

  // 3. a replacement while a query is in flight
  replace(v1);
  await open();
  await p.evaluate(() => { location.hash = "#/graph/" + encodeURIComponent("silmaril.all"); });
  replace(v2);
  await settle();
  await walk(names.slice(32, 40));
  st = await p.evaluate(() => window.explore.changed);
  check(!(await sawMalformed()) && !!st, "3. a replacement during a query is detected, not mixed");

  // 4. recovery by choosing a local file
  await p.click("#source");
  const n0 = await p.evaluate(() => window.explore.opened);
  await p.setInputFiles("dialog.dlg input[type=file]", v1);
  await p.waitForFunction((n) => window.explore.opened > n && !window.explore.busy, n0, { timeout: 60000 });
  await walk(names.slice(0, 4));
  check(await p.evaluate(() => window.explore.mode === "local file" && !window.explore.changed && !document.querySelector("#source .src-warn")),
    "4. a chosen file replaces the changed database");

  // 5. real damage, same version: reported as such
  // Where the damage falls decides when it shows: in pages a later view reads (then that view's
  // query reports it, the version being unchanged), or in the schema (then the file is not
  // opened at all, and the page says why). Either way it is damage, not a change.
  replace(bad);
  await p.goto(`http://127.0.0.1:${port}/index.html?cache=off&vfs-chunk=page&n=${++loads}#/graph`);
  await p.waitForFunction(() => window.explore && ((window.explore.ready && !window.explore.busy) || window.explore.failed), null, { timeout: 60000 });
  let t5;
  if (await p.evaluate(() => !!window.explore.failed)) {
    t5 = await pageText();
    check(/malformed|not a database/.test(t5) && /damaged/.test(t5) && !(await p.evaluate(() => window.explore.changed)),
      "5. a damaged file is reported as damage, not as a change (its schema is unreadable: not opened)");
  } else {
    await walk(names.slice(0, 6));
    await go("#/graph");
    t5 = await pageText();
    check(/not a mix of two versions/.test(t5) && !(await p.evaluate(() => window.explore.changed)), "5. a damaged file is reported as damage, not as a change");
  }
  await shot("snapshot-damaged.png");

  // 6. no strong ETag: one response, one file
  for (const [i, mode] of ["weak", "lastmod", "none"].entries()) {
    const root2 = path.join(work, "site-" + mode), port2 = 8798 + i;
    fs.mkdirSync(root2);
    for (const f of ["index.html", "explore-sw.js"]) fs.copyFileSync(path.join(site, f), path.join(root2, f));
    fs.copyFileSync(v1, path.join(root2, "project.sqlite"));
    const t0 = new Date(Math.floor(Date.now() / 1000) * 1000);
    fs.utimesSync(path.join(root2, "project.sqlite"), t0, t0);
    const s2 = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
      "--root", root2, "--port", String(port2), "--log", path.join(work, mode + ".jsonl"), "--validators", mode], { stdio: "ignore" });
    try {
      await new Promise((r) => setTimeout(r, 800));
      // open on a page that reads almost nothing, so that what follows reads after the replacement
      await p.goto(`http://127.0.0.1:${port2}/index.html?cache=off&n=${++loads}#/about`);
      await settle();
      const m = await p.evaluate(() => window.explore.mode);
      check(/^whole file \(the server sent no strong ETag/.test(m), `6. ${mode}: read whole: ${m}`);
      // the same size and the same mtime: nothing in the headers tells the two files apart
      const dst = path.join(root2, "project.sqlite");
      fs.copyFileSync(v3, dst + ".tmp"); fs.utimesSync(dst + ".tmp", t0, t0); fs.renameSync(dst + ".tmp", dst);
      // problems not read before the replacement: their titles must be v1's, not v3's upper case
      let mixed = 0;
      for (const t of titled.slice(0, 12)) {
        await go("#/problem/" + encodeURIComponent(t.name));
        const text = await p.evaluate(() => document.querySelector("#main").innerText);
        if (!text.includes(t.title) || /malformed/i.test(text)) mixed++;
      }
      check(mixed === 0, `6. ${mode}: a same-size, same-second replacement leaves the opened snapshot intact (${mixed} of 12 unread problems differ)`);
      if (mode === "lastmod") {
        await p.goto(`http://127.0.0.1:${port2}/index.html?cache=off&whole-limit=100000&n=${++loads}#/problems`);
        await p.waitForSelector("button.loadwhole", { timeout: 30000 });
        const msg = await p.evaluate(() => document.querySelector("#main").innerText);
        check(/would be read whole into memory/.test(msg) && /no strong ETag/.test(msg), "6. past the limit, the page says why and asks");
        await shot("snapshot-too-large.png");
        await p.click("button.loadwhole");
        await p.waitForFunction(() => window.explore.ready && /^whole file/.test(window.explore.mode || "") && !window.explore.busy, null, { timeout: 60000 });
        check(true, "6. reading it whole on request opens it");
      }
    } finally { s2.kill(); }
  }
  check(errors.length === 0, "no page errors " + errors.join("; "));
} finally {
  await b.close(); srv.kill();
  fs.rmSync(work, { recursive: true, force: true });
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all ok");
