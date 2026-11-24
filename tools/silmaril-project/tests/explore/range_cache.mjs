// Run with node range_cache.mjs SITE_DIR. Uses the generated explorer and a
// private fixture so the test can replace the served DB without changing SITE_DIR.
import assert from "node:assert/strict";
import { spawn, execFileSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";

const site = path.resolve(process.argv[2]);
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const localChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
const chrome = process.env.CHROME || (fs.existsSync(localChrome) ? localChrome : undefined);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "explore-ranges-"));
const dbPath = path.join(tmp, "project.sqlite");
const replacement = path.join(tmp, "replacement.sqlite");
const log = path.join(tmp, "requests.jsonl");
const chunk = 1024 * 1024;
const pageSize = 4096;
const port = 8766 + (process.pid % 500);
const server = `http://127.0.0.1:${port}`;

for (const f of ["index.html", "explore-sw.js"]) fs.copyFileSync(path.join(site, f), path.join(tmp, f));
execFileSync("python3", ["-I", "-c", `
import shutil, sqlite3, sys
db = sqlite3.connect(sys.argv[1])
db.executescript("""
PRAGMA page_size = 4096;
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
INSERT INTO meta VALUES ('schema', 'silmaril.project-db.v0.1');
CREATE TABLE padding (value BLOB);
INSERT INTO padding VALUES (zeroblob(3 * 1024 * 1024));
CREATE TABLE tail (value TEXT);
INSERT INTO tail VALUES ('old title');
""")
db.close()
shutil.copyfile(sys.argv[1], sys.argv[2])
with sqlite3.connect(sys.argv[2]) as db:
    db.execute("UPDATE tail SET value = 'new title'")
`, dbPath, replacement]);
const size = fs.statSync(dbPath).size;
assert.equal(fs.statSync(replacement).size, size);
assert.ok(size > 3 * chunk && size < 4 * chunk);
const tailOffset = 3 * chunk;
const tinyPath = path.join(tmp, "tiny.sqlite");
execFileSync("python3", ["-I", "-c", `
import sqlite3, sys
with sqlite3.connect(sys.argv[1]) as db:
    db.execute("PRAGMA page_size = 4096")
    db.execute("VACUUM")
`, tinyPath]);
assert.equal(fs.statSync(tinyPath).size, pageSize);

const srv = spawn("python3", ["-I", new URL("./pages_server.py", import.meta.url).pathname,
  "--root", tmp, "--port", String(port), "--log", log], { stdio: "inherit" });
const browser = await pw.chromium.launch({ executablePath: chrome });
try {
  for (let i = 0; ; i++) {
    try { if ((await fetch(server)).ok) break; } catch { /* waiting for listen */ }
    if (i === 100) throw new Error("Pages test server did not start");
    await new Promise(resolve => setTimeout(resolve, 25));
  }
  const ctx = await browser.newContext();
  const page = await ctx.newPage();
  const entries = () => fs.readFileSync(log, "utf8").trim().split("\n").filter(Boolean).map(JSON.parse)
    .filter(e => e.path.endsWith(".sqlite"));
  const ranges = () => entries().filter(e => new URLSearchParams(e.query).has("__sil_part"));
  const clear = () => fs.writeFileSync(log, "");
  let nav = 0;
  async function open(query = "", currentPage = page) {
    await currentPage.goto(`${server}/index.html?nav=${++nav}${query}#/summary`);
    await currentPage.waitForFunction(() => window.explore?.failed || (window.explore?.ready && !window.explore.busy));
    const state = await currentPage.evaluate(() => ({ ...window.explore, profiling: typeof window.explore.vfsProfile === "function" }));
    assert.ok(!state.failed, JSON.stringify(state));
    return state;
  }
  function checkRangeOnly() {
    assert.ok(entries().every(e => e.method === "GET" && e.range && e.status === 206), JSON.stringify(entries()));
  }
  const trace = () => page.evaluate(() => window.explore.vfsProfile());
  const readTail = () => page.evaluate(async () => (await q("SELECT value FROM tail"))[0].value);
  const replace = () => {
    const t = new Date(Date.now() + 120000);
    fs.utimesSync(replacement, t, t);
    fs.renameSync(replacement, dbPath);
  };

  clear();
  const ordinary = await open();
  assert.match(ordinary.mode, /^lazy .*1048576 B chunks/);
  assert.equal(ordinary.profiling, false);
  assert.equal(ordinary.stats.totalFetchedBytes, chunk);
  checkRangeOnly();
  assert.deepEqual(ranges().map(e => e.range), [`bytes=0-${chunk - 1}`]);
  console.log("ok default is one aligned 1 MiB range and a probe, without HEAD or profiling");

  clear();
  const warm = await open("&vfs-profile=1");
  checkRangeOnly();
  assert.equal(ranges().length, 0);
  assert.equal(entries().length, 1);
  const warmTrace = await trace();
  assert.equal(warmTrace.pageSize, pageSize);
  assert.equal(warmTrace.chunkSize, chunk);
  assert.ok(warmTrace.events.some(e => e.type === "read" && e.bytes < chunk));
  assert.deepEqual(warmTrace.events.filter(e => e.type === "fetch").map(e => [e.start, e.end, e.source, e.accepted]),
    [[0, chunk, "cache-storage", true]]);
  assert.equal((await trace()).events.length, 0);
  assert.match(warm.mode, /cached across reloads/);
  console.log("ok warm replay serves the 1 MiB range from Cache Storage and can drain the trace");

  clear();
  assert.equal(await readTail(), "old title");
  const tail = (await trace()).events.find(e => e.type === "fetch");
  assert.deepEqual([tail.start, tail.end, tail.bytes, tail.responseStart, tail.responseEnd, tail.source],
    [tailOffset, size, size - tailOffset, tailOffset, size, "http"]);
  assert.equal(tail.lastPage, size / pageSize);
  assert.ok(tail.accepted && tail.durationMs >= 0);
  checkRangeOnly();
  assert.deepEqual(ranges().map(e => e.range), [`bytes=${tailOffset}-${size - 1}`]);
  console.log("ok EOF block is fetched with its exact inclusive HTTP range and reported with exclusive offsets");

  // Start with an empty cache. The old snapshot must miss the tail after a
  // same-length replacement, so the new strong ETag is checked before SQLite sees it.
  const other = await browser.newContext();
  try {
    const stalePage = await other.newPage();
    const stale = await open("&vfs-profile=1", stalePage);
    replace();
    const rejected = await stalePage.evaluate(async () => {
      try { await q("SELECT value FROM tail"); return null; }
      catch (e) { return { name: e.name, was: e.was, now: e.now }; }
    });
    assert.equal(rejected?.name, "SourceChanged");
    assert.ok(rejected.now && rejected.was !== rejected.now);
    const failedFetch = (await stalePage.evaluate(() => window.explore.vfsProfile())).events.find(e => e.type === "fetch" && !e.accepted);
    assert.equal(failedFetch.start, tailOffset);
    const fresh = await open("", stalePage);
    assert.notEqual(fresh.mode, stale.mode);
    assert.equal(await stalePage.evaluate(async () => (await q("SELECT value FROM tail"))[0].value), "new title");
    const cachedVersions = await stalePage.evaluate(async () => {
      const cache = await caches.open("silmaril-explore-db-pages-v3");
      return (await cache.keys()).map(k => new URL(k.url).searchParams.get("__sil_v"));
    });
    assert.ok(!cachedVersions.includes(rejected.was));
    console.log("ok same-length replacements reject the stale read and reopen under the new version");
  } finally {
    await other.close();
  }

  clear();
  const brokenOrigin = await browser.newContext();
  try {
    const badResponse = brokenOrigin.waitForEvent("response", {
      predicate: res => res.fromServiceWorker() && new URL(res.url()).searchParams.has("__sil_part"),
    });
    // Keep the probe valid, then have the origin ignore Range on the tagged read.
    await brokenOrigin.route(url => url.pathname === "/project.sqlite" && url.searchParams.has("__sil_part"),
      route => route.fulfill({ status: 200, body: "the origin's whole-file response" }));
    const failed = await brokenOrigin.newPage();
    await failed.goto(`${server}/index.html`);
    await failed.waitForFunction(() => window.explore?.failed);
    const response = await badResponse;
    assert.equal(response.status(), 200);
    assert.equal((await response.body()).length, 0);
    const failure = await failed.evaluate(() => window.explore.failed);
    assert.match(failure, /range received HTTP 200/);
    assert.ok(!(await failed.evaluate(() => window.explore.ready)));
    checkRangeOnly();
    console.log("ok an origin that stops honoring Range fails the open without accepting a whole response");
  } finally {
    await brokenOrigin.close();
  }

  const custom = await open("&vfs-profile=1&vfs-chunk=65536");
  assert.equal((await trace()).chunkSize, 65536);
  assert.match(custom.mode, /65536 B chunks/);
  await open("&vfs-profile=1&vfs-chunk=page");
  assert.equal((await trace()).chunkSize, pageSize);
  await open("&vfs-profile=1&vfs-chunk=12345");
  assert.equal((await trace()).chunkSize, chunk);
  const tiny = await open("&db=tiny.sqlite&vfs-profile=1");
  assert.equal(tiny.stats.totalFetchedBytes, pageSize);
  assert.deepEqual((await trace()).events.filter(e => e.type === "fetch").map(e => [e.start, e.end, e.status]),
    [[0, pageSize, 206]]);
  const full = await open("&load=full");
  assert.match(full.mode, /^whole file/);
  assert.equal(full.stats.totalFetchedBytes, size);
  console.log("ok chunk overrides, invalid-value default, one-page Range and explicit whole mode");
} finally {
  await browser.close();
  srv.kill();
  fs.rmSync(tmp, { recursive: true, force: true });
}
