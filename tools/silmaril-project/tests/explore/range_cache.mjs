// Browser check of the explorer's lazy loading against a GitHub-Pages-like server
// (pages_server.py): the database opens lazily (not whole), only part of it is transferred,
// a reload of the same version reuses the browser's HTTP cache, and a new version of the
// database (another ETag) is never mixed with cached pages of the old one.
//
//   node range_cache.mjs SITE_DIR   (SITE_DIR holds index.html and project.sqlite)
//
// Needs playwright-core and a Chromium (PLAYWRIGHT_CORE, CHROME); it starts the server itself.
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";

const site = path.resolve(process.argv[2]);
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const chrome = process.env.CHROME || "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
const log = path.join(os.tmpdir(), `pages-log-${process.pid}.jsonl`);
fs.writeFileSync(log, "");
const port = 8766 + (process.pid % 500);
const srv = spawn("python3", ["-I", new URL("./pages_server.py", import.meta.url).pathname,
  "--root", site, "--port", String(port), "--log", log], { stdio: "inherit" });
await new Promise((r) => setTimeout(r, 800));
const fail = (m) => { console.error("FAIL: " + m); srv.kill(); process.exit(1); };
const entries = () => fs.readFileSync(log, "utf8").trim().split("\n").filter(Boolean).map(JSON.parse)
  .filter((e) => e.path.endsWith(".sqlite"));
const dbSize = fs.statSync(path.join(site, "project.sqlite")).size;

const browser = await pw.chromium.launch({ executablePath: chrome });
const ctx = await browser.newContext();
const page = await ctx.newPage();
let nav = 0;
async function open(hash, query) {
  // a new query each time, so that every call is a real page load (not a same-document hash change)
  await page.goto(`http://127.0.0.1:${port}/index.html?nav=${++nav}${query || ""}${hash || "#/summary"}`);
  await page.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  return page.evaluate(() => ({ mode: window.explore.mode, stats: window.explore.stats }));
}

// 1. lazy, partial
const a = await open("#/summary");
if (!/^lazy/.test(a.mode)) fail("not lazy: " + a.mode);
const first = entries().filter((e) => e.range && e.query.includes("part="));
const firstBytes = first.reduce((s, e) => s + e.bytes, 0);
if (firstBytes >= dbSize) fail(`read ${firstBytes} of ${dbSize} bytes on first load`);
console.log(`first load: ${a.mode}; ${first.length} range requests, ${firstBytes} of ${dbSize} bytes`);

// 2. same version, reload: the browser's HTTP cache serves the pages again
fs.writeFileSync(log, "");
const b = await open("#/summary");
const second = entries().filter((e) => e.range && e.query.includes("part="));
const secondBytes = second.reduce((s, e) => s + e.bytes, 0);
console.log(`reload mode: ${b.mode}`); console.log(`reload: ${second.length} range requests reached the server, ${secondBytes} bytes`);
if (secondBytes >= firstBytes) fail("the reload did not reuse cached pages");

// 3. a new version (another mtime, so another ETag): new URLs, nothing mixed
const dbPath = path.join(site, "project.sqlite");
const later = new Date(Date.now() + 120000);
fs.utimesSync(dbPath, later, later);
fs.writeFileSync(log, "");
const c = await open("#/summary");
const third = entries().filter((e) => e.range && e.query.includes("part="));
const tags = new Set(third.map((e) => new URLSearchParams(e.query).get("v")));
if (c.mode === b.mode) fail("the version tag did not change with the ETag");
if (!third.length) fail("a new version was served from the cache of the old one");
console.log(`new version: ${c.mode}; ${third.length} range requests, tags ${[...tags].join(",")}`);

// 4. ?load=full: an honest whole download, checked against the page's SHA-256
const d = await open("#/summary", "&load=full");
console.log(`load=full: ${d.mode}`);
if (!/^whole file/.test(d.mode)) fail("load=full did not download the whole file");

await browser.close(); srv.kill();
console.log("ok");
