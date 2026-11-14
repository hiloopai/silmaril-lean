// The explorer's browser-side dominator computation (`dominators` in explore.html), on small
// graphs with known answers: a chain, a diamond, two entries (synthetic root), an unreachable
// node.   node dominators.mjs SITE_DIR   (SITE_DIR holds explore.html and project.sqlite)
import { spawn } from "node:child_process";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const srv = spawn("python3", ["-I", "/work/repo/tools/silmaril-project/tests/explore/pages_server.py", "--root", path.resolve(process.argv[2]), "--port", "8792", "--log", "/tmp/dom2.log"]);
await new Promise((r) => setTimeout(r, 800));
const b = await pw.chromium.launch({ executablePath: process.env.CHROME || "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" });
const p = await b.newPage();
await p.goto("http://127.0.0.1:8792/explore.html#/summary");
await p.waitForFunction(() => window.explore && window.explore.ready, null, { timeout: 60000 });
const r = await p.evaluate(() => {
  const f = (n, e, r) => { const x = dominators(n, e, r); return { idom: [...x.idom], reach: [...x.reachable], syn: x.synthetic }; };
  return [f(["a","b","c"], [["a","b"],["b","c"]], ["a"]),
          f(["a","b","c","d"], [["a","b"],["a","c"],["b","d"],["c","d"]], ["a"]),
          f(["x","y","z"], [["x","z"],["y","z"]], ["x","y"]),
          f(["a","b","u"], [["a","b"]], ["a"])];
});
const want = [
  { idom: [["a", null], ["b", "a"], ["c", "b"]], reach: ["a", "b", "c"], syn: false },
  { idom: [["a", null], ["b", "a"], ["c", "a"], ["d", "a"]], reach: ["a", "b", "c", "d"], syn: false },
  { idom: [["x", null], ["y", null], ["z", null]], reach: ["x", "y", "z"], syn: true },
  { idom: [["a", null], ["b", "a"]], reach: ["a", "b"], syn: false }];
const ok = JSON.stringify(r) === JSON.stringify(want);
console.log(ok ? "ok" : "FAIL: " + JSON.stringify(r));
await b.close(); srv.kill();
process.exit(ok ? 0 : 1);
