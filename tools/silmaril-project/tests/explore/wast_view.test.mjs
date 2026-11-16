// Unit tests of the explorer's WAST view model (src/project/explore/views/wast.js): counts by
// status and reason, oracle agreement, row filters and the claim strength of a proved row, on a
// small fixture and on the committed report (examples/wasm-wast/report.json, oracle.json).
//
//   node --test tools/silmaril-project/tests/explore/wast_view.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const W = createRequire(import.meta.url)(path.join(here, "../../src/project/explore/views/wast.js"));

const fixture = {
  commands: [
    { id: "i32:37", file: "i32", line: 37, type: "assert_return", status: "proved", invoke: "add", args: ["i32:1", "i32:1"],
      expected: ["i32:2"], observed: "values i32:2", problem: "silmaril.wasm_wast.i32.l37",
      shape: "silmaril.shapes.wasm.wast.returns_only", strength: "only" },
    { id: "i32:64", file: "i32", line: 64, type: "assert_trap", status: "proved", invoke: "div_s", args: ["i32:1", "i32:0"],
      expected: ["trap"], observed: "trap", problem: "silmaril.wasm_wast.i32.l64", shape: "silmaril.shapes.wasm.wast.traps_only" },
    { id: "i32:900", file: "i32", line: 900, type: "assert_invalid", status: "unsupported", reason: "assert_invalid (no shape)" },
    { id: "address:104", file: "address", line: 104, type: "assert_return", status: "undetermined", reason: "kernel: data",
      invoke: "8u_good1", args: ["i32:0"], expected: ["i32:97"], observed: "values i32:97" },
  ],
};
const oracle = { results: [{ id: "i32:37", oracle: "pass" }, { id: "i32:64", oracle: "pass" }, { id: "address:104", oracle: "fail" }] };

test("counts by status, by file and by reason", () => {
  const s = W.summarize(fixture, oracle);
  assert.equal(s.total, 4);
  assert.deepEqual(s.byStatus, { proved: 2, unsupported: 1, undetermined: 1 });
  assert.equal(s.byFile.i32.total, 3);
  assert.equal(s.byFile.address.undetermined, 1);
  assert.deepEqual(s.reasons, [["undetermined: kernel: data", 1], ["unsupported: assert_invalid (no shape)", 1]]);
});

test("oracle agreement counts only kernel-proved rows as agreeing", () => {
  const s = W.summarize(fixture, oracle);
  assert.equal(s.oracleRun, 3);
  assert.equal(s.agreeProved, 2);
  assert.equal(s.disagree, 1);
  assert.equal(W.summarize(fixture, null).oracleLoaded, false);
});

test("rows: inputs, expectation, claim strength and filters", () => {
  const rs = W.rows(fixture, oracle);
  assert.equal(rs.length, 4);
  assert.equal(rs[0].input, "add(i32:1, i32:1)");
  assert.equal(rs[0].expected, "i32:2");
  assert.match(rs[0].strength, /every host-free normal form/);
  assert.match(rs[0].strength, /no host-free run diverges/);
  assert.match(rs[1].strength, /trap/);
  assert.equal(rs[2].problem, null);
  assert.equal(rs[3].oracle, "fail");
  assert.equal(W.rows(fixture, oracle, { status: "proved" }).length, 2);
  assert.equal(W.rows(fixture, oracle, { file: "address" }).length, 1);
});

test("the committed report: every proved row names its problem and shape, and the oracle agrees", () => {
  const root = path.join(here, "../../../../examples/wasm-wast");
  const report = JSON.parse(fs.readFileSync(path.join(root, "report.json"), "utf8"));
  const orc = fs.existsSync(path.join(root, "oracle.json")) ? JSON.parse(fs.readFileSync(path.join(root, "oracle.json"), "utf8")) : null;
  const s = W.summarize(report, orc);
  assert.equal(s.total, report.counts.total);
  for (const [k, v] of Object.entries(report.counts)) if (k !== "total") assert.equal(s.byStatus[k], v, k);
  for (const c of report.commands.filter((c) => c.status === "proved")) {
    assert.match(c.problem, /^silmaril\.wasm_wast\.[a-z0-9_]+\.l[0-9]+$/);
    assert.ok(W.STRENGTH[c.shape], c.shape);
    assert.ok(["scriptK", "scriptKM"].includes(c.checker), c.id);
  }
  // address.wast's modules have data segments: their rows are checked on KMem stores.
  for (const c of report.commands.filter((c) => c.status === "proved" && c.file === "address")) assert.equal(c.checker, "scriptKM", c.id);
  for (const c of report.commands.filter((c) => c.status === "unsupported" || c.status === "undetermined")) assert.ok(c.reason, c.id);
  if (orc) assert.equal(s.agreeProved, s.proved);
});
