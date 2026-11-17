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
    { id: "i32:900", file: "i32", line: 900, type: "assert_malformed", status: "unsupported", reason: "assert_malformed on text (no shape)" },
    { id: "i32:950", file: "i32", line: 950, type: "assert_invalid", status: "proved", expected: ["invalid"], module_type: "binary",
      wasm_sha256: "0123456789abcdef0123", problem: "silmaril.wasm_wast.i32.l950", shape: "silmaril.shapes.wasm.wast.validator_rejects",
      strength: "tool", checker: "validatorRejectsB" },
    { id: "address:104", file: "address", line: 104, type: "assert_return", status: "undetermined", reason: "kernel: data",
      invoke: "8u_good1", args: ["i32:0"], expected: ["i32:97"], observed: "values i32:97" },
    { id: "f32:42", file: "f32", line: 42, type: "assert_return", status: "proved", invoke: "add", args: ["f32:2139095040", "f32:4286578688"],
      expected: ["f32:nan:canonical"], allowed: ["f32:nan:canonical"], observed: "nan:canonical f32", profile: "Profile.spec",
      problem: "silmaril.wasm_wast.f32.l42", shape: "silmaril.shapes.wasm.wast.returns_allowed_all", strength: "all", checker: "scriptSK",
      claims: [{ kind: "all", shape: "silmaril.shapes.wasm.wast.returns_allowed_all", problem: "silmaril.wasm_wast.f32.l42" },
        { kind: "terminates", shape: "silmaril.shapes.wasm.wast.terminates_all", problem: "silmaril.wasm_wast.f32.l42_terminates" }] },
  ],
};
const oracle = { results: [{ id: "i32:37", oracle: "pass" }, { id: "i32:64", oracle: "pass" }, { id: "address:104", oracle: "fail" }] };

test("counts by status, by file and by reason", () => {
  const s = W.summarize(fixture, oracle);
  assert.equal(s.total, 6);
  assert.deepEqual(s.byStatus, { proved: 4, unsupported: 1, undetermined: 1 });
  assert.equal(s.byFile.i32.total, 4);
  assert.equal(s.byFile.address.undetermined, 1);
  assert.deepEqual(s.reasons, [["undetermined: kernel: data", 1], ["unsupported: assert_malformed on text (no shape)", 1]]);
  assert.deepEqual(s.byClaim, { "semantic: Core reduction": 1, "tool-level rejection": 1, "?": 1,
    "semantic: Core reduction under Profile.spec, every normal form": 1 });
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
  assert.equal(rs.length, 6);
  assert.equal(rs[0].input, "add(i32:1, i32:1)");
  assert.equal(rs[0].expected, "i32:2");
  assert.match(rs[0].strength, /every host-free normal form/);
  assert.match(rs[0].strength, /no host-free run diverges/);
  assert.match(rs[1].strength, /trap/);
  assert.equal(rs[2].problem, null);
  assert.equal(rs[4].oracle, "fail");
  assert.equal(W.rows(fixture, oracle, { status: "proved" }).length, 4);
  assert.equal(W.rows(fixture, oracle, { file: "address" }).length, 1);
});

test("rejection rows are labelled tool-level and do not claim spec invalidity", () => {
  const r = W.rows(fixture, oracle)[3];
  assert.equal(r.claim, "tool-level rejection");
  assert.match(r.strength, /validator rejects/);
  assert.match(r.strength, /Not a claim that the module is invalid in the specification/);
  assert.match(r.input, /binary SHA-256 0123456789ab/);
  assert.equal(W.rows(fixture, oracle)[0].claim, "semantic: Core reduction");
  assert.match(W.STRENGTH["silmaril.shapes.wasm.wast.decoder_rejects"], /not a claim that the bytes are malformed/);
});

test("rows under Profile.spec show the claim kinds, the allowed set and the profile", () => {
  const r = W.rows(fixture, oracle)[5];
  assert.equal(r.profile, "Profile.spec");
  assert.equal(r.allowed, "f32:nan:canonical");
  assert.deepEqual(r.claims.map((x) => x.kind), ["all", "terminates"]);
  assert.match(r.claims[0].kindText, /every normal form/);
  assert.match(r.claims[1].kindText, /terminates/);
  assert.match(r.claim, /Profile\.spec, every normal form/);
  assert.match(W.STRENGTH[r.claims[1].shape], /no host-free run is infinite/);
  assert.match(W.STRENGTH["silmaril.shapes.wasm.wast.returns_allowed_exists"], /existence only/);
  assert.equal(W.rows(fixture, oracle)[0].claims.length, 0);
});

test("rows of a linked script show their context and the host model", () => {
  const linked = { commands: [
    { id: "linking:17", file: "linking", line: 17, type: "assert_return", status: "proved", script: "linked", invoke: "call", args: [],
      on: "$Mf", expected: ["i32:2"], problem: "silmaril.wasm_wast.linking.l17", shape: "silmaril.shapes.wasm.wast.host.returns_only",
      strength: "only", checker: "scriptHK", host: "spectest = the typed host Spectest.host", printed: ["i32:13"],
      observation: "results; the host-call log (Spectest.printed) is determined by ScriptAt.unique but not claimed",
      context: { registered: ["Mf", "spectest"], named: ["Mf"], current: "$Nf", current_imports: ["Mf.call"], host: "spectest = Spectest.host" },
      claims: [{ kind: "only", shape: "silmaril.shapes.wasm.wast.host.returns_only", problem: "silmaril.wasm_wast.linking.l17" }] },
    { id: "linking:28", file: "linking", line: 28, type: "assert_unlinkable", status: "proved", script: "linked", expected: ["unlinkable"],
      module_type: "binary", wasm_sha256: "abcdef0123456789abcd", problem: "silmaril.wasm_wast.linking.l28",
      shape: "silmaril.shapes.wasm.wast.host.unlinkable", strength: "link", checker: "scriptHK",
      context: { registered: ["spectest"], named: [], current: null, current_imports: [], module_imports: ["spectest.unknown"] } },
    { id: "linking:7", file: "linking", line: 7, type: "register", status: "context", script: "linked", register: { as: "Mf", module: "$Mf" },
      reason: "register: part of the script context of later rows (no claim)" },
  ] };
  const rs = W.rows(linked, null);
  assert.equal(rs[0].input, "$Mf.call()");
  assert.ok(rs[0].linked);
  assert.match(rs[0].context, /registered: Mf, spectest; named: \$Mf; current: \$Nf \(imports: Mf\.call\)/);
  assert.match(rs[0].context, /host: spectest = Spectest\.host/);
  assert.match(rs[0].strength, /linked script prefix/);
  assert.match(rs[0].strength, /typed spectest host/);
  assert.equal(rs[0].printed, "i32:13");
  assert.match(rs[0].observation, /host-call log/);
  assert.equal(rs[0].claim, "semantic: Core reduction");
  assert.match(rs[1].claim, /linking/);
  assert.match(rs[1].strength, /ExternAddrOk/);
  assert.match(rs[1].context, /this module imports: spectest\.unknown/);
  assert.equal(rs[2].input, 'register "Mf" $Mf');
  assert.equal(W.summarize(linked, null).byStatus.context, 1);
  assert.ok(W.STATUS_ORDER.includes("context"));
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
    assert.ok(W.CLAIM[c.strength], c.id);
    if ((c.type === "assert_return" || c.type === "assert_trap") && c.strength === "all") {
      // Under Profile.spec: every normal form, and termination of every run, as two problems.
      assert.equal(c.checker, "scriptSK", c.id);
      assert.equal(c.profile, "Profile.spec", c.id);
      assert.deepEqual(c.claims.map((x) => x.kind), ["all", "terminates"], c.id);
      assert.equal(c.claims[1].problem, c.problem + "_terminates", c.id);
      for (const x of c.claims) assert.ok(W.STRENGTH[x.shape], x.shape);
    } else if (c.script === "linked" && !c.wasm_sha256 || c.type === "assert_unlinkable" || c.type === "assert_uninstantiable") {
      // A row of a linked script: one kernel evaluation of scriptHK per file, against the typed
      // spectest host, with the script context of the row.
      assert.equal(c.checker, "scriptHK", c.id);
      assert.match(c.shape, /^silmaril\.shapes\.wasm\.wast\.host\./, c.id);
      assert.equal(c.strength, c.type === "assert_unlinkable" ? "link" : "only", c.id);
      assert.match(c.host, /typed host Spectest\.host/, c.id);
      assert.match(c.observation, /host-call log/, c.id);
      assert.ok(c.context && Array.isArray(c.context.registered) && c.context.registered.includes("spectest"), c.id);
    } else if (c.type === "assert_return" || c.type === "assert_trap") {
      assert.equal(c.strength, "only", c.id);
      assert.ok(["scriptK", "scriptKM"].includes(c.checker), c.id);
    } else {
      // assert_invalid, assert_malformed: tool-level, by the validator (decoder) checker.
      assert.equal(c.strength, "tool", c.id);
      assert.ok(["validatorRejectsB", "decode?"].includes(c.checker), c.id);
    }
  }
  // address.wast's modules have data segments: their rows are checked on KMem stores.
  for (const c of report.commands.filter((c) => c.status === "proved" && c.file === "address" && c.type.startsWith("assert_r")))
    assert.equal(c.checker, "scriptKM", c.id);
  for (const c of report.commands.filter((c) => c.status === "unsupported" || c.status === "undetermined")) assert.ok(c.reason, c.id);
  if (orc) assert.equal(s.agreeProved, s.proved);
});
