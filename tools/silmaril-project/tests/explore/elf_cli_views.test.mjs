// Unit tests of the ELF and CLI views (src/project/explore/views/{elf,cli}.js), without a browser:
// the two files run in a sandbox with a stub `registerView`, `fetch` answering small fixtures and a
// minimal `document`, and their views render to HTML. They run in pull-request CI (ci-project), so
// a change to the views alone is checked before merge; the browser tests (elf.mjs, cli.mjs) run on
// the built site after merge.
//
//   node --test tools/silmaril-project/tests/explore/elf_cli_views.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const views = path.join(here, "../../src/project/explore/views");

const thm = (decl, extra = {}) => ({ decl, short: decl.split(".").pop(), kind: "part", part: null, label: decl,
  windows: [], axioms: ["propext", "Classical.choice", "Quot.sound"], kernelOnly: true, status: "checked",
  module: "M.Thms", file: "M/Thms.lean", line: 1, statement: null, ...extra });

const elfFile = {
  schema: "silmaril.elf-pages.v1", slug: "x", title: "X", path: "x.so", size: 64, sha256: "00",
  provenance: [], module: "M", bytesModule: "M.Bytes",
  header: { class: "ELF64", data: "little-endian", osabi: 0, abiversion: 0, type: "DYN", machine: "x86-64", machineCode: 62,
    version: 1, entry: 0, phoff: 64, shoff: 0, flags: 0, ehsize: 64, phentsize: 56, phnum: 0, shentsize: 64, shnum: 0, shstrndx: 0, theorem: "M.header" },
  segments: [], sections: [], loader: { interp: null, needed: [], soname: null, runpath: null, dynamic: [], theorem: "M.loader" },
  symbols: [],
  functions: [
    { table: "dynsym", sec: 3, idx: 1, name: "f_known", version: "@@V_1", type: "FUNC", bind: "GLOBAL", visibility: 0, shndx: 9,
      value: 4096, size: 16, defined: true, ifunc: false, extent: "known (st_value, st_size)", offset: 4096, segment: 1, segmentFlags: "R-X",
      section: ".text", aliases: ["f_alias"], overlaps: [], theorem: "M.sym_3_1", contracts: [] },
    { table: "dynsym", sec: 3, idx: 2, name: "f_zero", version: null, type: "FUNC", bind: "GLOBAL", visibility: 0, shndx: 9,
      value: 8192, size: 0, defined: true, ifunc: false, extent: "unknown (st_size = 0)", offset: 8192, segment: 1, segmentFlags: "R-X",
      section: ".text", aliases: [], overlaps: [], theorem: "M.sym_3_2", contracts: [] },
    { table: "dynsym", sec: 3, idx: 3, name: "f_res", version: null, type: "IFUNC", bind: "GLOBAL", visibility: 0, shndx: 9,
      value: 8300, size: 8, defined: true, ifunc: true, extent: "known (st_value, st_size)", offset: 8300, segment: 1, segmentFlags: "R-X",
      section: ".text", aliases: [], overlaps: [], theorem: "M.sym_3_3", contracts: [] },
    { table: "dynsym", sec: 3, idx: 4, name: "f_proved", version: null, type: "FUNC", bind: "GLOBAL", visibility: 0, shndx: 9,
      value: 9000, size: 4, defined: true, ifunc: false, extent: "known (st_value, st_size)", offset: 9000, segment: 1, segmentFlags: "R-X",
      section: ".text", aliases: [], overlaps: [], theorem: "M.sym_3_4", contracts: ["M.f_contract"] },
    { table: "dynsym", sec: 3, idx: 5, name: "imp", version: "@G_2", type: "FUNC", bind: "GLOBAL", visibility: 0, shndx: 0,
      value: 0, size: 0, defined: false, ifunc: false, extent: "import (undefined here)", offset: null, segment: null, segmentFlags: null,
      section: null, aliases: [], overlaps: [], theorem: "M.sym_3_5", contracts: [] }],
  theorems: [1, 2, 3, 4, 5].map((i) => thm(`M.sym_3_${i}`, { kind: "symbol" }))
    .concat([thm("M.f_contract", { kind: "contract", statement: "And (CodeAt F 9000 code) (Total …)" }), thm("M.header"), thm("M.loader")]),
  coverage: [[0, 64, "decoded"]], coverageSummary: { decoded: 64, zeros: 0, raw: 0, unknown: 0 }, unsupported: [],
  disassembly: { file: "dis/x.json" },
};
const dis = { tool: "GNU objdump 2.44", command: "objdump -d -w -z x.so", listing: "x.objdump", unverified: true, rows: 1,
  chunks: [["dis/x/0.json", 4096, 4096, 1]], sections: [".text"] };
const disRows = [[4096, 4096, "c3", "ret", ".text", "f_known"]];
const edge = (decl, role, status, kind = "theorem", association = "n/a") => ({ decl, role, status, kind, note: "", axioms: [], module: "M", file: "M.lean", line: 1, statement: "s", association, about: [] });
const cli = {
  schema: "silmaril.cli-pages.v1",
  io: [
    { id: "a", title: "A", binary: "a", elfSlug: "x", sha256: "00", level: "L1", input: [["stdin", "any"]], output: [["stdout", "hi"], ["exit", "0"]],
      model: [["libc", "contracts (trusted)"]], limits: [],
      edges: [edge("M.a_proof", "proves the row", "proved", "theorem", "checked"), edge("M.Task.a", "open obligation", "parametrised statement, no instance proved here", "statement (parametrised)"),
        edge("M.Task.b", "open obligation", "statement, not proved here", "statement"), edge("M.spec", "specification", "specification", "statement (parametrised)"),
        edge("M.Shape", "shape (uninstantiated)", "uninstantiated shape", "statement (parametrised)")] },
    { id: "b", title: "B", binary: "b", elfSlug: null, sha256: "00", level: "—", input: [], output: [], model: [], limits: ["nothing proved"],
      edges: [edge("M.spec", "specification", "specification", "statement (parametrised)")] },
    { id: "c", title: "C", binary: "c", elfSlug: null, sha256: "00", level: "L1", input: [], output: [], model: [], limits: [],
      edges: [edge("M.unrelated_true_theorem", "proves", "proved", "theorem", "curated")] }],
  specs: [
    { id: "s1", title: "S1", kind: "args grammar", level: "L3", implementation: [["tool", "tools/s1"]], notes: [],
      edges: [edge("M.tool", "specification", "specification", "definition"), edge("M.main_refines", "refinement (by construction)", "proved", "theorem", "checked")] },
    { id: "s3", title: "S3", kind: "sentence", level: "L1", implementation: [["ELF", "c"]], notes: [],
      edges: [edge("M.spec3", "specification", "specification", "definition"), edge("M.curated_refines", "refinement proof", "proved", "theorem", "curated")] },
    { id: "s2", title: "S2", kind: "args grammar", level: "L3", implementation: [["tool", "tools/s2"]], notes: [],
      edges: [edge("M.tool2", "specification", "specification", "definition"), edge("M.tool2_wf", "proves", "proved")] }],
};
const fixtures = { "elf/f/x.json": elfFile, "elf/dis/x.json": dis, "elf/dis/x/0.json": disRows, "elf/cli.json": cli,
  "elf/index.json": { files: [{ slug: "x", title: "X", path: "x.so", size: 64, sha256: "00", type: "DYN", machine: "x86-64", sections: 0, segments: 0, theorems: 8, functions: 5, kernelOnly: true, coverageSummary: elfFile.coverageSummary }] } };

function load() {
  const registered = new Map();
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
  const ctx = vm.createContext({
    registerView: (v) => registered.set(v.id, v), esc, repoFile: () => null, console,
    $: () => null, location: { hash: "" }, history: { replaceState() {} },
    document: { getElementById: () => null, createElement: () => ({}), head: { appendChild() {} }, querySelectorAll: () => [] },
    fetch: async (url) => {
      const key = decodeURIComponent(url);
      if (!(key in fixtures)) return { ok: false, status: 404 };
      return { ok: true, status: 200, json: async () => fixtures[key] };
    },
  });
  for (const f of ["elf.js", "cli.js"]) vm.runInContext(fs.readFileSync(path.join(views, f), "utf8"), ctx, { filename: f });
  return registered;
}
const html = async (v, arg) => { const r = await v.render(arg, {}); return typeof r === "string" ? r : r.html; };
const rowOf = (h, attr) => h.match(new RegExp(`<tr[^>]*${attr}[^>]*>([\\s\\S]*?)</tr>`))?.[1] || "";

test("the views register their routes once", () => {
  const v = load();
  for (const id of ["elf", "elf-file", "elf-bytes", "elf-disasm", "elf-funcs", "cli", "cli-specs"]) assert.ok(v.has(id), id);
  assert.equal(v.get("cli-specs").tab, "cli");
  assert.equal(v.get("elf-funcs").tab, "elf");
});

test("function table: what a row is not, unknown extents, resolvers, imports, contracts", async () => {
  const v = load();
  const h = await html(v.get("elf-funcs"), "x");
  assert.match(h, /not a recovered function/);
  assert.match(h, /System V ABI/);
  assert.match(h, /1<\/b> with a contract theorem/);
  assert.match(h, /1 imports/);
  assert.match(h, /1 with unknown extent/);
});

test("disassembly keeps its UNVERIFIED warning", async () => {
  const v = load();
  const h = await html(v.get("elf-disasm"), "x/0x1000");
  assert.match(h, /UNVERIFIED/);
  assert.match(h, /elf-warn sticky/);
  assert.match(h, /ret/);
});

test("CLI I/O: verdicts follow the declarations, open obligations are never proved", async () => {
  const v = load();
  const h = await html(v.get("cli"), "");
  const a = rowOf(h, 'id="cli-io-a"'), b = rowOf(h, 'id="cli-io-b"');
  assert.match(a, /verified under the stated model/);
  assert.match(a, /2 open obligations/);
  assert.match(b, /no verified input\/output pair/);
  // a proved theorem not checked to be about the record gives no verdict
  assert.match(rowOf(h, 'id="cli-io-c"'), /no verified input\/output pair/);
  assert.match(h, /curated reference \(association not checked\)/);
  // the uninstantiated shape is not an open obligation
  assert.doesNotMatch(a, /3 open obligations/);
  assert.match(h, /data-role="shape \(uninstantiated\)"[\s\S]*?uninstantiated shape/);
  for (const m of h.matchAll(/<tr data-role="open obligation">([\s\S]*?)<\/tr>/g)) {
    assert.match(m[1], /st-bad/);
    assert.doesNotMatch(m[1], /prov-lean/);
  }
});

test("CLI specs: a specification without a refinement proof shows none", async () => {
  const v = load();
  const h = await html(v.get("cli-specs"), "");
  assert.match(rowOf(h, 'id="cli-spec-s1"'), /main_refines/);
  assert.match(rowOf(h, 'id="cli-spec-s2"'), /<td><span class="muted">none<\/span><\/td>/);
  // a curated refinement proof is not shown as a refinement
  assert.match(rowOf(h, 'id="cli-spec-s3"'), /<td><span class="muted">none<\/span><\/td>/);
});
