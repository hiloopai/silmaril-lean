// Unit tests of the assembly view (src/project/explore/views/asm.js) and its links from the ELF
// tab (views/elf.js), without a browser: the files run in a sandbox with a stub `registerView`,
// `fetch` answering a small fixture in the `silmaril.elf.asm/1` form and a minimal `document`.
// The browser test on the built site is asm.mjs.
//
//   node --test tools/silmaril-project/tests/explore/elf_asm_view.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const views = path.join(here, "../../src/project/explore/views");

const STD = ["propext", "Classical.choice", "Quot.sound"];
const ev = (kind, decl, extra = {}) => ({ kind, decl, model: null, axioms: STD, hypotheses: [], ...extra });
const arch = { id: "elf64-le/em62", machine: 62, class: 2, data: 1, osabi: 0 };
const MA = "x86-64/M.A.decode", MB = "x86-64/M.B.decode";
// f: bytes in a segment, decoded by model A (not by B), a decoded reference grounded, a contract
// under one premise; no symbol theorem; the display lines name an instruction the decoders do not.
const f = {
  decl: "Ex.f", file: "Ex.F", name: "f", arch, abiRef: "sysv64", symbol: { table: "symtab", index: 3 },
  extent: { vaddr: "0x401000", size: 7, fileOff: "0x1000", segment: 1, shndx: 1 },
  bytesHex: "89d2e9f9ffffff",
  lines: [{ off: 0, len: 2, addr: "0x401000", text: "mov %edx,%edx", label: "f" }, { off: 2, len: 5, addr: "0x401002", text: "jmp 401000 <DISPLAYONLY>", label: null }],
  refs: [{ off: 2, target: "0x401000", symbol: "f", kind: 0, addend: "0", origin: { kind: "decoded" } },
    { off: 2, target: "0x401000", symbol: "f", kind: 0, addend: "0", origin: { kind: "display" } }],
  decodings: [{ model: MA, decl: "Ex.fDecoding", insns: [{ off: 0, len: 2, addr: "0x401000", render: "movA" }, { off: 2, len: 5, addr: "0x401002", render: "jmpA" }] }],
  evidence: [ev("arch", "Ex.f_arch"), ev("bytes", "Ex.f_bytes"), ev("decode", "Ex.f_decodes", { model: MA }),
    ev("noDecode", "Ex.f_not_b", { model: MB }), ev("refs", "Ex.f_refs", { model: MA }),
    ev("contract", "Ex.f_contract", { model: "M.A.isa", hypotheses: ["h : Task.premise"] }), ev("lineTiles", "Ex.f_tiles", { axioms: [] })],
};
// g: the same name in the same file, another architecture: no evidence but its negation.
const g = { ...f, decl: "Ex.g", arch: { ...arch, id: "elf64-le/em4660", machine: 4660 }, refs: [], decodings: [], abiRef: null,
  evidence: [ev("bytes", "Ex.g_bytes"), ev("notArch", "Ex.g_not_arch")] };
// r: a relocatable object's function: unknown segment, a relocation reference, nothing else; an
// ABI conformance row through the extension point.
const r = { decl: "Ex.r", file: "Ex.R", name: "r", arch, abiRef: "sysv64", symbol: null,
  extent: { vaddr: "0x0", size: 1, fileOff: null, segment: null, shndx: null }, bytesHex: "c3",
  lines: [{ off: 0, len: 1, addr: "0x0", text: "ret", label: "r" }],
  refs: [{ off: 0, target: null, symbol: "s", kind: 4, addend: "-4", origin: { kind: "reloc", selector: "section 1", index: 0 } }],
  decodings: [], evidence: [ev("sectionBytes", "Ex.r_sec", { axioms: ["propext", "Ex.myAxiom"] })],
  abi: [{ problemId: "abi/r", decl: "Ex.r_abi", abiId: "sysv64", mode: "call", frame: 0, status: "open",
    data: [{ vaddr: "0x2000", size: 2, bytesHex: "abcd", mapped: "Ex.r_data_mapped", untouched: "Ex.r_data_untouched" },
      { vaddr: "0x3000", size: 4, readOnly: true }, { vaddr: "0x4000", size: 2, bytesHex: "abcd", mapped: "Ex.r_m" }] }] };
const asm = { schema: "silmaril.elf.asm/1",
  files: [{ decl: "Ex.F", path: "x.so", sha256: "00" }, { decl: "Ex.R", path: "dir/r.o", sha256: "11" }],
  functions: [f, g, r] };
const decls = { schema: "silmaril.elf-pages.asm-decls.v1", decls: { "Ex.f_arch": { module: "Ex.Thms", file: "Ex/Thms.lean", line: 12, kind: "theorem" } } };
const index = { files: [{ slug: "x", title: "X", path: "x.so" }] };

function load(fixtures, extra = {}) {
  const registered = new Map();
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
  const ctx = vm.createContext({
    registerView: (v) => registered.set(v.id, v), esc, repoFile: (p) => ({ path: p, blob: "https://example.invalid/blob/" + p }), console,
    $: extra.$ || (() => null), location: { hash: "" }, history: { replaceState() {} },
    document: { getElementById: () => null, createElement: () => ({}), head: { appendChild() {} }, querySelectorAll: () => [] },
    fetch: async (url) => {
      const key = decodeURIComponent(url);
      if (!(key in fixtures)) return { ok: false, status: 404 };
      return { ok: true, status: 200, json: async () => structuredClone(fixtures[key]) };
    },
  });
  for (const file of ["elf.js", "asm.js"]) vm.runInContext(fs.readFileSync(path.join(views, file), "utf8"), ctx, { filename: file });
  return registered;
}
const FIX = { "elf/asm.json": asm, "elf/asm-decls.json": decls, "elf/index.json": index };
const html = async (v, arg) => { const x = await v.render(arg, {}); return typeof x === "string" ? x : x.html; };
const escapeRegex = (s) => String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const tbody = (h, dim, model) => h.match(new RegExp(`<tbody data-dim="${dim}"${model ? ` data-model="${escapeRegex(model)}"` : ""}[^>]*>([\\s\\S]*?)</tbody>`))?.[0] || "";
const statusOf = (h, dim, model) => tbody(h, dim, model).match(/data-status="([^"]*)"/)?.[1];

test("the assembly view registers one route in the navigation", () => {
  const v = load(FIX);
  assert.ok(v.has("asm"));
  assert.equal(typeof v.get("asm").nav, "number");
});

test("index: one row per record, a column per dimension, no overall status", async () => {
  const h = await html(load(FIX).get("asm"), "");
  assert.equal((h.match(/<tr data-decl=/g) || []).length, 3);
  for (const d of ["arch", "bytes", "sectionBytes", "code", "symbol", "decode", "lines", "refs", "contract", "abi"]) assert.match(h, new RegExp(`data-dim="${d}"`));
  assert.doesNotMatch(h, /\bverified\b/i);
  // the two records named f link to themselves, by declaration
  assert.match(h, /href="#\/asm\/x\/f\/Ex\.f"/);
  assert.match(h, /href="#\/asm\/x\/f\/Ex\.g"/);
  assert.match(h, /href="#\/asm\/r\.o\/r"/);
});

test("one function: evidence rows are separate, missing dimensions show none", async () => {
  const h = await html(load(FIX).get("asm"), "x/f/Ex.f");
  assert.equal(statusOf(h, "arch"), "holds");
  assert.equal(statusOf(h, "bytes"), "holds");
  assert.equal(statusOf(h, "sectionBytes"), "none");
  assert.equal(statusOf(h, "code"), "none");
  assert.equal(statusOf(h, "symbol"), "none");
  assert.match(tbody(h, "symbol"), /<span class="muted">none<\/span>/);
  assert.equal(statusOf(h, "decode", MA), "holds");
  assert.equal(statusOf(h, "decode", MB), "does not hold");
  assert.equal(statusOf(h, "lines"), "holds");
  assert.equal(statusOf(h, "refs"), "holds");
  // a contract with a premise is not shown as unconditional, and its premise is listed
  assert.equal(statusOf(h, "contract"), "holds under premises");
  assert.match(tbody(h, "contract"), /h : Task\.premise/);
  assert.match(tbody(h, "contract"), /M\.A\.isa/);
  // ABI conformance: its own row, empty here
  assert.equal(statusOf(h, "abi"), "none");
  assert.match(tbody(h, "abi"), /no conformance row/);
  // each row lists only its own declarations
  assert.doesNotMatch(tbody(h, "arch"), /f_bytes|f_decodes/);
  assert.doesNotMatch(tbody(h, "bytes"), /f_arch/);
  // the declaration map gives a source link
  assert.match(tbody(h, "arch"), /href="https:\/\/example\.invalid\/blob\/Ex\/Thms\.lean#L12"/);
  // axioms and premises are listed
  assert.match(tbody(h, "arch"), /Classical\.choice/);
  assert.match(tbody(h, "arch"), /none \(unconditional\)/);
  assert.doesNotMatch(h, /\bverified\b/i);
});

test("display lines are labelled unchecked; abiRef is metadata; decodings are per model", async () => {
  const h = await html(load(FIX).get("asm"), "x/f/Ex.f");
  assert.match(h, /display only, not checked/);
  assert.match(h, /DISPLAYONLY/);
  assert.match(h, /sysv64<\/code> <span class="asm-meta"[^>]*>metadata \(not evidence\)<\/span>/);
  const heads = h.match(/<th class="model" data-model="[^"]*">/g) || [];
  assert.deepEqual(heads, [`<th class="model" data-model="${MA}">`]);
  assert.match(h, /decoder accepted<\/span> <code title="Ex\.f_decodes">/);
  // exact bytes with offsets
  assert.match(h, /\+0x0<\/td><td class="o">0x401000<\/td><td class="o">0x1000<\/td><td>89 d2 e9 f9 ff ff ff<\/td>/);
  // references: origin and grounding, a listing reference never grounded
  assert.match(h, /<tr data-origin="decoded">[\s\S]*?grounded<\/span> by <code title="Ex\.f_refs">/);
  assert.match(h, /<tr data-origin="display">[\s\S]*?not grounded: a listing reference/);
  // links back to the ELF tab and to the unverified objdump view
  assert.match(h, /href="#\/elf-file\/x"/);
  assert.match(h, /href="#\/elf-disasm\/x\/0x401000"/);
});

test("another architecture under the same name: a chooser, then its own rows", async () => {
  const v = load(FIX).get("asm");
  const c = await html(v, "x/f");
  assert.match(c, /2 records of this file have this name/);
  const h = await html(v, "x/f/Ex.g");
  assert.equal(statusOf(h, "arch"), "does not hold");
  assert.equal(statusOf(h, "bytes"), "holds");
  assert.equal(statusOf(h, "decode"), "none");
  assert.match(h, /No decoding by any instruction model/);
  assert.match(h, /abiRef<\/dt><dd><span class="muted">unknown<\/span>/);
});

test("unknown extent fields show unknown; extra axioms are flagged; ABI rows come from the extension point", async () => {
  const h = await html(load(FIX).get("asm"), "r.o/r");
  assert.match(h, /segment<\/dt><dd><span class="muted">unknown<\/span>/);
  assert.match(h, /file offset<\/dt><dd><span class="muted">unknown<\/span>/);
  assert.match(h, /section<\/dt><dd><span class="muted">unknown<\/span>/);
  assert.match(h, /this file has no page in the ELF tab/);
  assert.equal(statusOf(h, "sectionBytes"), "holds");
  assert.match(tbody(h, "sectionBytes"), /st-bad" title="not a standard axiom">Ex\.myAxiom/);
  assert.equal(statusOf(h, "bytes"), "none");
  assert.equal(statusOf(h, "abi"), "rows");
  assert.match(tbody(h, "abi"), /abi\/r/);
  assert.match(h, /<tr data-origin="reloc">[\s\S]*?not grounded<\/span> <span class="muted">\(no RefsGrounded evidence\)/);
});

// The text a page shows, without tags or attributes (titles are not visible text).
const visible = (h) => h.replace(/<[^>]*>/g, " ");

test("decode rows: rejection is not classified; a model without a theorem is unknown", async () => {
  const v = load(FIX).get("asm");
  const h = await html(v, "x/f/Ex.f");
  const rej = visible(tbody(h, "decode", MB));
  assert.match(rej, /rejected \(¬ DecodesAs proved; no cause classified\)/);
  for (const d of [MA, MB]) assert.doesNotMatch(visible(tbody(h, "decode", d)), /\b(invalid|incomplete|unsupported)\b/);
  // the decoding's text is printer output; its evidence is the DecodesAs theorem named
  assert.match(h, /text: printer output, not evidence/);
  assert.match(h, /a line's source \(lean-decode or objdump\) is not itself evidence/);
  const g = await html(v, "x/f/Ex.g");
  assert.match(visible(tbody(g, "decode")), /none: unknown \(no DecodesAs theorem\)/);
});

test("extent fields name the dimension that grounds them, with its own status", async () => {
  const h = await html(load(FIX).get("asm"), "x/f/Ex.f");
  assert.match(h, /record field; grounded by <code>BytesAt<\/code>: <span class="prov prov-lean"[^>]*>holds/);
  // f has no SymbolOf theorem: its symbol field is a record field, grounded by nothing
  assert.match(h, /record field; grounded by <code>SymbolOf<\/code>: <span class="muted">none<\/span>/);
  assert.match(h, /segment flags are the file's program header/);
});

test("Code.data ranges count only with exact bytes, MappedAt and Untouched", async () => {
  const h = await html(load(FIX).get("asm"), "r.o/r");
  const abi = tbody(h, "abi");
  assert.equal((abi.match(/data-grounded="yes"/g) || []).length, 1);
  assert.equal((abi.match(/data-grounded="no"/g) || []).length, 2);
  assert.match(abi, /Ex\.r_data_mapped[\s\S]*?MappedAt[\s\S]*?Ex\.r_data_untouched[\s\S]*?Untouched/);
  assert.match(abi, /not grounded: not counted<\/span> <code>0x3000<\/code>, 4 B <span class="muted">\(read-only flag: metadata\)/);
});

test("without the data the view says where it comes from", async () => {
  const h = await html(load({}).get("asm"), "");
  assert.match(h, /assembly data is not available/);
  assert.match(h, /elf-pages/);
});

test("ELF function table links to assembly records by file path and name", async () => {
  const elfFile = {
    schema: "silmaril.elf-pages.v1", slug: "x", title: "X", path: "x.so", size: 64, sha256: "00", provenance: [], module: "M", bytesModule: "M.Bytes",
    header: { type: "EXEC", machine: "x86-64" }, segments: [], sections: [], symbols: [], coverage: [], coverageSummary: {}, unsupported: [],
    theorems: [{ decl: "M.s", short: "s", kind: "symbol", axioms: STD, kernelOnly: true, status: "checked", module: "M", file: "M.lean", line: 1, windows: [] }],
    functions: ["f", "h"].map((name, i) => ({ table: "symtab", sec: 3, idx: i, name, version: null, type: "FUNC", bind: "GLOBAL", shndx: 1, value: 4096, size: 7,
      defined: true, ifunc: false, extent: "known", offset: 4096, segment: 1, segmentFlags: "R-X", section: ".text", aliases: [], overlaps: [], theorem: "M.s", contracts: [] })),
    disassembly: {} };
  const els = {};
  const $ = (sel) => (els[sel] ||= { value: "", checked: sel === "#elf-fdef", innerHTML: "", textContent: "", addEventListener() {} });
  const v = load({ ...FIX, "elf/f/x.json": elfFile }, { $ });
  const out = await v.get("elf-funcs").render("x", {});
  assert.match(out.html, /1 of these names have <a href="#\/asm\/x">assembly records/);
  out.init();
  const table = els["#elf-ft"].innerHTML;
  assert.match(table, /<tr data-fn="f">[\s\S]*?href="#\/asm\/x\/f"[^>]*>assembly \(2 records\)<\/a>/);
  assert.doesNotMatch(table.match(/<tr data-fn="h">[\s\S]*?<\/tr>/)[0], /#\/asm\//);
});
