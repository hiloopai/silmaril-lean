// ---------- Assembly: functions, their exact bytes, decodings and evidence, dimension by dimension ----------
// A Compiler-Explorer-like view of assembly functions: the bytes of one function, the display
// listing beside each instruction model's decoding, its references and, for every dimension of
// evidence, the Lean declarations that state it (with their axioms and premises).
//
// Data: a source is one JSON file in the `silmaril.elf.asm/1` form (Silmaril.Elf.Asm.Export,
// docs/projects/elf-asm.md), plus an optional map of where its declarations are. The ELF source is
// elf/asm.json, the committed examples/elf-asm/samples.json that `elf-pages` copies unchanged (its
// evidence is read from theorem statements and checked by `elf-asm --check`), and
// elf/asm-decls.json (each named declaration's module and line, from the checked environment).
// Another source of the same form (another file format, another toolchain) is one more entry in
// ASM_SOURCES; the renderers below take a function record and never read the source's name.
//
// Routes: #/asm (every function), #/asm/<file>/<name> (one function; a chooser when several
// records of that file have the name), #/asm/<file>/<name>/<decl> (one record). <file> is the ELF
// tab's slug of the file when it has one, else the file's base name.
//
// What this view does not do: it never infers one dimension from another, never ranks a function
// and has no overall "verified" badge. A dimension with no evidence shows "none". `abiRef` is the
// function's ABI identifier, metadata only. ABI conformance is a separate row: the JSON has no
// conformance evidence yet, and the optional `abi` array of a function record ({problemId, decl,
// abiId, mode, frame, status}) is the extension point for it.
(() => {
  const ASM_SOURCES = [
    { id: "elf", schema: "silmaril.elf.asm/1", data: "elf/asm.json", decls: "elf/asm-decls.json", files: "elf/index.json",
      writer: "<code>elf-pages</code> (<code>make pages</code>) from <code>examples/elf-asm/samples.json</code>" },
  ];
  const SRC = ASM_SOURCES[0];
  const STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"];
  const enc = encodeURIComponent;

  const cache = new Map();
  function getJson(url, optional) {
    if (!cache.has(url)) cache.set(url, fetch(url).then((r) => {
      if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
      return r.json();
    }));
    const p = cache.get(url).catch((e) => { cache.delete(url); throw e; });
    return optional ? p.catch(() => null) : p;
  }

  // The functions of a source, with each record's file (path, ELF tab slug) and its route key.
  async function load(src) {
    const d = await getJson(src.data);
    if (d.schema !== src.schema) throw new Error(`${src.data}: schema ${d.schema}, expected ${src.schema}`);
    const [decls, ix] = await Promise.all([getJson(src.decls, true), getJson(src.files, true)]);
    const slugOf = new Map(((ix && ix.files) || []).map((f) => [f.path, f.slug]));
    const files = new Map(d.files.map((f) => [f.decl, { ...f, slug: slugOf.get(f.path) || null, key: slugOf.get(f.path) || f.path.split("/").pop() }]));
    const fns = d.functions.map((fn) => ({ ...fn, fileInfo: files.get(fn.file) || { decl: fn.file, path: null, sha256: null, slug: null, key: String(fn.file) } }));
    for (const fn of fns) {
      const same = fns.filter((g) => g.fileInfo.key === fn.fileInfo.key && g.name === fn.name);
      fn.route = `#/asm/${enc(fn.fileInfo.key)}/${enc(fn.name)}` + (same.length > 1 ? `/${enc(fn.decl)}` : "");
    }
    return { schema: d.schema, files, fns, decls: (decls && decls.decls) || {} };
  }

  if (typeof document !== "undefined" && document.getElementById && !document.getElementById("asm-style")) {
    const st = document.createElement("style");
    st.id = "asm-style";
    st.textContent = `
.asm-warn { border-left:4px solid #d9a400; background:#fff6dc; padding:6px 10px; margin:8px 0; max-width:1100px; }
.asm-meta { display:inline-block; padding:0 6px; border:1px dashed #9aa0a6; border-radius:3px; font-size:12px; color:#555; background:#f6f7f8; }
table.asm-hex td { border:0; padding:0 6px 0 0; } table.asm-hex td.o { color:var(--muted); }
table.asm-side td { border:0; border-bottom:1px solid #f0f2f4; padding:1px 10px 1px 0; white-space:pre; }
table.asm-side td.cont { color:#b0b6bc; } table.asm-side tr.lbl td { color:#a3157a; font-weight:600; padding-top:6px; }
table.asm-side th.disp, table.asm-side td.disp { background:#fffaf0; } table.asm-side th.model { min-width:240px; }
table.asm-ev tbody { border-top:2px solid var(--line); } table.asm-ev td.dim { font-weight:600; font-family:inherit; }
table.asm-ev td ul { margin:0; padding-left:16px; }
`;
    document.head.appendChild(st);
  }

  const missing = (e) => `<p class="err">The assembly data is not available here (${esc(e.message || e)}). It is written by ${SRC.writer}.</p>`;
  const unknown = '<span class="muted">unknown</span>';
  const val = (v, f) => v == null ? unknown : esc(f ? f(v) : v);
  const none = '<span class="muted">none</span>';
  const hexOf = (s) => (typeof s === "string" && /^0x[0-9a-f]+$/i.test(s) ? parseInt(s.slice(2), 16) : null);
  const hx = (n) => "0x" + n.toString(16);
  const shortModel = (m) => m == null ? "" : String(m).replace(/^.*\//, "").split(".").slice(-2).join(".");

  // A declaration: its short name (full name on hover) and, when the declaration map has it, its
  // source (a link when the page knows its repository, else file:line).
  function declCell(decls, decl) {
    const loc = decls[decl];
    let src = "";
    if (loc) {
      const f = typeof repoFile === "function" ? repoFile(loc.file) : null;
      src = f ? ` <a href="${esc(f.blob)}${loc.line ? "#L" + loc.line : ""}" target="_blank" rel="noopener noreferrer" title="${esc(loc.file)}">source</a>`
        : ` <span class="muted" title="${esc(loc.module)}">${esc(loc.file.split("/").pop())}${loc.line ? ":" + loc.line : ""}</span>`;
    }
    return `<code title="${esc(decl)}">${esc(String(decl).split(".").slice(-2).join("."))}</code>${src}`;
  }
  const axiomsCell = (axs) => !axs || !axs.length ? '<span class="muted">none</span>'
    : axs.map((a) => STANDARD_AXIOMS.includes(a) ? `<span class="muted">${esc(a)}</span>` : `<span class="st st-bad" title="not a standard axiom">${esc(a)}</span>`).join(", ");
  const premisesCell = (hs) => !hs || !hs.length ? '<span class="muted">none (unconditional)</span>'
    : "<ul>" + hs.map((h) => `<li><code>${esc(h)}</code></li>`).join("") + "</ul>";

  // ---------- evidence dimensions ----------
  // Each dimension is one proposition of Silmaril.Elf.Asm; `holds` and `refutes` are the evidence
  // kinds (Silmaril.Elf.Asm.Export) that state it or its negation. Rows are filled from the
  // function's evidence array only: no row reads another row.
  const DIMENSIONS = [
    { id: "arch", label: "architecture", prop: "ArchOf F f", what: "the file's header names the function's architecture", holds: ["arch"], refutes: ["notArch"] },
    { id: "bytes", label: "bytes (segment)", prop: "BytesAt F f", what: "the bytes are the file's bytes at the file offset, mapped by the segment to the address (no zero fill)", holds: ["bytes"], refutes: ["notBytes"] },
    { id: "sectionBytes", label: "bytes (section)", prop: "SectionBytesAt F f", what: "the bytes are the file's bytes through the section (a relocatable object has no segments)", holds: ["sectionBytes"], refutes: [] },
    { id: "code", label: "bytes (code fact)", prop: "CodeAt F vaddr bytes", what: "the ELF API's code fact at the function's address", holds: ["code"], refutes: [] },
    { id: "symbol", label: "symbol", prop: "SymbolOf F f", what: "a function symbol with the function's name, value and size", holds: ["symbol"], refutes: [] },
    { id: "decode", label: "decodes", prop: "DecodesAs isa f d", what: "the instruction model decodes the bytes back to back", holds: ["decode"], refutes: ["noDecode"], perModel: true },
    { id: "lines", label: "lines tile", prop: "LinesTile f", what: "the display lines' byte ranges tile the bytes (their text is not read)", holds: ["lineTiles"], refutes: [] },
    { id: "refs", label: "references grounded", prop: "RefsGrounded F f isa d", what: "each relocation reference is the file's relocation; each decoded reference is the decoded branch target", holds: ["refs"], refutes: [] },
    { id: "unrelocated", label: "unrelocated", prop: "Unrelocated F f", what: "no relocation of the file patches the function's bytes", holds: ["unrelocated"], refutes: [] },
    { id: "present", label: "present (load)", prop: "Load.PresentFn F name", what: "the file defines a function of this name", holds: ["present"], refutes: [] },
    { id: "contract", label: "contract", prop: "FnContract.Spec.Total (machine)", what: "a machine contract, stated in the same theorem as the function's bytes", holds: ["contract"], refutes: [] },
  ];
  const KNOWN_KINDS = new Set(DIMENSIONS.flatMap((d) => d.holds.concat(d.refutes)));

  // The models a function has a decoding for or decode evidence about, in order of appearance.
  function decodeModels(fn) {
    const ms = [];
    for (const d of fn.decodings || []) if (!ms.includes(d.model)) ms.push(d.model);
    for (const e of fn.evidence || []) if ((e.kind === "decode" || e.kind === "noDecode") && e.model != null && !ms.includes(e.model)) ms.push(e.model);
    return ms;
  }

  // The rows of the evidence panel: one per dimension (decodes: one per model), each with the
  // entries that state it (`pos`) or its negation (`neg`).
  function evidenceRows(fn) {
    const ev = fn.evidence || [];
    const rows = [];
    for (const D of DIMENSIONS) {
      const pick = (kinds, model) => ev.filter((e) => kinds.includes(e.kind) && (model === undefined || e.model === model));
      if (D.perModel) {
        const ms = decodeModels(fn);
        if (!ms.length) rows.push({ D, model: null, pos: [], neg: [] });
        for (const m of ms) rows.push({ D, model: m, pos: pick(D.holds, m), neg: pick(D.refutes, m) });
      } else rows.push({ D, model: null, pos: pick(D.holds), neg: pick(D.refutes) });
    }
    const other = ev.filter((e) => !KNOWN_KINDS.has(e.kind));
    return { rows, other };
  }
  // A theorem's premises: schema 1.2 `assumptions` (with `applicability`), else 1.0 `hypotheses`.
  const premisesOf = (e) => (e.assumptions && e.assumptions.length ? e.assumptions : e.hypotheses) || [];
  const unconditional = (e) => e.applicability ? e.applicability === "unconditional" : !premisesOf(e).length;
  // A row's status, from its own entries. Every entry is a proved theorem (1.2 `statusKind:
  // "theorem"`); a conditional one is a theorem with undischarged premises, never an open problem.
  function rowStatus(r) {
    if (r.pos.length && r.neg.length) return "conflicting";
    if (r.neg.length) return "does not hold";
    if (!r.pos.length) return "none";
    return r.pos.some(unconditional) ? "holds" : "holds under premises";
  }
  // A decoder that is a partial function (`decode : bytes → Option insn`) proves acceptance or
  // rejection, never why it rejected: invalid, incomplete and unsupported bytes all give `none`.
  // So a decode row says "rejected" (¬ DecodesAs proved) or "unknown" (no theorem), never a cause.
  function statusPill(s, D) {
    if (D && D.id === "decode") {
      if (s === "does not hold") return '<span class="st st-bad" title="a theorem states ¬ DecodesAs: this model\'s decoder rejects the bytes. A rejection does not say why (invalid, incomplete or unsupported are not distinguished)">rejected (¬ DecodesAs proved; no cause classified)</span>';
      if (s === "none") return '<span class="muted" title="no DecodesAs theorem either way for this model">none: unknown (no DecodesAs theorem)</span>';
    }
    return s === "holds" ? '<span class="prov prov-lean" title="a theorem states it, with no premise">holds</span>'
      : s === "holds under premises" ? '<span class="st st-open" title="a proved theorem whose premises (listed) are not discharged: a conditional theorem, not a registered open problem">holds under premises (conditional theorem)</span>'
      : s === "does not hold" ? '<span class="st st-bad" title="a theorem states its negation">does not hold (negation proved)</span>'
      : s === "conflicting" ? '<span class="st st-bad">both it and its negation are stated</span>'
      : '<span class="muted">none</span>';
  }
  // Conformance rows: `abiRows` (elf-pages adds them, each linked to the record by a checked bridge
  // theorem); a pre-1.2 `abi` array is still read. A 1.2 `abi` object is metadata, never rows.
  const abiRows = (fn) => Array.isArray(fn.abiRows) ? fn.abiRows : Array.isArray(fn.abi) ? fn.abi : [];
  // The read-only data a conformance row's code carries (`Code.data`). A range counts only with a
  // finite extent, its exact bytes, a theorem grounding them in the file's read-only mapping
  // (`MappedAt`) and one that no relocation writes them (`Untouched`); a read-only flag or a
  // target name alone is metadata.
  function dataGrounded(r) {
    return r && Number.isFinite(Number(r.vaddr)) && Number.isFinite(Number(r.size)) && Number(r.size) > 0 &&
      typeof r.bytesHex === "string" && r.bytesHex.length === 2 * Number(r.size) && !!r.mapped && !!r.untouched;
  }
  function dataCell(a, decls) {
    const ds = Array.isArray(a.data) ? a.data : [];
    if (!ds.length) return "";
    return '<ul class="asm-data">' + ds.map((r) => dataGrounded(r)
      ? `<li data-grounded="yes">data <code>${esc(r.vaddr)}</code>, ${esc(r.size)} B: bytes ${declCell(decls, r.mapped)} (MappedAt), not relocated ${declCell(decls, r.untouched)} (Untouched)</li>`
      : `<li data-grounded="no"><span class="st st-bad" title="a Code.data range needs a finite extent, its exact bytes, MappedAt and Untouched">not grounded: not counted</span> <code>${esc(r.vaddr ?? "?")}</code>${r.size != null ? ", " + esc(r.size) + " B" : ""}${r.readOnly ? ' <span class="muted">(read-only flag: metadata)</span>' : ""}</li>`).join("") + "</ul>";
  }

  function evidencePanel(fn, decls) {
    const { rows, other } = evidenceRows(fn);
    let h = '<div class="tablebox"><table class="asm-ev"><thead><tr><th>dimension</th><th>proposition</th><th>status</th><th>declaration</th><th>model</th><th>axioms</th><th>premises (hypotheses)</th></tr></thead>';
    for (const r of rows) {
      const st = rowStatus(r);
      const label = r.D.label + (r.model != null ? `: ${shortModel(r.model)}` : "");
      const ents = r.pos.map((e) => [e, false]).concat(r.neg.map((e) => [e, true]));
      const span = Math.max(1, ents.length);
      const head = `<td class="dim" rowspan="${span}" title="${esc(r.D.what)}">${esc(label)}</td><td rowspan="${span}"><code>${esc((r.neg.length && !r.pos.length ? "¬ " : "") + r.D.prop)}</code>` +
        `${r.model != null ? `<br><span class="muted" title="${esc(r.model)}">isa: ${esc(r.model)}</span>` : ""}</td><td rowspan="${span}">${statusPill(st, r.D)}</td>`;
      h += `<tbody data-dim="${esc(r.D.id)}"${r.model != null ? ` data-model="${esc(r.model)}"` : ""} data-status="${esc(st)}">`;
      if (!ents.length) h += `<tr>${head}<td colspan="4">${none}</td></tr>`;
      ents.forEach(([e, neg], i) => {
        h += `<tr data-kind="${esc(e.kind)}">${i === 0 ? head : ""}<td>${neg ? '<span class="muted">¬</span> ' : ""}${declCell(decls, e.decl)}</td>` +
          `<td>${e.model == null ? '<span class="muted">—</span>' : `<code title="${esc(e.model)}">${esc(e.model)}</code>`}</td>` +
          `<td>${axiomsCell(e.axioms)}</td><td>${premisesCell(premisesOf(e))}${e.note ? `<br><span class="muted">${esc(e.note)}</span>` : ""}</td></tr>`;
      });
      h += "</tbody>";
    }
    // ABI conformance: its own row, never filled from abiRef.
    const abi = abiRows(fn);
    h += `<tbody data-dim="abi" data-status="${abi.length ? "rows" : "none"}">`;
    if (!abi.length) h += '<tr><td class="dim">ABI conformance</td><td><span class="muted">a conformance problem of the calling-convention layer</span></td><td><span class="muted">none</span></td>' +
      '<td colspan="4"><span class="muted">no conformance row</span> <span class="muted">(this data has no ABI conformance evidence; <code>abiRef</code> above is metadata, not evidence)</span></td></tr>';
    abi.forEach((a, i) => {
      h += `<tr data-kind="abi">${i === 0 ? `<td class="dim" rowspan="${abi.length}">ABI conformance</td>` : ""}<td>problem <code>${esc(a.problemId ?? "")}</code><br><span class="muted">ABI ${esc(a.abiId ?? "")}, ${esc(a.mode ?? "")}${a.frame != null ? ", frame " + esc(a.frame) : ""}${a.machine ? ", on " + esc(a.machine) : ""}</span>` +
        `${a.bridge ? `<br><span class="muted">same function as this record:</span> ${declCell(decls, a.bridge)} <span class="muted">(${esc(a.association ?? "")})</span>` : ""}` +
        `${a.limits ? `<br><span class="asm-meta" title="what the row does not claim">${esc(a.limits)}</span>` : ""}</td>` +
        `<td><span class="st" title="as given by the conformance row">${esc(a.status ?? "")}</span></td><td>${a.decl ? declCell(decls, a.decl) : none}</td><td colspan="3"><span class="muted">as given by the conformance row</span>${dataCell(a, decls)}</td></tr>`;
    });
    h += "</tbody>";
    if (other.length) {
      h += '<tbody data-dim="other" data-status="other">' + other.map((e, i) => `<tr data-kind="${esc(e.kind)}">${i === 0 ? `<td class="dim" rowspan="${other.length}">other evidence</td><td rowspan="${other.length}"><span class="muted">a kind this view does not know</span></td><td rowspan="${other.length}"><span class="st">not interpreted</span></td>` : ""}` +
        `<td>${declCell(decls, e.decl)} <span class="muted">${esc(e.kind)}</span></td><td>${e.model == null ? '<span class="muted">—</span>' : `<code>${esc(e.model)}</code>`}</td><td>${axiomsCell(e.axioms)}</td><td>${premisesCell(e.hypotheses)}</td></tr>`).join("") + "</tbody>";
    }
    return h + "</table></div>";
  }

  // ---------- one function ----------
  function bytesOf(fn) { return (String(fn.bytesHex || "").match(/../g) || []); }

  function hexDump(fn) {
    const bs = bytesOf(fn), base = hexOf(fn.extent.vaddr), fo = hexOf(fn.extent.fileOff);
    let rows = "";
    for (let o = 0; o < bs.length; o += 16) rows += `<tr><td class="o">+${hx(o)}</td><td class="o">${base == null ? "" : hx(base + o)}</td><td class="o">${fo == null ? "" : hx(fo + o)}</td><td>${bs.slice(o, o + 16).join(" ")}</td></tr>`;
    return `<div class="tablebox"><table class="asm-hex"><thead><tr><th>offset</th><th>address</th><th>file offset</th><th>bytes</th></tr></thead><tbody>${rows}</tbody></table></div>`;
  }

  // The display lines beside each model's decoding, one row per offset where a line or an
  // instruction starts; "·" marks a row inside an earlier line or instruction of that column.
  function sideBySide(fn, decls) {
    const bs = bytesOf(fn), base = hexOf(fn.extent.vaddr);
    const lines = fn.lines || [], decs = fn.decodings || [];
    const cols = [{ items: lines.map((l) => ({ off: l.off, len: l.len, text: l.text, label: l.label })) }]
      .concat(decs.map((d) => ({ items: d.insns.map((i) => ({ off: i.off, len: i.len, text: i.render })) })));
    const offs = [...new Set(cols.flatMap((c) => c.items.map((i) => i.off)))].sort((a, b) => a - b);
    const starts = cols.map((c) => new Map(c.items.map((i) => [i.off, i])));
    const evFor = (m) => (fn.evidence || []).filter((e) => e.kind === "decode" && e.model === m);
    const negFor = (m) => (fn.evidence || []).filter((e) => e.kind === "noDecode" && e.model === m);
    let h = '<div class="tablebox"><table class="asm-side"><thead><tr><th>offset</th><th>address</th><th>bytes</th>' +
      '<th class="disp">display line (objdump)<br><span class="st" title="external text, kept for reading; no theorem reads it">display only, not checked</span></th>' +
      decs.map((d) => {
        const ev = evFor(d.model);
        return `<th class="model" data-model="${esc(d.model)}">model <code title="${esc(d.model)}">${esc(d.model)}</code><br><span class="muted">decoding</span> ${declCell(decls, d.decl)}<br>` +
          (ev.length ? `<span class="prov prov-lean" title="DecodesAs: the decoder accepted these bytes">decoder accepted</span> ${ev.map((e) => declCell(decls, e.decl)).join(", ")}`
            : negFor(d.model).length ? `<span class="st st-bad" title="a theorem states ¬ DecodesAs for this model; no cause is classified">rejected (¬ DecodesAs; no DecodesAs evidence)</span> ${negFor(d.model).map((e) => declCell(decls, e.decl)).join(", ")}`
            : '<span class="st st-bad" title="no DecodesAs theorem for this model in the evidence">unknown: no DecodesAs evidence</span>') +
          '<br><span class="asm-meta" title="the text is the decoding\'s printer output; what is proved is the DecodesAs theorem named here, about the decoded instructions, not about this text">text: printer output, not evidence</span>' + "</th>";
      }).join("") + "</tr></thead><tbody>";
    const open = cols.map(() => null);
    offs.forEach((o, k) => {
      const next = k + 1 < offs.length ? offs[k + 1] : bs.length;
      const lab = starts[0].get(o)?.label;
      if (lab) h += `<tr class="lbl"><td colspan="${4 + decs.length}">&lt;${esc(lab)}&gt;:</td></tr>`;
      const cells = cols.map((c, ci) => {
        const it = starts[ci].get(o);
        if (it) { open[ci] = it; return `<td${ci === 0 ? ' class="disp"' : ""}>${esc(it.text)}</td>`; }
        const cur = open[ci];
        return cur && o < cur.off + cur.len ? `<td class="cont${ci === 0 ? " disp" : ""}">·</td>` : `<td${ci === 0 ? ' class="disp"' : ""}></td>`;
      });
      h += `<tr data-off="${o}"><td class="muted">+${hx(o)}</td><td>${base == null ? "" : hx(base + o)}</td><td>${bs.slice(o, next).join(" ")}</td>${cells.join("")}</tr>`;
    });
    return h + "</tbody></table></div>";
  }

  function originText(o) {
    if (!o) return unknown;
    if (o.kind === "reloc") return `relocation <span class="muted">(${esc(o.selector)}, entry ${esc(o.index)})</span>`;
    if (o.kind === "decoded") return "decoded";
    if (o.kind === "display") return "listing";
    return esc(o.kind);
  }
  // Where a target lies (segment, section, read-only): computed from the parse for display, not a
  // theorem; a read-only target is never Code.data on that basis alone.
  function targetInText(t) {
    if (!t) return "";
    const parts = [t.segment != null ? "segment " + esc(t.segment) : null, t.section ? esc(t.section) : null, t.readOnly != null ? (t.readOnly ? "read-only" : "writable") : null].filter(Boolean);
    return parts.length ? `<br><span class="asm-meta" title="${esc(t.provenance ?? "computed from the parse; not a theorem")}">target in ${parts.join(", ")}: metadata (not evidence)</span>` : "";
  }
  function refsTable(fn, decls) {
    const refs = fn.refs || [];
    if (!refs.length) return `<p class="muted">none</p>`;
    const base = hexOf(fn.extent.vaddr);
    const g = (fn.evidence || []).filter((e) => e.kind === "refs");
    const grounded = (r) => {
      if (r.origin && r.origin.kind === "display") return '<span class="muted">not grounded: a listing reference (RefsGrounded does not cover it)</span>';
      return g.length ? `<span class="prov prov-lean">grounded</span> by ${g.map((e) => `${declCell(decls, e.decl)}${e.model ? ` <span class="muted">(${esc(shortModel(e.model))})</span>` : ""}`).join(", ")}`
        : '<span class="st st-bad">not grounded</span> <span class="muted">(no RefsGrounded evidence)</span>';
    };
    return '<div class="tablebox"><table class="asm-refs"><thead><tr><th>offset</th><th>address</th><th>target</th><th>symbol</th><th>relocation type</th><th>addend</th><th>origin</th><th>grounded</th></tr></thead><tbody>' +
      refs.map((r) => `<tr data-origin="${esc(r.origin ? r.origin.kind : "")}"><td>+${hx(r.off)}</td><td>${base == null ? "" : hx(base + r.off)}</td><td>${val(r.target)}</td><td>${val(r.symbol)}</td>` +
        `<td>${r.kind ? esc(r.kind) : '<span class="muted">— (not a relocation)</span>'}</td><td>${esc(r.addend)}</td><td>${originText(r.origin)}${targetInText(r.targetIn)}</td><td>${grounded(r)}</td></tr>`).join("") +
      "</tbody></table></div>";
  }

  const dl = (pairs) => "<dl>" + pairs.map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v}</dd>`).join("") + "</dl>";
  function backLinks(fn) {
    const f = fn.fileInfo;
    if (!f.slug) return `<span class="muted">this file has no page in the ELF tab</span>`;
    const v = hexOf(fn.extent.vaddr);
    return `<a href="#/elf-file/${enc(f.slug)}">ELF tab: ${esc(f.slug)}</a> · <a href="#/elf-funcs/${enc(f.slug)}">its function symbols</a>` +
      (v != null && fn.extent.segment != null ? ` · <a href="#/elf-disasm/${enc(f.slug)}/${hx(v)}">objdump view at ${hx(v)}</a> <span class="muted">(unverified)</span>` : "");
  }

  function renderFunction(fn, decls) {
    const f = fn.fileInfo, x = fn.extent, a = fn.arch || {};
    let h = `<h2><a href="#/asm">Assembly</a> / ${esc(f.key)} / <code>${esc(fn.name)}</code></h2>` +
      `<p class="muted">record ${declCell(decls, fn.decl)} · file ${declCell(decls, fn.file)}${f.path ? ` <code>${esc(f.path)}</code>` : ""}${f.sha256 ? ` · SHA-256 <code title="${esc(f.sha256)}">${esc(f.sha256.slice(0, 16))}…</code>` : ""}</p>` +
      `<p>${backLinks(fn)}</p>` +
      '<p class="note">Each row of the evidence panel is a separate proposition about this record; no row is inferred from another, and there is no overall status. ' +
      "A dimension with no theorem shows <b>none</b>.</p>";
    // Each extent field is a record field; it is grounded in the file only by the dimension named
    // beside it, with that dimension's own status.
    const { rows: evRows } = evidenceRows(fn);
    const ground = (id, prop) => {
      const r = evRows.find((q) => q.D.id === id);
      return ` <span class="asm-origin" title="a field of the record; grounded in the file only by ${esc(prop)}">record field; grounded by <code>${esc(prop)}</code>: ${statusPill(r ? rowStatus(r) : "none", r && r.D)}</span>`;
    };
    const addrKind = x.addrKind === "link" ? ' <span class="muted">(link-time address; no load base: a row rebases it at each admitted base)</span>' : "";
    h += '<div class="grid"><div><h3>Extent</h3>' + dl([["virtual address", val(x.vaddr) + addrKind + ground("bytes", "BytesAt")], ["size", val(x.size, (n) => n + " B")], ["file offset", val(x.fileOff)],
      ["segment", val(x.segment) + (x.segment != null ? ground("bytes", "BytesAt") + ' <span class="muted">(the segment flags are the file\'s program header, read by the ELF tab; BytesAt uses its mapping, not a record flag)</span>' : "")],
      ["section", val(x.shndx, (n) => "#" + n)],
      ["symbol", (fn.symbol ? `${esc(fn.symbol.table)} #${esc(fn.symbol.index)}` + ground("symbol", "SymbolOf") : unknown) +
        (fn.symbol && fn.symbol.version != null ? ` <span class="asm-origin">version <code>${esc(fn.symbol.version)}</code>: record field; a binding's version is checked only by a conformance row's <code>CodeOf</code> (ld.so's versioned lookup)</span>` : "")]]) + "</div>" +
      '<div><h3>Architecture</h3>' + dl([["id", val(a.id)], ["e_machine", val(a.machine)], ["class", val(a.class)], ["data", val(a.data)], ["OS ABI", val(a.osabi)],
        ["abiRef", `${fn.abiRef == null ? unknown : `<code>${esc(fn.abiRef)}</code>`} <span class="asm-meta" title="an identifier carried by the record; no proposition reads it">metadata (not evidence)</span>`]].concat(
          fn.abi && !Array.isArray(fn.abi) && typeof fn.abi === "object" ? [["abi (cited)", `<code>${esc(fn.abi.id ?? "")}</code> ${esc(fn.abi.source ?? "")} <span class="asm-meta" title="${esc(fn.abi.note ?? "metadata")}">metadata (not evidence)</span>`]] : []).concat(
          fn.listing ? [["listing", `${esc(fn.listing.tool ?? "")} <span class="asm-meta">${fn.listing.verified ? "verified" : "not verified"}</span>`]] : [])) + "</div></div>";
    h += "<h3>Evidence</h3>" + evidencePanel(fn, decls);
    h += `<h3>Bytes (${bytesOf(fn).length} B)</h3>` + hexDump(fn);
    h += "<h3>Display lines and decodings</h3>" +
      '<p class="asm-warn" role="note"><b>Display lines are display only, not checked.</b> They are objdump\'s text, kept for reading: no proposition reads their text ' +
      "(LinesTile only says their byte ranges tile the bytes). Each instruction model's decoding is a separate column, a value checked by its decoder; " +
      "a column's evidence is the DecodesAs theorem named in its header; its text is that decoding's printer output, and a line's source (lean-decode or objdump) is not itself evidence. " +
      "A model with ¬ DecodesAs proved is <b>rejected</b>; the view does not say why (an <code>Option</code> decoder does not distinguish invalid, incomplete or unsupported bytes).</p>" +
      (fn.decodings && fn.decodings.length ? "" : '<p class="muted">No decoding by any instruction model in this record.</p>') + sideBySide(fn, decls);
    h += "<h3>References</h3>" + refsTable(fn, decls);
    return h;
  }

  // ---------- index ----------
  function dimCell(fn, id) {
    if (id === "abi") return abiRows(fn).length ? abiRows(fn).map((r) => `<span class="st">${esc(r.status ?? "")}</span>`).join(" ") : '<span class="muted">no conformance row</span>';
    const rs = evidenceRows(fn).rows.filter((r) => r.D.id === id);
    if (id === "decode") {
      const shown = rs.filter((r) => r.model != null);
      if (!shown.length) return none;
      return shown.map((r) => `<span title="${esc(r.model)}">${esc(shortModel(r.model))}</span>: ${statusPill(rowStatus(r), r.D)}`).join("<br>");
    }
    return rs.map((r) => statusPill(rowStatus(r), r.D)).join(" ");
  }
  const INDEX_DIMS = [["arch", "arch"], ["bytes", "bytes (segment)"], ["sectionBytes", "bytes (section)"], ["code", "CodeAt"], ["symbol", "symbol"],
    ["decode", "decodes (per model)"], ["lines", "lines tile"], ["refs", "refs grounded"], ["unrelocated", "unrelocated"], ["present", "present"], ["contract", "contract"], ["abi", "ABI conformance"]];

  async function asmIndex(D) {
    let h = "<h2>Assembly</h2><p>Assembly functions: the exact bytes of each, its display listing beside each instruction model's decoding, its references, " +
      "and the Lean theorems about it, <b>one column per dimension</b>. The dimensions are independent propositions (<code>Silmaril.Elf.Asm</code>): " +
      "a column shows only the theorems of that dimension, and a function has no overall status.</p>";
    h += '<div class="tablebox"><table class="asm-index"><thead><tr><th>file</th><th>function</th><th>address</th><th>size</th>' +
      INDEX_DIMS.map(([, t]) => `<th>${esc(t)}</th>`).join("") + "</tr></thead><tbody>" +
      D.fns.map((fn) => `<tr data-decl="${esc(fn.decl)}"><td title="${esc(fn.fileInfo.path || fn.file)}">${fn.fileInfo.slug ? `<a href="#/elf-file/${enc(fn.fileInfo.slug)}">${esc(fn.fileInfo.key)}</a>` : esc(fn.fileInfo.key)}</td>` +
        `<td><a href="${fn.route}"><code>${esc(fn.name)}</code></a><br><span class="muted" title="${esc(fn.decl)}">${esc(fn.decl.split(".").pop())}</span></td>` +
        `<td>${val(fn.extent.vaddr)}</td><td class="num">${val(fn.extent.size)}</td>` +
        INDEX_DIMS.map(([id]) => `<td data-dim="${id}">${dimCell(fn, id)}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
    return h;
  }

  function chooser(fns, decls) {
    return `<h2><a href="#/asm">Assembly</a> / ${esc(fns[0].fileInfo.key)} / <code>${esc(fns[0].name)}</code></h2>` +
      `<p>${fns.length} records of this file have this name; they are different claims (for example another architecture), not the same function. Choose one:</p><ul class="asm-choose">` +
      fns.map((fn) => `<li><a href="${fn.route}">${esc(fn.decl)}</a> <span class="muted">${esc(fn.arch ? fn.arch.id : "")}, ${val(fn.extent.vaddr)}</span> ${declCell(decls, fn.decl)}</li>`).join("") + "</ul>";
  }

  async function asmView(arg) {
    let D;
    try { D = await load(SRC); } catch (e) { return missing(e); }
    const parts = String(arg || "").split("/").filter((s) => s !== "");
    if (!parts.length) return asmIndex(D);
    const [key, name, decl] = [parts[0], parts[1], parts.slice(2).join("/")];
    const inFile = D.fns.filter((fn) => fn.fileInfo.key === key || fn.fileInfo.path === key || fn.file === key);
    if (!inFile.length) return `<p class="err">No assembly record for the file <code>${esc(key)}</code>.</p><p><a href="#/asm">all functions</a></p>`;
    if (!name) return asmIndex({ ...D, fns: inFile });
    let hits = inFile.filter((fn) => fn.name === name);
    if (decl) hits = hits.filter((fn) => fn.decl === decl);
    if (!hits.length) return `<p class="err">No assembly record <code>${esc(name)}</code> in <code>${esc(key)}</code>.</p><p><a href="#/asm">all functions</a></p>`;
    if (hits.length > 1) return chooser(hits, D.decls);
    return renderFunction(hits[0], D.decls);
  }

  registerView({ id: "asm", title: "Assembly", nav: 85.5, render: (arg) => asmView(arg) });
})();
