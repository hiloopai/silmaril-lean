// The compiler explorer's page. Every text from the database is inserted with textContent (syntax
// highlighting makes token spans; no string is ever parsed as HTML).
import { lineOffsets, indexEdges, edgeObligations, badge, highlightText, langOf, includeRows, prettySexp, stageTrust } from "./view.js";

import { initCorpus } from "./corpus.js";
import { initEquivalence } from "./equivalence.js";

const $ = (id) => document.getElementById(id);
const el = (tag, cls, text) => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined && text !== null) e.textContent = String(text);
  return e;
};
const COLORS = 8;
const state = { list: [], problem: null, index: null, locked: null, mode: "navigation", show: {} };

async function getJSON(url) {
  const r = await fetch(url);
  if (!r.ok) throw new Error(`${url}: ${r.status}`);
  return r.json();
}

function groupOf(id) { return id.split("/").slice(0, 2).join("/"); }

async function init() {
  if (await initEquivalence()) return;
  if (await initCorpus()) return;
  state.list = await getJSON("api/problems.json");
  const groups = [...new Set(state.list.map((p) => groupOf(p.id)))];
  const prog = $("program");
  for (const g of groups) prog.append(new Option(g, g));
  const params = new URLSearchParams(location.search);
  const want = params.get("problem");
  if (want && state.list.some((p) => p.id === want)) prog.value = groupOf(want);
  prog.onchange = () => { fillBuilds(); load($("build").value); };
  $("build").onchange = () => load($("build").value);
  $("mode").onchange = () => { state.mode = $("mode").value; render(); };
  const mode = params.get("mode");
  if (mode === "semantic" || mode === "navigation") { state.mode = mode; $("mode").value = mode; }
  for (const side of ["source", "target"]) {
    $(`${side}-show`).onchange = () => { state.show[side] = $(`${side}-show`).value; render(); };
    $(`${side}-exact`).onchange = render;
  }
  fillBuilds(want);
  await load($("build").value, params.get("source"), params.get("target"));
}

function fillBuilds(want) {
  const b = $("build");
  b.replaceChildren();
  for (const p of state.list.filter((q) => groupOf(q.id) === $("program").value)) {
    const d = p.derivation || {};
    const how = d.compiler ? `${d.compiler} ${(d.version || "").replace(/^.*\) /, "")} -${d.opt || "?"}`
      : d.kind === "claimed" ? "supplied" : (d.kind || p.direction || "file");
    b.append(new Option(`${how} — ${p.id.split("/").slice(2).join("/") || p.id}`, p.id));
  }
  if (want && [...b.options].some((o) => o.value === want)) b.value = want;
}

async function load(id, source, target) {
  state.problem = await getJSON(state.list.find(p => p.id === id)?.static_path || ("api/problems/" + encodeURIComponent(id)));
  state.locked = null;
  state.pretty = new Map();
  const mode = $("mode");
  mode.querySelector('[value="semantic"]').disabled = !state.problem.edges.some((edge) => edge.kind === "semantic");
  if (mode.selectedOptions[0]?.disabled) mode.value = "navigation";
  state.mode = mode.value;
  const v = state.problem.view;
  state.show = { source: v.source, target: v.target };
  for (const [side, want] of [["source", source], ["target", target]]) {
    const alts = (v.alternatives || {})[side] || [{ role: v[side], label: side }];
    if (want && alts.some((a) => a.role === want)) state.show[side] = want;
    const sel = $(`${side}-show`);
    sel.replaceChildren(...alts.map((a) => new Option(a.label, a.role)));
    sel.value = state.show[side];
    sel.disabled = alts.length < 2;
    $(`${side}-exact`).checked = false;
  }
  render();
}

function textOf(p, role) {
  if (role === p.view.source) return p.texts.source;
  if (role === p.view.target) return p.texts.target;
  return p.alt_texts ? p.alt_texts[role] : null;
}

function render() {
  const p = state.problem;
  const primary = { source: state.show.source === p.view.source, target: state.show.target === p.view.target };
  const text = { source: textOf(p, state.show.source) ?? "(not text)", target: textOf(p, state.show.target) ?? "(not displayable text)" };
  const format = {};
  for (const side of ["source", "target"]) {
    const role = state.show[side];
    const exact = text[side];
    if (!state.pretty.has(role)) {
      state.pretty.set(role, langOf(p.artifacts[role]?.media) === "sexp" ? prettySexp(exact, role === "compact" ? 64 : 88) : null);
    }
    const pretty = state.pretty.get(role);
    const showPretty = pretty !== null && !$(`${side}-exact`).checked;
    $(`${side}-exact-label`).hidden = pretty === null;
    $(side).classList.toggle("pretty-code", showPretty);
    if (pretty !== null) {
      format[side] = showPretty ? "formatted · display only" : "exact text";
      if (showPretty) {
        text[side] = pretty;
        primary[side] = false;
      }
    }
  }
  const lines = { source: lineOffsets(text.source), target: lineOffsets(text.target) };
  const linked = primary.source && primary.target;
  state.linked = linked;
  if (!linked) state.locked = null;
  state.index = linked ? indexEdges(p, state.mode, lines.source, lines.target)
    : { byLine: { source: new Map(), target: new Map() }, edgeLines: new Map() };
  state.colorOf = new Map();
  p.edges.filter((e) => e.kind === state.mode).forEach((e, i) => state.colorOf.set(e.id, i % COLORS));
  for (const side of ["source", "target"]) {
    const role = state.show[side];
    const art = p.artifacts[role];
    $(`${side}-title`).textContent = [side === "source" ? "Source" : "Target", art?.path || role, format[side]].filter(Boolean).join(" · ");
    const links = p.artifact_links[role] || [];
    const original = (p.artifact_links[side] || []).filter((link) => link.kind === "viewer");
    drawLinks($(`${side}-links`), role === side ? links : [...original, ...links]);
    const stages = (p.extra.stages || []).filter((stage) => stage.side === side && stage.model);
    const stage = stages.find((stage) => stage.output === role);
    const input = role === side && stages.find((stage) => stage.input === role);
    const provenance = stage ? stageRow(p, stage) : input ? stageValue(p, "C input", input.input_decl, role) : null;
    $(`${side}-stage`).replaceChildren(...(provenance ? [provenance] : []));
    drawCode($(side), side, text[side], langOf(art ? art.media : ""));
  }
  drawProblem(p);
  drawQuestions(p);
  drawStages(p);
  drawBlocks(p);
  drawDwarf(p);
  drawEnv(p);
  drawProvenance(p);
  const nEdges = p.edges.filter((e) => e.kind === state.mode).length;
  $("status").textContent = linked
    ? `${nEdges} ${state.mode} link(s). Manifest ${p.manifest_sha256.slice(0, 12)}…, context ${p.context_hash.slice(0, 12)}…`
    : "Fragment links are hidden: their coordinates apply only to the primary representations.";
  showSelection(null);
}

function drawLinks(box, links) {
  box.replaceChildren();
  appendLinks(box, links);
}

function appendLinks(box, links) {
  for (const l of links) {
    const a = el("a", "ext", l.kind === "viewer" || l.kind === "download" ? l.label :
      l.kind === "explorer" ? "explorer ↗" : l.kind === "lean" ? "Lean ↗" : "repo ↗");
    a.href = l.url;
    a.title = l.label;
    if (l.kind === "download") a.download = "";
    else { a.target = "_blank"; a.rel = "noopener noreferrer"; }
    box.append(a);
  }
}

function drawCode(box, side, text, lang) {
  box.replaceChildren();
  const toks = highlightText(text, lang);
  const links = state.index.byLine[side];
  toks.forEach((tokens, i) => {
    const n = i + 1;
    const row = el("div", "line");
    row.dataset.side = side;
    row.dataset.n = n;
    const ids = links.get(n) || [];
    if (ids.length) {
      row.classList.add("linked", `c${state.colorOf.get(ids[0])}`);
      if (ids.length > 1) row.classList.add("multi");
      row.tabIndex = 0;
      row.setAttribute("role", "button");
      row.setAttribute("aria-label", `${side} line ${n}: ${ids.length} link(s)`);
      const pick = () => { state.locked = state.locked && state.locked.join() === ids.join() ? null : ids; highlight(ids); };
      row.onclick = pick;
      row.onkeydown = (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); pick(); } };
    }
    if (links.size) row.onmouseenter = () => { if (!state.locked) highlight(ids); };
    const tx = el("span", "tx");
    for (const [t, cls] of tokens) tx.append(cls ? el("span", cls, t) : document.createTextNode(t));
    row.append(el("span", "ln", n), tx);
    box.append(row);
  });
}

function highlight(ids) {
  document.querySelectorAll(".line.hl").forEach((r) => r.classList.remove("hl"));
  for (const id of ids) {
    const l = state.index.edgeLines.get(id);
    for (const side of ["source", "target"]) {
      for (const n of l[side]) document.querySelector(`.line[data-side="${side}"][data-n="${n}"]`)?.classList.add("hl");
    }
  }
  const first = ids.length && state.index.edgeLines.get(ids[0]).target[0];
  if (first) document.querySelector(`.line[data-side="target"][data-n="${first}"]`)?.scrollIntoView({ block: "nearest" });
  showSelection(ids);
}

function statusBadge(status) {
  const b = badge(status);
  const s = el("span", `badge ${b.cls}`, b.label);
  s.title = b.title;
  return s;
}

// An info toggle: a button that shows and hides a short explanation (hover shows it as a title).
let infoSeq = 0;
function info(text) {
  const id = `info-${++infoSeq}`;
  const btn = el("button", "info", "i");
  btn.type = "button";
  btn.title = text;
  btn.setAttribute("aria-label", "explain");
  btn.setAttribute("aria-expanded", "false");
  btn.setAttribute("aria-controls", id);
  const box = el("div", "info-text", text);
  box.id = id;
  box.hidden = true;
  btn.onclick = () => { box.hidden = !box.hidden; btn.setAttribute("aria-expanded", String(!box.hidden)); };
  return [btn, box];
}

function showSelection(ids) {
  const box = $("selection");
  box.replaceChildren(el("h2", null, "Selection"));
  if (!state.linked) {
    box.append(el("p", "muted", "Switch both panes back to their primary representations to show fragment links. Other stages do not use those byte coordinates."));
    return;
  }
  if (!ids || !ids.length) {
    box.append(el("p", "muted", state.mode === "navigation"
      ? "Navigation links say where code came from (debug information, a decompiler, an author), not that it is correct."
      : "Semantic links are program points of a Lean mapping; each has its own obligations."));
    return;
  }
  const p = state.problem;
  for (const id of ids) {
    const e = p.edges.find((x) => x.id === id);
    const card = el("div", "edge");
    card.append(el("div", "edge-id", `${e.kind} · ${e.id}`));
    const frag = (fid) => p.fragments[fid]?.label || fid;
    card.append(el("div", null, `source: ${e.source.map(frag).join("; ")}`), el("div", null, `target: ${e.target.map(frag).join("; ")}`));
    if (e.origin) card.append(el("div", "muted", `origin: ${e.origin}`));
    if (e.note) card.append(el("div", "warn", e.note));
    for (const block of p.extra.blocks || []) {
      if (!block.attribution.includes(id)) continue;
      card.append(el("div", "muted", `Attributed to ${block.side} block candidate ${block.symbol}; navigation only.`));
    }
    if (e.kind === "semantic") for (const o of edgeObligations(p, id)) card.append(obligationRow(o, true));
    box.append(card);
  }
}

// Short names and one-line explanations of the obligation kinds.
const KINDS = {
  translation: ["Does the target refine the source?", "From every related entry whose source state is safe (no run from it has undefined behaviour, every run from it is finite), every target run is safe, finite, stops only at a final state, and returns a result some source run produces."],
  nonvacuity: ["Not vacuous", "Some related entry has a safe source state (one canonical entry, empty caller)."],
  abi: ["ABI entry", "For every argument tuple a System V entry state exists (existence). Return-side ABI conditions are part of the translation."],
  mapping: ["All segments", "Every segment is simulated, including points nobody listed. Individually proved links do not imply it."],
  refinement: ["Location relation", "At every point, each C object with a value holds it in its frame slot (offsets read by c-tv from DWARF, unverified)."],
  decompilation: ["Decompiled block", "The decompiler's checked block prints as this C text, and the machine's rax is the C0 value of its expression. ret and the calling convention are outside the block."],
  c2c_refines: ["Refines the source", "From the canonical entries: wherever the source is safe, every outcome of the target is an outcome of the source."],
  c2c_equivalent: ["Equivalent", "Refinement both ways, from the canonical entries."],
  typing: ["Can these operands be added?", "C11 §6.5.6¶2: the extracted operand types must satisfy the additive constraint. The fragment recognizes only a small grammar, not all of C."],
  operand_types: ["What types does the text give?", "The kernel checks that the restricted recognizer reads these types from the displayed source."],
  elaboration: ["Core function extraction", "The modeled function is extracted from the elaboration of this typed Ail; this does not prove the frontend."],
  core_elaboration: ["Source Ail → Core", "The elaborator returns the exact bound source Core from the bound typed Ail."],
  target_core_elaboration: ["Target Ail → Core", "The elaborator returns the exact bound target Core from the bound typed Ail."],
  decoding: ["Disassembly", "The Lean decoder's listing is the decoding of these bytes."],
  artifact: ["Bytes = object", "The function's bytes are its symbol's code in the registered object."],
  nonvacuity_canonical: ["Canonical entry row", "c.compiles_to.canonical_entry: the placed code implements the C function from its canonical entry."],
  nonvacuity_universal: ["Safe from every entry", "The C function is safe on some tuple from every Core entry (needed for c.compiles_to)."],
  point: ["Point ↔ statement", "The point's Core fragment is the Core of its C statement."],
  edge: ["Is this segment simulated?", "This is a statement about the selected semantic cut-point, not the DWARF reader."],
};
const MAIN = ["translation", "c2c_refines", "c2c_equivalent", "decompilation", "typing", "nonvacuity", "abi", "mapping", "refinement"];

function obligationRow(o, full, anchor = false) {
  const [title, text] = KINDS[o.kind] || [o.kind, ""];
  const row = el("div", "obl");
  if (anchor) row.id = `obligation-${o.id}`;
  const head = el("div", "obl-head");
  head.append(statusBadge(o.status), el("span", "obl-title", o.edge ? `${title} · ${o.id}` : title));
  const [btn, box] = info(`${text}${o.statement ? `\nStatement: ${o.statement}` : ""}${o.reason ? `\n${o.reason}` : ""}`);
  btn.setAttribute("aria-label", `Explain ${title}`);
  head.append(btn);
  for (const l of o.links || []) {
    const a = el("a", "ext", l.kind === "lean" ? "Lean ↗" : "explorer ↗");
    a.href = l.url; a.title = l.label; a.target = "_blank"; a.rel = "noopener noreferrer";
    head.append(a);
  }
  row.append(head, box);
  if (full && o.statement) row.append(el("code", "stmt", o.statement));
  if (o.status === "unsupported" && o.reason) row.append(el("div", "muted", o.reason));
  if (o.evidence && o.evidence.detail && o.status !== "proved") row.append(el("div", "warn", o.evidence.detail));
  if (o.status === "stale") row.append(el("div", "warn", `Evidence exists for manifest ${o.older_manifest.slice(0, 12)}…, not for these artifacts`));
  return row;
}

function drawProblem(p) {
  const box = $("problem");
  const x = p.extra || {};
  const rel = x.relation || {};
  box.replaceChildren(el("h2", null, "Problem"));
  const head = el("div", "q-head");
  const form = x.problem_form || "semantic";
  head.append(el("span", `badge form-${form}`, form === "relation" ? "relation · no semantics" : form), el("strong", null, p.title));
  box.append(head);
  if (rel.description) box.append(el("div", "muted", rel.description));
  if (rel.semantics === "none") {
    box.append(el("div", "nosem", "No semantics: this relation is recorded, not stated in Lean. Nothing below is a statement about it."));
  }
}

function drawQuestions(p) {
  const box = $("questions");
  box.replaceChildren(el("h2", null, "Questions"));
  const x = p.extra || {};
  if (p.obligations.some((obligation) => obligation.status === "unavailable" || obligation.status === "incompatible")) {
    box.append(el("p", "muted", "Some project evidence is missing or does not match. These are database states, not rejected theorems. " +
      "Regenerate the site from the same checkout, or run make compiler-explorer-check for exact local evidence."));
  } else if (p.obligations.some((obligation) => obligation.status === "unchecked")) {
    box.append(el("p", "muted", "Some evidence is not loaded. Run make compiler-explorer-check, then open the local viewer."));
  }
  const shown = p.obligations.filter((o) => MAIN.includes(o.kind) && !(x.problem_form === "relation" && o.status === "unsupported"));
  shown.sort((a, b) => MAIN.indexOf(a.kind) - MAIN.indexOf(b.kind));
  for (const o of shown) box.append(obligationRow(o, false, true));
  if (!shown.length) box.append(el("p", "muted", "No statement is attempted for this problem."));
  const ed = p.questions.edges;
  if (ed.listed) {
    const r = el("div", "obl");
    const h = el("div", "obl-head");
    const [b, t] = info(ed.note);
    h.append(el("span", "obl-title", `Segments proved: ${ed.proved} of ${ed.listed}`), b);
    r.append(h, t);
    box.append(r);
  }
  const rest = p.obligations.filter((o) => !MAIN.includes(o.kind));
  if (rest.length) {
    const more = el("details", "more");
    more.append(el("summary", null, `Supporting obligations (${rest.length})`));
    for (const o of rest) more.append(obligationRow(o, false, true));
    box.append(more);
  }
  for (const t of p.tests) {
    const r = el("div", "obl");
    const h = el("div", "obl-head");
    const [b, i] = info(`${t.record.what || t.kind}. A test of the target, not a proof.`);
    h.append(statusBadge(t.status), el("span", "obl-title", `Test: ${t.id}`), b);
    r.append(h, i);
    box.append(r);
  }
}

function section(id, title) {
  const box = $(id);
  box.replaceChildren();
  const d = el("details", "more");
  d.append(el("summary", null, title));
  box.append(d);
  return d;
}

function drawStages(p) {
  const stages = (p.extra || {}).stages || [];
  const d = section("stages", `Stages (${stages.length})`);
  for (const stage of stages) d.append(stageRow(p, stage));
  if (!stages.length) d.append(el("p", "muted", "No stage recorded."));
}

function stageRow(p, stage) {
  const row = el("div", "stage");
  const evidence = p.obligations.find((obligation) => obligation.id === stage.obligation);
  const trust = stageTrust(p, stage, evidence);
  row.append(el("span", `badge ${trust === "unchecked" ? "st-unchecked" : `trust-${trust}`}`, trust),
    el("span", null, ` ${stage.side}: ${stage.name}`));
  const trace = el("div", "muted", `${stage.input} → ${stage.output}; ${stage.evidence} `);
  appendLinks(trace, [stage.input, stage.output].map((role) => artifactDownload(p, role)));
  if (stage.origin_table) {
    const download = artifactDownload(p, stage.origin_table);
    if (download) appendLinks(trace, [{ ...download, label: "Source origins by preorder node ID" }]);
  }
  if (evidence) appendLinks(trace, evidence.links || []);
  row.append(trace);
  if (stage.output_decl) {
    row.append(stageValue(p, "Input", stage.input_decl, stage.input),
      stageValue(p, "Model", stage.model), stageValue(p, "Output", stage.output_decl, stage.output));
  }
  return row;
}

function stageValue(p, label, decl, role) {
  const hash = p.artifacts[role]?.sha256;
  const value = el("div", "muted stage-value", `${label}: ${decl}`);
  if (hash) {
    const fingerprint = el("code", null, ` · SHA-256 ${hash.slice(0, 12)}…`);
    fingerprint.title = `SHA-256 ${hash}`;
    value.append(fingerprint);
  }
  appendLinks(value, p.definitions.filter((link) => link.label === decl));
  return value;
}

function drawDwarf(p) {
  const facts = (p.extra || {}).dwarf_facts || [];
  const d = section("dwarf", `Debug information → statements (${facts.length})`);
  const extraction = p.extra?.dwarf_extraction;
  if (extraction) {
    const summary = el("p", "muted", `${extraction.tool} · ${extraction.profile}/${extraction.function} · unverified extraction `);
    appendLinks(summary, [artifactDownload(p, extraction.input), artifactDownload(p, extraction.output)]);
    d.append(summary);
  }
  for (const f of facts) {
    const r = el("div", "fact");
    r.append(el("span", "badge st-unchecked", "extracted"), el("span", null, ` ${f.fact}`));
    const use = el("div", "muted", `${f.origin}; used by `);
    for (const dep of f.used_by) {
      const target = document.getElementById(`obligation-${dep}`);
      const button = el(target ? "button" : "span", target ? "ext" : null, dep);
      if (target) button.onclick = () => {
        const details = target.closest("details");
        if (details) details.open = true;
        target.scrollIntoView({ block: "center" });
        target.querySelector("button")?.focus({ preventScroll: true });
      };
      use.append(button, " ");
    }
    use.append(`· ${f.if_wrong}`);
    r.append(use);
    d.append(r);
  }
}

function drawBlocks(p) {
  const blocks = p.extra.blocks || [];
  $("blocks").hidden = !blocks.length;
  if (!blocks.length) return;
  const d = section("blocks", `Block-to-fragment associations (${blocks.length})`);
  d.open = true;
  const range = ([start, end]) => `[0x${start.toString(16)}, 0x${end.toString(16)})`;
  for (const block of blocks) {
    const card = el("div", "stage");
    card.append(el("h3", null, `${block.symbol} · ${block.side} block candidate`),
      el("p", null, `ELF section ${block.section} ${range(block.section_range)} · file bytes ${range(block.file_range)} · model entry 0x${block.model_base.toString(16)} (not a loader result)`),
      el("p", "muted", "Attribution is navigation only. Neither the decoder nor the associations certify a CFG, coverage, local execution, or source equivalence."));
    for (const dep of block.dependencies) {
      const obligation = p.obligations.find((o) => o.id === dep);
      if (obligation) card.append(obligationRow(obligation, false));
    }
    const trace = block.parse_stage;
    if (trace) {
      const stage = (p.extra.stages || []).find((stage) => stage.output === trace.output);
      const evidence = stage && p.obligations.find((obligation) => obligation.id === stage.obligation);
      const trust = stage ? stageTrust(p, stage, evidence) : "unchecked";
      card.append(el("p", "muted", `Opposite-side stage: ${trace.name} · ${trust} · ${trace.input_sha256.slice(0, 12)}… → ${trace.output_sha256.slice(0, 12)}…`));
    }
    const other = block.side === "target" ? "source" : "target";
    const links = el("ul");
    for (const edge of p.edges.filter((e) => block.attribution.includes(e.id))) {
      links.append(el("li", null, `${edge.origin || "recorded association"}: ${edge[other].map((fid) =>
        `${p.fragments[fid].label} (${p.fragments[fid].ranges.map(range).join(", ")})`).join("; ")}`));
    }
    card.append(links);
    appendLinks(card, p.definitions.filter((link) => link.label === block.model_decl || link.label === `${block.model_decl}_shape`));
    if (block.viewer) appendLinks(card, [{ kind: "viewer", label: "Inspect this block in the ELF tab", url: block.viewer }]);
    d.append(card);
  }
}

function drawEnv(p) {
  const env = (p.extra || {}).include_env;
  const d = section("env", "Preprocessor environment");
  if (!env) { d.append(el("p", "muted", "Not recorded.")); return; }
  d.append(el("p", "muted", env.note));
  const compiler = p.derivation?.version || p.derivation?.compiler;
  const provenance = el("p", "muted env-provenance", compiler ? `${compiler} · image ` : "Image ");
  provenance.append(el("code", null, env.image));
  d.append(provenance);
  const table = el("table", "include-files");
  const caption = env.trace
    ? "GCC include trace: direct from the main file, indirect from a header. Repeats are grouped; open a name for ordered occurrences. “Not entered” does not establish why GCC skipped a file."
    : env.dependencies
    ? "Names are path basenames. Directive spelling, direct versus indirect, resolution history, aliases, repeats and guard effects: unknown."
    : "Main file only. No header dependency capture for this build.";
  table.append(el("caption", "muted", caption));
  const heading = table.createTHead().insertRow();
  for (const label of ["Name", "Size (B)", "SHA-256 (short)"]) {
    const head = el("th", null, label);
    head.scope = "col";
    heading.append(head);
  }
  const body = table.createTBody();
  for (const file of includeRows(env)) {
    const row = body.insertRow();
    const name = el("details");
    const label = el("summary", null, file.label + (file.main ? " · main" : ""));
    if (file.kind) label.append(el("span", "muted", ` · ${file.kind}`));
    if (file.events?.length > 1) label.append(el("span", "muted", ` ×${file.events.length}`));
    const resolution = file.path ? `Resolved path: ${file.path}` : "No file entry recorded; resolution unknown";
    const first = file.events?.[0];
    label.title = first?.operand ? `${resolution}\n${first.operand} from ${first.from}:${first.line} (${file.kind})` : resolution;
    name.append(label, el("code", "file-detail", file.path || "Not entered · resolution unknown"));
    for (const event of file.events || []) {
      if (!event.operand) {
        name.append(el("div", "muted", `#${event.index + 1} · implicit compiler entry; no source directive`));
        continue;
      }
      const origin = event.literal ? "literal" : "GCC-reported operand; literal spelling not confirmed";
      const parent = event.parent === null ? "main file" : `inside #${event.parent + 1}`;
      name.append(el("div", "file-detail", `#${event.index + 1} · #${event.directive} ${event.operand} · ` +
        `${event.from}:${event.line} · ${parent} · ${origin}`));
    }
    row.insertCell().append(name);
    row.insertCell().textContent = file.size?.toLocaleString() ?? "—";
    if (!file.sha256) {
      row.insertCell().textContent = "—";
      continue;
    }
    const fingerprint = el("details");
    const short = el("summary");
    short.title = `Full SHA-256: ${file.sha256}`;
    short.append(el("code", null, `${file.sha256.slice(0, 10)}…`));
    const full = el("textarea", "full-hash");
    full.value = file.sha256;
    full.readOnly = true;
    full.rows = 4;
    full.title = "Full fingerprint; press Ctrl+C or Command+C to copy";
    full.setAttribute("aria-label", `Full SHA-256 for ${file.label}`);
    full.onfocus = () => full.select();
    fingerprint.append(short, full);
    row.insertCell().append(fingerprint);
  }
  d.append(table);
  const dl = el("dl");
  const add = (k, v) => dl.append(el("dt", null, k), el("dd", null, v));
  add("search", env.search.join(" → ") || "(none)");
  add("working directory", env.workdir);
  add("macro/search probe flags", env.probe_flags);
  if (env.dependencies) add("dependency probe flags", env.dependencies.flags);
  add("options", env.options.join(" "));
  add("macros", `${p.artifacts[env.macros]?.path || env.macros} (gcc -dM -E)`);
  d.append(dl);
  appendLinks(d, [env.macros, env.search_receipt, env.dependencies?.artifact].filter(Boolean).map((role) => artifactDownload(p, role)));
}

function artifactDownload(p, role) {
  return { ...p.artifact_links[role].find((link) => link.kind === "download"), label: role };
}

function drawProvenance(p) {
  const d = section("provenance", "Provenance");
  const dl = el("dl");
  const add = (k, v) => { if (v !== null && v !== undefined && v !== "") dl.append(el("dt", null, k), el("dd", null, v)); };
  add("direction", p.direction);
  const g = p.derivation || {};
  if (!p.extra?.include_env) {
    add("compiler", g.compiler ? g.version : null);
    add("image", g.image);
  }
  add("decompiler", g.tool);
  add("command", g.command);
  add("origin (a claim)", g.claim);
  for (const [role, a] of Object.entries(p.artifacts)) add(role, `${a.path} · sha256 ${a.sha256} · ${a.size} B`);
  add("manifest", p.manifest_sha256);
  d.append(dl);
  if (p.lean?.bindings?.length) d.append(el("p", "muted", p.bindings_checked ?
    "Displayed C, model data and decoder renderings match the Lean build byte for byte (compiled rendering check)." :
    "The model artifact renderings have not been checked against this Lean build."));
  for (const [key, val] of Object.entries(p.context || {})) {
    const item = el("details", "more");
    item.append(el("summary", null, key.replaceAll("_", " ") + (val ? "" : " · not selected")));
    if (val) {
      item.append(el("p", "muted", `${val.decl} — ${val.version}`));
      appendLinks(item, p.definitions.filter((link) => val.decl.startsWith(link.label)));
    }
    d.append(item);
  }
  if (p.definitions.length) {
    const defs = el("details", "more");
    defs.append(el("summary", null, "Exact Lean inputs, outputs and definitions"));
    for (const link of p.definitions) {
      const item = el("div", "muted", `${link.label} `);
      appendLinks(item, [link]);
      defs.append(item);
    }
    d.append(defs);
  }
}

init().catch((e) => { $("status").textContent = `error: ${e.message}`; });
