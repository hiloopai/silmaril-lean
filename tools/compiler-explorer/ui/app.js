// The compiler explorer's page. Every text from the database is inserted with textContent.
import { lineOffsets, indexEdges, edgeObligations, badge, uncovered } from "./view.js";

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

const state = { list: [], problem: null, index: null, locked: null, mode: "navigation" };

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
  const want = new URLSearchParams(location.search).get("problem");
  if (want && state.list.some((p) => p.id === want)) prog.value = groupOf(want);
  prog.onchange = () => { fillBuilds(); load($("build").value); };
  $("build").onchange = () => load($("build").value);
  $("mode").onchange = () => { state.mode = $("mode").value; render(); };
  const mode = new URLSearchParams(location.search).get("mode");
  if (mode === "semantic" || mode === "navigation") { state.mode = mode; $("mode").value = mode; }
  fillBuilds(want);
  await load($("build").value);
}

function fillBuilds(want) {
  const b = $("build");
  b.replaceChildren();
  for (const p of state.list.filter((q) => groupOf(q.id) === $("program").value)) {
    const d = p.derivation || {};
    const how = d.compiler ? `${d.compiler} ${(d.version || "").replace(/^.*\) /, "")} -${d.opt || "?"}` : (d.kind || p.direction);
    b.append(new Option(`${p.direction}: ${how} — ${p.id.split("/").slice(2).join("/") || p.id}`, p.id));
  }
  if (want && [...b.options].some((o) => o.value === want)) b.value = want;
}

let loadGeneration = 0;
async function load(id) {
  const generation = ++loadGeneration;
  const problem = await getJSON(state.list.find(p => p.id === id)?.static_path || ("api/problems/" + encodeURIComponent(id)));
  if (generation !== loadGeneration) return;
  state.problem = problem;
  state.locked = null;
  render();
}

function render() {
  const p = state.problem;
  const srcText = p.texts.source ?? "(the source is not text)";
  const tgtText = p.texts.target ?? "(the target is not displayable text)";
  const srcLines = lineOffsets(srcText), tgtLines = lineOffsets(tgtText);
  state.index = indexEdges(p, state.mode, srcLines, tgtLines);
  const colorOf = new Map();
  p.edges.filter((e) => e.kind === state.mode).forEach((e, i) => colorOf.set(e.id, i % COLORS));
  state.colorOf = colorOf;
  $("src-title").textContent = `Source · ${p.artifacts[p.view.source].path}`;
  $("tgt-title").textContent = `Target · ${p.artifacts[p.view.target].path}`;
  drawCode($("src"), "source", srcText);
  drawCode($("tgt"), "target", tgtText);
  drawQuestions(p);
  drawProvenance(p);
  drawAssumptions(p);
  const nEdges = p.edges.filter((e) => e.kind === state.mode).length;
  const isCode = (n) => /\S/.test(srcText.split("\n")[n - 1] || "") && !/^\s*(\/\*|\*|#|\/\/|[{}]\s*$)/.test(srcText.split("\n")[n - 1]);
  const none = uncovered(state.index, "source", srcLines.length, isCode);
  $("status").textContent = `${nEdges} ${state.mode} link(s). Source lines with code but no ${state.mode} link: ${none.length ? none.join(", ") : "none"}. Manifest ${p.manifest_sha256.slice(0, 12)}…, context ${p.context_hash.slice(0, 12)}…`;
  if (state.mode === "semantic" && nEdges === 0) {
    $("selection").replaceChildren(el("h2", null, "Selection"), el("p", "warn", "No semantic links: no Lean statement relates this source and target. The debug-info links remain available."));
  } else {
    showSelection(null);
  }
}

function drawCode(box, side, text) {
  box.replaceChildren();
  text.split("\n").forEach((line, i) => {
    const n = i + 1;
    const row = el("div", "line");
    row.dataset.side = side;
    row.dataset.n = n;
    const ids = state.index.byLine[side].get(n) || [];
    if (ids.length) {
      row.classList.add("linked", `c${state.colorOf.get(ids[0])}`);
      if (ids.length > 1) row.classList.add("multi");
    }
    row.append(el("span", "ln", n), el("span", "tx", line || " "));
    row.onmouseenter = () => { if (!state.locked) highlight(ids); };
    row.onclick = () => {
      state.locked = state.locked && state.locked.join() === ids.join() ? null : ids;
      highlight(ids);
    };
    box.append(row);
  });
}

function highlight(ids) {
  document.querySelectorAll(".line.hl").forEach((r) => r.classList.remove("hl"));
  for (const id of ids) {
    const l = state.index.edgeLines.get(id);
    for (const side of ["source", "target"]) {
      for (const n of l[side]) {
        const r = document.querySelector(`.line[data-side="${side}"][data-n="${n}"]`);
        if (r) r.classList.add("hl");
      }
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

function showSelection(ids) {
  const box = $("selection");
  box.replaceChildren(el("h2", null, "Selection"));
  if (!ids || !ids.length) {
    box.append(el("p", "muted", state.mode === "navigation"
      ? "Navigation links come from the compiler's debug information or the decompiler's input block: they say where code came from, not that it is correct."
      : "Semantic links are program points of a Lean correspondence; each has its own obligations."));
    return;
  }
  const p = state.problem;
  for (const id of ids) {
    const e = p.edges.find((x) => x.id === id);
    const card = el("div", "edge");
    card.append(el("div", "edge-id", `${e.kind} · ${e.id}`));
    const frag = (fid) => p.fragments[fid]?.label || fid;
    card.append(el("div", null, `source: ${e.source.map(frag).join("; ")}`));
    card.append(el("div", null, `target: ${e.target.map(frag).join("; ")}`));
    card.append(el("div", "muted", `fragment ids: ${[...e.source, ...e.target].join(", ")} (content addresses)`));
    if (e.origin) card.append(el("div", "muted", `origin: ${e.origin}`));
    if (e.note) card.append(el("div", "warn", e.note));
    if (e.kind === "semantic") {
      card.append(el("div", "muted", `program point ${e.point} (${e.point_kind}); the target fragment is where the segment starts, laid out up to the next point. The proved statement is about the run, which may jump.`));
      for (const o of edgeObligations(p, id)) card.append(obligationRow(o));
    } else {
      card.append(el("div", "muted", "navigation only: no obligation"));
    }
    box.append(card);
  }
}

function obligationRow(o) {
  const row = el("div", "obl");
  const head = el("div", "obl-head");
  head.append(statusBadge(o.status), el("span", "obl-id", o.id));
  row.append(head);
  if (o.statement) row.append(el("code", "stmt", o.statement));
  if (o.reason) row.append(el("div", "muted", o.reason));
  if (o.decl) row.append(el("div", "muted", `proof: ${o.decl}`));
  if (o.row) row.append(el("div", "muted", `sil project row: ${o.row}`));
  if (o.evidence) {
    const ev = o.evidence;
    row.append(el("div", "muted", `evidence: ${{ "exporter-run": "exporter run by this database", "sil-project": `sil project row ${ev.row}`, file: "file handed in (a claim)" }[ev.origin] || ev.origin} (${ev.export_status}), axioms ${ev.axioms.join(", ") || "none"}, Lean ${ev.lean_version}, commit ${ev.git_commit.slice(0, 10)}`));
    if (ev.detail) row.append(el("div", "warn", ev.detail));
  }
  if (o.status === "stale") row.append(el("div", "warn", `proved for manifest ${o.older_manifest.slice(0, 12)}…, not for these artifacts`));
  return row;
}

const QUESTIONS = [
  ["translation", "Translation: target refines source, from safe source states",
    "From every related entry whose source state is safe (no source run from it reaches undefined behaviour, and every source run from it is finite), every target run is safe and finite, stops only at a final state, and returns a result that some source run produces. It says nothing about entries from which some source run has undefined behaviour or diverges. No mapping is involved."],
  ["nonvacuity", "Not vacuous",
    "Some related entry has a safe source state. Without it, a refinement could hold because nothing is related. This is one entry (canonical arguments, empty caller), not every entry: safety from every Core entry is a separate, open obligation."],
  ["abi", "ABI entry exists",
    "For every argument tuple, a System V entry state of the placed code exists (existence only). The return-side conditions of every execution (callee-saved registers, writes only in the frame, the value in rax) are part of the translation."],
  ["mapping", "Whole mapping",
    "Every segment is simulated, including points nobody listed. Individually proved links do not imply this."],
  ["refinement", "Refines the location relation",
    "At every point, the mapping's relation implies the relation the location semi-comorphism generates: each C object with a value has a value it holds in Core and its frame slot holds on the machine. Independent of the segments. The slot offsets come from c-tv's reading of DWARF, which is not verified."],
];

const DECOMPILATION = ["decompilation", "Decompiled block (machine → C0)",
  "The decompiler's summary of the block before ret is accepted by its checker; its rax expression prints as exactly this C text; and from every state where the block is loaded and entered, the machine reaches a state whose rax is the C0 value of that expression's typed Ail. The C text is printed from the expression, not parsed back; ret and the calling convention are outside the block; C0 is the repository's C subset interpreter."];

const TRUST = {
  "decompiled-word-block": [
    ["kernel", "the decompilation obligation, for exactly these block bytes and this C text (WordC.checked_output_c0 instantiated)"],
    ["tool check", "the block bytes are the object's .text at the receipt's range: read from the ELF file by the database, not by the kernel"],
    ["printing only", "the C text is the printing of the generated expression; nothing parses it back into Cerberus or C0"],
    ["not replayed by default", "the exporter reads theorem types from .olean files; tools/compiler-explorer/replay.sh replays the key modules with leanchecker"],
  ],
  "c-function-x86": [
    ["kernel", "every obligation shown proved: a theorem of exactly that statement, standard axioms, read from the Lean build by the exporter that this database ran"],
    ["kernel", "the function's bytes are the registered object's code at its symbol (artifact obligation)"],
    ["evaluation", "C text → typed Ail: the Lean frontend checked by #guard (compiled evaluation), not by the kernel"],
    ["unverified", "the line table and the DWARF slot offsets: read by tools/c-tv (gimli); a wrong offset makes a goal unprovable or the location relation about other bytes"],
    ["recorded", "compiler, version, image digest and command: a receipt with hashes, reproducible, not verified"],
    ["trusted", "the semantics themselves: the Lean port of Cerberus Core and the x86-64 model (Silmaril.X86.Open.isa)"],
    ["not replayed", "the exporter reads theorem types from .olean files; their proofs were checked when Lake built them, not again here"],
  ],
};

function drawQuestions(p) {
  const box = $("questions");
  box.replaceChildren(el("h2", null, "Questions"));
  const dq = p.questions.decompilation;
  if (dq) {
    const card = el("div", "q");
    const head = el("div", "q-head");
    head.append(statusBadge(dq.status), el("strong", null, DECOMPILATION[1]));
    card.append(head, el("div", "muted", DECOMPILATION[2]), obligationRow(dq));
    box.append(card);
  }
  const generic = {
    translation: "Does the target refine the source (backward, from safe source states)?",
    nonvacuity: "Is some related entry safe on the source side?",
    abi: "Does an entry state of the calling convention exist?",
    mapping: "Is every segment of a semantic mapping valid?",
    refinement: "Does a mapping refine a comorphism-generated relation?",
  };
  for (const [k, title0, text0] of QUESTIONS) {
    const c = p.family === "c-function-x86";
    const title = c ? title0 : title0.split(":")[0];
    const text = c ? text0 : generic[k];
    const o = p.questions[k];
    const card = el("div", "q");
    const head = el("div", "q-head");
    head.append(statusBadge(o ? o.status : "unsupported"), el("strong", null, title));
    card.append(head, el("div", "muted", text));
    if (o) card.append(obligationRow(o));
    box.append(card);
  }
  const trust = TRUST[p.family];
  if (trust) {
    const t = el("details", "q");
    t.append(el("summary", null, "What each link rests on"));
    const ul = el("ul");
    for (const [kind, text] of trust) {
      const li = el("li");
      li.append(el("strong", null, `${kind}: `), document.createTextNode(text));
      ul.append(li);
    }
    t.append(ul);
    box.append(t);
  }
  const ed = p.questions.edges;
  const card = el("div", "q");
  card.append(el("div", "q-head", `Links with a proved segment: ${ed.proved} of ${ed.listed} listed`), el("div", "muted", ed.note));
  box.append(card);
  const rest = p.obligations.filter((o) => !["edge", "point", "decompilation", ...QUESTIONS.map((q) => q[0])].includes(o.kind));
  if (rest.length) {
    const more = el("details", "q");
    more.append(el("summary", null, "Other obligations (elaboration, artifact identity, non-vacuity)"));
    for (const o of rest) more.append(obligationRow(o));
    box.append(more);
  }
  for (const t of p.tests) {
    const card = el("div", "q");
    const head = el("div", "q-head");
    head.append(statusBadge(t.status), el("strong", null, `Test: ${t.id}`));
    card.append(head, el("div", "muted", `${t.record.what || t.kind}. A test of the target, not a proof of anything.`));
    if (t.record.stdout !== undefined) card.append(el("div", "muted", "output:"), el("pre", "out", t.record.stdout));
    if (t.record.expected_stdout !== undefined && t.record.expected_stdout !== t.record.stdout) {
      card.append(el("div", "warn", "expected:"), el("pre", "out", t.record.expected_stdout));
    }
    box.append(card);
  }
}

function drawProvenance(p) {
  const box = $("provenance");
  box.replaceChildren(el("h2", null, "Provenance"));
  const dl = el("dl");
  const add = (k, v) => { if (v !== null && v !== undefined && v !== "") { dl.append(el("dt", null, k), el("dd", null, v)); } };
  add("direction", p.direction);
  const d = p.derivation || {};
  add("compiler", d.compiler ? d.version : null);
  add("decompiler", d.tool);
  add("decompiler version", d.tool ? `${d.version} at commit ${d.commit}` : null);
  add("SemLift.check accepted the block", d.checked_by_SemLift_check === undefined ? null : String(d.checked_by_SemLift_check));
  add("origin (a claim, not checked)", d.claim);
  add("image", d.image);
  add("command", d.command);
  for (const [role, a] of Object.entries(p.artifacts)) add(`artifact: ${role}`, `${a.path} · sha256 ${a.sha256} · ${a.size} bytes`);
  for (const [k, v] of Object.entries(p.context || {})) add(k.replace("_", " "), v ? `${v.decl} — ${v.version}` : "none");
  add("Lean modules", (p.lean.modules || []).join(", ") || "none");
  add("manifest", p.manifest_sha256);
  add("context hash", p.context_hash);
  add("versions", `${p.versions.length} (evidence never carries across versions)`);
  box.append(dl);
}

function drawAssumptions(p) {
  const box = $("assumptions");
  box.replaceChildren(el("h2", null, "Assumptions and limits"));
  const ul = el("ul");
  const items = p.family === "c-function-x86" ? [
    "Source undefined behaviour permits any target behaviour: every statement assumes the Core run is safe.",
    "Divergence is not covered: safety includes termination of every Core run.",
    "Nondeterminism of Core (unsequenced operands) is handled by an existential over Core runs.",
    "No I/O, calls, globals, pointers or floating point: the C elaborator's fragment of integer leaves.",
    "One deterministic x86-64 thread (Silmaril.X86.Open.isa); no concurrency or memory model.",
    "C text → typed Ail is checked by evaluation (#guard), not by the kernel; Core is the Lean port's.",
    "The translation is proved for safe entries; that some entry is safe is a separate obligation (non-vacuity), open for every entry, proved for canonical ones.",
  ] : [
    "No Lean statement relates these artifacts: only the compiler's debug information and execution tests are shown.",
    "Debug-info links describe provenance of code, not its correctness.",
  ];
  for (const t of items) ul.append(el("li", null, t));
  box.append(ul);
}

init().catch((e) => { $("status").textContent = `error: ${e.message}`; });
