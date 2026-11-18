function sqlTabs(on) {
  return '<div class="controls">' + [["sql", "Query"], ["schema", "Schema"], ["about", "About"]].map(([k, t]) =>
    k === on ? `<b>${t}</b>` : `<a href="#/${k}">${t}</a>`).join(" · ") + "</div>";
}
// One line per table and view: what a row is. `sil project` checks (explore.rs tests) that every
// table it writes has an entry here.
const TABLE_DOCS = {
  meta: "Key/value facts about the database: its schema version and how it was written.",
  projects: "The local project and the imported ones (from their silmaril.toml): sid, name, root group.",
  objects: "Every named object and its sid: (kind, name) to sid, the module that declared it, how the sid was made.",
  artifacts: "Registry blobs, keyed by sid and CID (BLAKE3), with SHA-256, Git SHA-1 and size of the exact bytes.",
  artifact_paths: "Where each artifact was found, per package; a path is not an identity.",
  facts: "Tool-tier facts recorded about artifacts (property, value, the checker that computed it).",
  artifact_types: "Artifact types (`ArtifactType` declarations).",
  formats: "Formats: a parser from the input type to the value type, its printer and base format.",
  format_defaults: "Family defaults: a family name and the format it resolves to.",
  format_laws: "Proved laws of a format (round trip, soundness) with the proof's declaration.",
  value_defs: "Named values: a format, the Lean declaration, and the obligation that the bytes parse.",
  value_sources: "The sources of each value: a CID read under a format, and the problem that it parses.",
  specs: "Specs: predicates over a model class and a format.",
  models: "Model classes.",
  rooms: "Rooms: sentences, a category of models and satisfaction (an institution at one signature), or a family of rooms (arity, params); the institution and signature it is a fiber of, when Lean found one.",
  institutions: "Institutions (logic-graph nodes): the Lean declaration of type Inst (or a family, arity > 0), its printed type and universe parameters, provenance, and how it relates to a logic of the pinned Hets logic graph.",
  comorphisms: "Institution comorphisms (logic translations) src → dst between registered institutions, found by Lean from the type Inst.CoHom src dst: sentences forwards, models backwards.",
  morphisms: "Institution morphisms (logic projections) src → dst between registered institutions, from the type Inst.Hom src dst: sentences backwards, models forwards.",
  corridors: "Corridors src → dst between registered rooms (a comorphism at one signature), from the type Corridor src dst: sentences forwards, models backwards.",
  logic_edge_kinds: "The kinds of edge of the logic graph, their level (institution or room) and what moves which way along an edge A → B.",
  logic_facts: "Theorems about logic-graph edges that Lean checked state a known property of the edge (model_expansive, sound), with their axioms.",
  logic_audit: "Every non-theorem declaration in the scanned scope whose type is (a family of) an institution, comorphism, morphism, room or corridor, its arity, module and layer, and the record that registers it (null: omitted from the registry).",
  hets_logics: "The logics of the Hets logic graph at a pinned Hets commit, as Hets lists them (with the CPP flag that guards each).",
  hets_comorphisms: "The comorphisms of the Hets logic graph at a pinned Hets commit, with their source and target logics as Hets names them.",
  logic_pending: "Logic families with Lean developments not in this repository yet: title, institution and map counts, status. Nothing in them is registered or claimed.",
  logic_catalogue: "The curated catalogue the logic-graph port started from (137 logics, 158 maps), entry by entry: status (registered, represented, not institution-typed, prospective), the registered records that hold it, the Lean evidence declarations and the reason.",
  logic_catalogue_summary: "View: catalogue entries per entry kind and status.",
  logic_exclusions: "What the logic graph leaves out: unregistrable declarations with their exact reasons, modules that depend on tool-generated fixtures, and the parts of the source developments outside the institution graph, with counts.",
  presentations: "S-expression presentations of a logic's abstract syntax: the codec's name and version (read by Lean from the codec), its abstract type and whether it is the row's default.",
  logic_properties: "Theorems with a role (soundness, consistency, nontriviality, satisfiability, inclusion), each statement checked by Lean against its role for the registered system, with its axioms.",
  logic_problems: "Concrete problems: a sentence, its S-expression in each registered presentation (computed by Lean), and its claims (derived, entailed, true in a model), each checked by Lean to be about the sentence.",
  logic_rows: "The formal rows: each logic's systems, interpretations, presentations, properties, problems, derivation systems and derivations, with its exact variant.",
  derivation_systems: "Derivation systems: rule instances checked step by step, their judgment presentation and proof formats, and their Lean-checked claims (local soundness, agreement with a consequence system).",
  derivations: "Concrete proofs: the S-expression in each proof format, the indexed steps (rule, judgment, cited lines), and Lean-checked verdicts of the checkers (accepted or rejected, with the stage).",
  logic_edges: "View: every logic-graph edge (comorphism, morphism, corridor) with its level, endpoints and number of facts.",
  logic_nodes: "View: every logic-graph node (institution or room) with its degree.",
  logic_coverage: "View: per audited kind and layer, how many declarations there are, how many are closed, generic (constructions over arbitrary institutions), registered, omitted, and omitted generic constructions.",
  hets_coverage: "View: per Hets logic or comorphism, the registered records that relate to it and how (corresponds, fragment, related).",
  machines: "Finite machine documents: counts, determinism and the canonical JSON (the content identity).",
  machine_bindings: "Typed Lean machines proved equal to a machine document (the theorem names the proof).",
  language_domains: "Language domains: the carrier type of a language (bytes, Unicode strings, numbers, trees), whether it is a monoid and its letters.",
  measures: "Measures on a language domain (byte length, UTF-8 length, depth, …): the Lean function and its codomain.",
  language_interpretations: "Interpretations of artifacts as languages: the Lean definition, its ABI and environment (both occur in the definition).",
  languages: "Languages: domain, construction (op and its fields), the generated or given Lean definition, provenance and the identity of the construction (no display name).",
  language_operands: "The operands of a language's set operation or measure restriction, or the leaves of its regular expression.",
  language_shape_roles: "What each argument of a standard language shape is (the language L, K, a measure, a bound, the sentence x).",
  language_problems: "Instances of the standard language shapes, by the languages their arguments name, with the expected status, summary and verdict.",
  consequence_systems: "Consequence systems (Γ ⊢ φ, a relation from contexts to conclusions): construction (decl, union, inter, diff, erase of a witness system, or artifact: a registered value read through an interpretation), the Lean definition, its term as instance arguments print it, the context and conclusion types, their typed shape (unit/list/finset/set/other, element type, Signed polarity, raw sequent; read by Lean from the types), provenance.",
  consequence_interpretations: "Interpretations of artifacts as consequence systems: the Lean definition (total I : V → System Ax C, or partial I : Interp Env V Ax C under a configuration of type env), the value type it reads, its context and conclusion types (families over env when partial), ABI and environment (both occur in the definition).",
  consequence_matrix_cells: "Cells of an evidence matrix (the protocol track's SignedMatrix): variant, reading, the listed supporting declarations with their modules, and the owner's evidence and strength classifications, verbatim (the registry checked only that the declarations exist).",
  consequence_operands: "The operands of a consequence system built by union, intersection or difference.",
  consequence_shape_roles: "What each argument of a standard consequence shape is (the system S, the system T it is compared with or translated into, the maps f and g, the chosen ff, a context, a conclusion, a type).",
  consequence_problems: "Instances of the standard consequence shapes, by the systems their arguments name (role S or T), with the expected status, summary and verdict.",
  problems: "Problems and groups: the Lean declaration, arity, model/spec, expected status, title and doc.",
  problem_args: "The binders of a problem over arguments, in order.",
  problem_inputs: "Values and CIDs a problem is about.",
  instance_args: "The fixed arguments of an instance problem, as terms, values or CIDs.",
  answers: "Answers: a theorem establishing one SZS status of a problem, with its tier.",
  answer_axioms: "The axioms each answer depends on (checked against the standard ones).",
  edges: "The DAG: group children, decompositions, refutation routes and instance edges, with the proof (`via`).",
  szs: "The SZS status codes used, their names and the verdict each gives.",
  statuses: "Every status a problem has, and how it was obtained (an answer, an edge, a group).",
  summary: "One summary status and verdict (holds/fails/unknown) per problem.",
  deprecations: "Deprecated problems, groups or specs, with the reason.",
  deprecation_replacements: "What supersedes each deprecation.",
  deprecated_problems: "Every problem that is deprecated, directly or through a spec or general problem.",
  findings: "Classifications of failing problems (error, spec_bug, model_gap, unclear).",
  finding_versions: "The affected versions of an `error` finding.",
  expected_open: "Open problems expected to stay open for a metatheoretic reason about Lean's ambient theory (independent, consistency), with a note and a pointer.",
  decl_locations: "Where each Lean declaration the dump names is declared: module, whole range and name range (lines 1-based, columns in codepoints from 0).",
  group_verdicts: "View: each group's children with their summaries and verdicts.",
  deprecated_with_replacements: "View: deprecations with their replacements.",
  genuine_errors: "View: the `error` findings with their problems' titles and summaries.",
  model_gaps: "View: the `model_gap` findings by what is missing.",
  spec_bugs: "View: the `spec_bug` findings and how their problems are deprecated.",
  unclassified_failures: "View: failing problems that are neither deprecated nor classified.",
};
async function schemaPage() {
  const objs = await q("SELECT name, type FROM sqlite_master WHERE type IN ('table','view') AND name NOT LIKE 'sqlite_%' ORDER BY type, name");
  let h = "<h2>Schema</h2>" + sqlTabs("schema") +
    '<p class="muted">Read from this database (<code>pragma_table_info</code>, <code>pragma_index_list</code>); the notes are the page\'s.</p>';
  // No row counts: counting would read whole tables, which a lazily read database avoids.
  h += '<div class="tablebox"><table><thead><tr><th>table</th><th>kind</th><th>note</th></tr></thead><tbody>';
  for (const o of objs) {
    h += `<tr><td><a href="#schema-${esc(o.name)}" onclick="document.getElementById('schema-${esc(o.name)}').scrollIntoView();return false">${esc(o.name)}</a></td>` +
      `<td>${esc(o.type)}</td><td>${esc(TABLE_DOCS[o.name] || "")}</td></tr>`;
  }
  h += "</tbody></table></div>";
  for (const o of objs) {
    const cols = await q(`SELECT name, type, "notnull" AS nn, pk FROM pragma_table_info(?)`, [o.name]);
    const idx = o.type === "table" ? await q(`SELECT name, "unique" AS uq, origin FROM pragma_index_list(?)`, [o.name]) : [];
    h += `<h2 id="schema-${esc(o.name)}"><code>${esc(o.name)}</code> <span class="muted">${esc(o.type)}</span></h2>`;
    if (TABLE_DOCS[o.name]) h += `<p>${esc(TABLE_DOCS[o.name])}</p>`;
    h += await table(cols.map((c) => ({ column: c.name, type: c.type || "", "not null": c.nn ? "yes" : "", key: c.pk ? "primary " + c.pk : "" })),
      ["column", "type", "not null", "key"], { hints: { column: "" } });
    for (const i of idx) {
      const ic = await q("SELECT name FROM pragma_index_info(?) ORDER BY seqno", [i.name]);
      h += `<p class="muted">${i.origin === "pk" ? "primary key" : i.uq ? "unique" : "index"} <code>${esc(i.name)}</code>(${ic.map((c) => esc(c.name)).join(", ")})</p>`;
    }
    h += `<p><a href="#/sql/${encodeURIComponent(`SELECT * FROM ${o.name} LIMIT 50;`)}">query it</a></p>`;
  }
  return h;
}
function aboutPage() {
  return "<h2>About</h2>" + sqlTabs("about") + `<div style="max-width:860px">
<h2>What this page is</h2>
<p>A static view of one <b>silmaril project database</b>, written by <code>sil project sqlite</code> from what
Lean recorded (<code>sil project dump</code>) and what <code>sil project check</code> derived. The page holds no data:
it opens the SQLite file in the browser and runs SQL there. Over HTTP it reads the file lazily (HTTP
Range requests, one SQLite page at a time, cached across reloads per database version) when the
server allows it, and otherwise downloads it whole; the header says which.</p>
<h2>How it is made</h2>
<ol>
<li>Lean modules declare records: TOML records files read by <code>silmaril load</code>, commands and attributes
(<code>@[problem]</code>, <code>@[answers]</code>, <code>silmaril value</code>, …). Lean checks them as it elaborates.</li>
<li><code>sil project dump</code> builds the modules and writes every record (<code>#silmaril_dump</code>).</li>
<li><code>sil project check</code> applies the rules (names, sids, references, provenance, answers and their axioms)
and derives statuses and verdicts; <code>sil project sqlite</code> writes the database; <code>sil project explore</code> this page.</li>
</ol>
<h2>Glossary</h2>
<dl>
<dt>record</dt><dd>one declaration of the project (a value, a problem, a group, a machine, …), with a kind, a name and fields.</dd>
<dt>name</dt><dd>dotted, unique per kind: segments <code>[a-z][a-z0-9_-]*</code> or all digits.</dd>
<dt>sid</dt><dd>a 256-bit identifier (64 hex digits). The project's is random; an object's default sid is
<code>BLAKE3.derive_key("silmaril.sid.v0", kind ‖ 0 ‖ project sid ‖ 0 ‖ name)</code>; an artifact's is its BLAKE3 digest.</dd>
<dt>CID</dt><dd>a blob's content identifier: CIDv1, codec raw, BLAKE3-256 of the exact bytes, base32 (<code>bafkr4i…</code>).</dd>
<dt>artifact</dt><dd>a blob in <code>silmaril/artifacts.toml</code>, keyed by CID; a path is only where it was found.</dd>
<dt>format, value</dt><dd>a named parser from bytes; a value is a named artifact read under a format.</dd>
<dt>problem</dt><dd>a named Lean <code>Prop</code>, or a predicate over arguments (arity n); an instance fixes arguments.</dd>
<dt>answer</dt><dd>a theorem establishing one SZS status of a problem: THM (holds), SAT, UNS, CSA.</dd>
<dt>group, verdict</dt><dd>a DAG node over children; each problem's summary gives a verdict: holds, fails or unknown.</dd>
<dt>tier</dt><dd>how a status or fact is known: <code>kernel</code> (a Lean proof the kernel checked) or
<code>tool</code> (computed by <code>sil project</code>, e.g. digests and sizes).</dd>
<dt>machine</dt><dd>a finite machine document (states, labels, edges, layers) and the typed Lean machines bound to it.</dd>
</dl>
<h2>Using it</h2>
<ul>
<li>Tabs list problems, artifacts, values, formats and machines; names link to their pages; Graph draws the DAG.</li>
<li>Query runs any read-only SQL; prefer a <code>LIMIT</code> and indexed columns when the file is read lazily.
Schema lists every table, its columns, keys and indexes.</li>
<li><code>?db=&lt;url&gt;</code> opens another database; <code>?load=full</code> downloads it whole;
<code>?cache=off</code> skips the page cache.</li>
<li>Locally: <code>sil project dump</code>, <code>check</code>, <code>sqlite --httpvfs</code>, <code>explore</code>, then serve
<code>.lake/silmaril</code> over HTTP (e.g. <code>npx http-server</code>) and open <code>explore.html</code>.</li>
</ul></div>`;
}

const EXAMPLES = {
  "tables": "SELECT name, type FROM sqlite_master WHERE type IN ('table','view') ORDER BY name;",
  "problems with their verdict": "SELECT p.name, p.kind, s.summary, s.verdict FROM problems p LEFT JOIN summary s ON s.problem = p.name ORDER BY s.verdict, p.name LIMIT 200;",
  "statuses by SZS code": "SELECT st.status, z.verdict AS szs_verdict, count(*) AS n FROM statuses st LEFT JOIN szs z ON z.code = st.status GROUP BY 1, 2;",
  "proved edges": "SELECT parent, child, kind, via FROM edges WHERE via IS NOT NULL LIMIT 200;",
  "axioms used by answers": "SELECT axiom, count(*) AS answers FROM answer_axioms GROUP BY axiom ORDER BY 2 DESC;",
  "values and their files": "SELECT v.name, s.format, s.cid, ap.path FROM value_defs v JOIN value_sources s ON s.value = v.name JOIN artifacts a ON a.cid = s.cid LEFT JOIN artifact_paths ap ON ap.artifact = a.sid LIMIT 200;",
};
let lastSql = EXAMPLES["tables"];
function sqlPage(arg) {
  if (arg) lastSql = arg;
  const html = '<h2>SQL</h2>' + sqlTabs("sql") + '<div class="controls"><select id="ex"><option value="">examples…</option>' +
    Object.keys(EXAMPLES).map((k) => `<option>${esc(k)}</option>`).join("") +
    '</select><button id="run">Run (Ctrl+Enter)</button><span class="muted">results link known names. ' +
    "Over HTTP the database is read lazily: a query reads only the pages it touches, so prefer a LIMIT and indexed columns.</span></div>" +
    '<textarea id="sqltext" spellcheck="false"></textarea><div id="sqlout"></div>';
  const init = async () => {
    const ta = $("#sqltext"); ta.value = lastSql;
    const run = async () => {
      lastSql = ta.value;
      $("#sqlout").innerHTML = '<p class="muted">running…</p>';
      try {
        const res = await dbExec(ta.value);
        let h = "";
        for (const r of res) h += `<p class="muted">${r.values.length} rows</p>` +
          await table(r.values.map((row) => Object.fromEntries(r.columns.map((c, i) => [c, row[i]]))), r.columns, { all: true });
        $("#sqlout").innerHTML = h || '<p class="muted">no result set</p>';
      } catch (e) { $("#sqlout").innerHTML = `<p class="err">${esc(e.message || e)}</p>`; }
      updateStats();
    };
    $("#run").addEventListener("click", run);
    ta.addEventListener("keydown", (e) => { if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) { e.preventDefault(); run(); } });
    $("#ex").addEventListener("change", (e) => { if (EXAMPLES[e.target.value]) { ta.value = EXAMPLES[e.target.value]; run(); } });
    await run();
  };
  return { html, init };
}

// ---------- graph ----------

registerView({ id: "sql", title: "SQL", nav: 90, render: sqlPage });
registerView({ id: "schema", title: "Schema", tab: "sql", render: schemaPage });
registerView({ id: "about", title: "About", tab: "sql", render: aboutPage });
