// The Systems view (docs/projects/consequence-systems.md): the registered consequence systems
// (Γ ⊢ φ, relations from contexts to conclusions), how each is built, and one page per system
// with the standard consequence problems about it, their outcomes, what each outcome means and
// the Lean answers (with their witnesses) that establish it.
//   #/systems                 every system, and what the standard questions mean
//   #/system/<name>           one system
// It reads the database only. A problem with no answer is unknown, never false; universality,
// context-universality and deriving a chosen ff are three different properties and are always
// named as such. A database without the consequence tables gets a notice instead of an error.
(() => {
  const ui = Explorer.ui;
  const LIMIT = 300;
  const PREFIX = "silmaril.shapes.consequence.";
  const SHAPE = (s) => (s || "").startsWith(PREFIX) ? s.slice(PREFIX.length) : s || "";
  const has = () => Explorer.tables().has("consequence_systems");
  const missing = `<p class="muted">This database has no consequence-system tables (built by an older <code>sil project</code>).</p>`;
  const code = (s) => s == null || s === "" ? "" : `<code>${ui.esc(s)}</code>`;
  // A Lean term, compact: qualified names keep their last two components (the full term is the
  // title, and the SQL tab has it too); keyword escapes «…» are dropped from the display only.
  const compactText = (t) => String(t).replace(/«([^»]*)»/g, "$1")
    .replace(/(?:[A-Za-z_][\w']*\.)+([A-Za-z_][\w']*\.[A-Za-z_][\w'!?]*)/g, "$1");
  const term = (t) => t == null || t === "" ? "" : `<code title="${ui.esc(t)}">${ui.esc(compactText(t))}</code>`;
  // A system's name relative to `base` (the namespace of the page's system), for readings.
  const rel = (n, base) => base && n.startsWith(base) && n.length > base.length ? n.slice(base.length) : n;
  const sysLink = (n) => `<a href="#/system/${encodeURIComponent(n)}">${ui.esc(n)}</a>`;

  // What each status means, by shape and by the arguments left free (`Silmaril.Project.Shapes.
  // Consequence.Thms` proves these readings). `{S}`, `{T}`, `{ctx}`, `{phi}`, `{ff}`, `{f}`, `{g}`
  // are the instance's arguments. A closed refutation is stored as UNS and reads as false.
  const READING = {
    derives: {
      "ctx phi": { THM: "{S} is universal: every context derives every conclusion", SAT: "{S} derives something",
        UNS: "{S} is empty: it derives nothing", CSA: "{S} is not universal", contingent: "{S} derives something, and is not universal" },
      phi: { THM: "{ctx} is context-universal in {S}: it derives every conclusion", SAT: "{ctx} derives something in {S}",
        UNS: "{ctx} derives nothing in {S}", CSA: "{ctx} does not derive every conclusion in {S}", contingent: "{ctx} derives some conclusions in {S}, not all" },
      ctx: { THM: "every context derives {phi} in {S}", SAT: "some context derives {phi} in {S}",
        UNS: "no context derives {phi} in {S}", CSA: "some context does not derive {phi} in {S}", contingent: "some contexts derive {phi} in {S}, some do not" },
      "": { THM: "{ctx} ⊢ {phi} holds in {S}", CSA: "{ctx} ⊢ {phi} does not hold in {S}" },
    },
    context_universal: {
      ctx: { THM: "every context derives every conclusion in {S} (universal)", SAT: "some context is context-universal in {S}",
        UNS: "no context is context-universal in {S}", CSA: "some context is not context-universal in {S}",
        contingent: "some contexts are context-universal in {S}, some are not" },
      "": { THM: "{ctx} is context-universal in {S}: it derives every conclusion", CSA: "{ctx} does not derive every conclusion in {S}" },
    },
    derives_bottom: {
      ctx: { THM: "every context derives {ff} in {S}", SAT: "some context derives {ff} in {S}",
        UNS: "no context derives {ff} in {S}", CSA: "some context does not derive {ff} in {S}",
        contingent: "some contexts derive {ff} in {S}, some do not" },
      "": { THM: "{ctx} derives {ff} in {S}", CSA: "{ctx} does not derive {ff} in {S}" },
    },
    sound_at: {
      "ctx phi": { THM: "{S} is sound for {T}: every consequence of {S} is one of {T}", CSA: "{S} is not sound for {T}: a counterexample" },
      "": { THM: "if {ctx} ⊢ {phi} in {S}, then in {T}", CSA: "{ctx} ⊢ {phi} in {S} but not in {T}" },
    },
    complete_at: {
      "ctx phi": { THM: "{S} is complete for {T}: every consequence of {T} is one of {S}", CSA: "{S} is not complete for {T}: a counterexample" },
      "": { THM: "if {ctx} ⊢ {phi} in {T}, then in {S}", CSA: "{ctx} ⊢ {phi} in {T} but not in {S}" },
    },
    complete_within_at: {
      "ctx phi": { THM: "{S} is complete for {T} on the pairs with {mu} ≤ {b}", CSA: "a pair within {mu} ≤ {b} is in {T} and not in {S}" },
    },
    gentzen_closed: {
      "": { THM: "{S} is closed under the Gentzen rules {rules}", CSA: "{S} is not closed under {rules}" },
    },
    ...Object.fromEntries(["context_free", "conclusion_free", "supported_ax", "supported_c", "ctx_perm_inv", "ctx_set_inv", "ctx_up_closed", "ctx_append_extensive"]
      .map((k) => [k, { "": { THM: `{S} is ${({ context_free: "context-free", conclusion_free: "conclusion-free", supported_ax: "supported at the context {tt}",
        supported_c: "supported at the conclusion {ff}", ctx_perm_inv: "invariant under permuting contexts", ctx_set_inv: "reads contexts as sets",
        ctx_up_closed: "closed under weakening contexts (⊆)", ctx_append_extensive: "closed under appending to contexts" })[k]}`,
        CSA: "{S} is not: a counterexample" } }])),
    translates_at: {
      "ctx phi": { THM: "({f}, {g}) preserves consequence from {S} to {T}", CSA: "({f}, {g}) does not preserve consequence from {S} to {T}: a counterexample" },
    },
    reflects_at: {
      "ctx phi": { THM: "({f}, {g}) reflects consequence from {T} back to {S}", CSA: "({f}, {g}) does not reflect consequence from {T} to {S}: a counterexample" },
    },
  };
  // The argument roles of each shape that a reading can leave free.
  const FREE_ROLES = ["ctx", "phi"];

  // A problem row as the shared status API reads it: its summary (no answer is OPN, unknown, never
  // false), expectation, arity and its established statuses (the `statuses` table, with the
  // arity-0 closure THM ⇒ SAT, UNS ⇒ CSA), so that expectations are compared as the checker does.
  const statusOfRow = (p) => ({ summary: p.summary || "OPN", verdict: p.verdict || "unknown", expect: p.expect || null,
    arity: p.arity, established: p.established ? p.established.split(",") : [], deprecated: p.deprecated ? "self" : null });
  const outcome = (p) => ui.statusBadge(statusOfRow(p));
  // The established statuses of a problem, as a comma-separated list (SQL).
  const ESTABLISHED = "(SELECT group_concat(st.status, ',') FROM statuses st WHERE st.problem = p.name) AS established";

  function fill(t, args) {
    return t.replace(/\{(S|T|ctx|phi|ff|f|g|mu|b|rules|tt)\}/g, (_, k) => args[k] || ({ S: "S", T: "T", ctx: "Γ", phi: "φ", ff: "ff", f: "f", g: "g", mu: "μ", b: "b", rules: "rs", tt: "tt" })[k]);
  }
  function reading(p, args) {
    const sh = READING[SHAPE(p.shape)];
    if (!sh) return "";
    const free = FREE_ROLES.filter((r) => (p.roles || []).includes(r) && !(r in args)).join(" ");
    const r = sh[free];
    // a closed refutation is stored as UNS (refuted at arity 0): the statement is false
    const s = p.arity === 0 && p.summary === "UNS" ? "CSA" : p.summary;
    return r && r[s] ? fill(r[s], args) : "";
  }

  // The fixed arguments of the given instances, by problem: role -> display text (a system by
  // its registered name, anything else by its Lean term), and the roles of each shape.
  async function argsOf(ctx, problems) {
    const out = new Map();
    if (!problems.length) return out;
    const marks = problems.map(() => "?").join(",");
    const rows = await ctx.q(
      "SELECT i.problem, r.role, i.term, c.name AS system FROM instance_args i " +
      "JOIN edges e ON e.child = i.problem AND e.kind = 'instance' " +
      "JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos " +
      "LEFT JOIN consequence_systems c ON c.term = i.term " +
      `WHERE i.problem IN (${marks}) AND r.role <> 'type' LIMIT 5000`, problems);
    for (const r of rows) {
      if (!out.has(r.problem)) out.set(r.problem, {});
      out.get(r.problem)[r.role] = { text: r.system || r.term, system: r.system };
    }
    return out;
  }

  // Expectations, apart from truth (ui.expectationSummary): met, unexpected, not established, or
  // without an expectation. "All met" needs every problem to have an expectation that is met; an
  // unknown or unset one never counts as met. This counts expectations; it is not a statement
  // about the problems, nor a proof of their conjunction.
  const summarize = (list) => ui.expectationSummary(list.map(statusOfRow));
  function expectations(list) {
    const n = summarize(list), bad = n.mismatch + n.error;
    const parts = [`${n.met} of ${n.total} expected statuses met`];
    if (n.pending) parts.push(`${n.pending} not established yet`);
    if (n.unset) parts.push(`${n.unset} without an expected status`);
    if (bad) parts.push(`<b>${bad} unexpected</b>`);
    return `<p class="expectations" data-all-met="${n.allMet}">${n.allMet ? "All " : ""}${parts.join(", ")}` +
      `<span class="muted"> — whether the project's expectations hold, not whether the statements are true: an expected
refutation that is refuted counts as met.</span></p>`;
  }

  // The views of the index: each a test on the typed shape Lean recorded (never on printed
  // types), on the construction, or on an established certification.
  const VIEWS = [
    ["all", "all", () => true],
    ["artifact", "artifacts", (r) => r.op === "artifact"],
    ["acceptor", "acceptors (unit contexts)", (r) => r.ctx_kind === "unit"],
    ["rejector", "rejectors (unit conclusions)", (r) => r.concl_kind === "unit"],
    ["list", "list contexts", (r) => r.ctx_kind === "list"],
    ["finset", "finset contexts", (r) => r.ctx_kind === "finset"],
    ["set", "set contexts", (r) => r.ctx_kind === "set"],
    ["multi", "multiple conclusions", (r) => r.concl_kind === "list"],
    ["partial", "partial interpretations", (r) => r.definedness === "partial"],
    ["signed", "signed formulas", (r) => !!(r.ctx_signed || r.concl_signed)],
    ["raw-sequent", "raw sequents", (r) => !!r.raw_sequent],
    ["gentzen", "Gentzen-closed (certified)", (r, g) => g.has(r.name)],
  ];
  // Whether a table has a column (an older database may lack it).
  const columnCache = new Map();
  async function hasColumn(ctx, table, col) {
    const k = table + "." + col;
    if (!columnCache.has(k)) {
      columnCache.set(k, Explorer.tables().has(table) &&
        (await ctx.q("SELECT count(*) AS n FROM pragma_table_info(?) WHERE name = ?", [table, col]))[0].n > 0);
    }
    return columnCache.get(k);
  }
  // The definedness certificates of a system read through a partial interpretation: every
  // `artifact_defined` problem about its value, with its interpretation and configuration, and
  // what can be said. Positive evidence only: no certificate means "not certified", a refutation
  // without decode evidence means "undefined or undecodable", and "defined, empty" needs both a
  // definedness certificate and established emptiness (derives UNS over all Γ, φ).
  async function definednessRows(c, ctx, isProved) {
    const [ci] = await ctx.q("SELECT decl FROM consequence_interpretations WHERE name = ? LIMIT 1", [c.interpretation]);
    const all = await ctx.q(
      "SELECT i.problem, s.summary, s.verdict, p.arity, p.expect, " +
      "(SELECT a.term FROM instance_args a JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = a.pos WHERE a.problem = i.problem AND r.role = 'I') AS interp, " +
      "(SELECT a.term FROM instance_args a JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = a.pos WHERE a.problem = i.problem AND r.role = 'e') AS env " +
      "FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' AND e.parent = ? " +
      "JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos AND r.role = 'X' " +
      "JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem WHERE i.value = ? ORDER BY i.problem LIMIT 50",
      [PREFIX + "artifact_defined", c.value]);
    // this system's certificates: the same interpretation, at the same configuration
    const ps = all.filter((p) => ci && p.interp === ci.decl && (p.env === c.env_term || (!c.env_term && p.env === "PUnit.unit")));
    const [empty] = await ctx.q("SELECT cp.problem FROM consequence_problems cp JOIN problems p ON p.name = cp.problem " +
      "WHERE cp.system = ? AND cp.role = 'S' AND cp.shape = ? AND p.arity = 2 AND cp.summary = 'UNS' LIMIT 1", [c.name, PREFIX + "derives"]);
    const label = (p) => p.summary === "THM" ? (empty ? `defined, empty (certified with ${ui.link("problem", empty.problem)})` : "defined (certified)")
      : p.summary === "UNS" || p.summary === "CSA" ? (isProved ? "undefined: the bytes decode (proved .is or .parses) but the reading is undefined" : "undefined or undecodable")
      : "not certified (no answer)";
    if (!ps.length) return [["definedness", '<span class="muted">not certified: no <code>artifact_defined</code> problem names this value</span>']];
    return [["definedness", ps.map((p) => `${ui.link("problem", p.problem)} ${ui.statusBadge({ summary: p.summary || "OPN", verdict: p.verdict || "unknown", arity: p.arity, expect: p.expect || null })}` +
      ` <b>${label(p)}</b> <span class="muted">— ${term(p.interp)} at ${term(p.env)}</span>`).join("<br>")]];
  }

  // One side of a system's typed shape: kind, element type, polarity.
  const side = (k, e, sg) => k == null ? "" : `${ui.esc(k)}${k === "other" || k === "unit" ? "" : " of"} ${k === "unit" ? "" : term(e)}${sg ? ' <span class="pill">signed</span>' : ""}`;
  const shapeText = (r) => r.ctx_kind == null ? '<span class="muted">not recorded</span>'
    : `${side(r.ctx_kind, r.ctx_elem, r.ctx_signed)} → ${side(r.concl_kind, r.concl_elem, r.concl_signed)}${r.raw_sequent ? ' <span class="pill">raw sequent</span>' : ""}`;
  // The Gentzen certifications: system -> [{ rules, summary, problem }] from gentzen_closed problems.
  async function gentzenOf(ctx) {
    const out = new Map();
    const rows = await ctx.q("SELECT cp.system, cp.problem, cp.summary, " +
      "(SELECT i.term FROM instance_args i JOIN consequence_shape_roles r ON r.shape = cp.shape AND r.pos = i.pos WHERE i.problem = cp.problem AND r.role = 'rules') AS rules " +
      "FROM consequence_problems cp WHERE cp.shape = ? AND cp.role = 'S' LIMIT 5000", [PREFIX + "gentzen_closed"]);
    for (const r of rows) { if (!out.has(r.system)) out.set(r.system, []); out.get(r.system).push(r); }
    return out;
  }

  // Relations between systems stated as problems: soundness, completeness (also within a
  // bound), translations, and Gentzen closure. Each with both systems, the other fixed arguments
  // (measure, bound, maps, rule profile) and where it stands: established (the universal or
  // closed statement is proved), counterevidence (a counterexample or refutation, kept),
  // partial (only an instance, SAT), or unknown. A SAT answer is never shown as established.
  const SHAPE_EVIDENCE = { context_free: "context-free", conclusion_free: "conclusion-free", supported_ax: "supported at the context {tt}",
    supported_c: "supported at the conclusion {ff}", ctx_perm_inv: "contexts permutable", ctx_set_inv: "contexts read as sets",
    ctx_up_closed: "contexts weakenable (⊆)", ctx_append_extensive: "contexts append-extensible" };
  const REL_SHAPES = ["sound_at", "complete_at", "complete_within_at", "translates_at", "reflects_at", "gentzen_closed", ...Object.keys(SHAPE_EVIDENCE)];
  const REL_TEXT = { sound_at: "{S} ≤ {T} (sound)", complete_at: "{T} ≤ {S} (complete)", complete_within_at: "{T} ≤ {S} where {mu} ≤ {b}",
    translates_at: "{S} → {T} along ({f}, {g}) preserves", reflects_at: "{T} → {S} along ({f}, {g}) reflects", gentzen_closed: "{S} closed under {rules}",
    ...Object.fromEntries(Object.entries(SHAPE_EVIDENCE).map(([k, v]) => [k, "{S}: " + v])) };
  function standing(p) {
    const s = p.summary || "OPN";
    if (s === "THM") return "established";
    if (s === "OPN" || s === "UNK") return "unknown";
    if (s === "SAT") return "partial";
    return "counterevidence";   // CSA, UNS, contingent (which includes CSA)
  }
  async function relations(ctx, system) {
    const shapes = REL_SHAPES.map((x) => PREFIX + x);
    const marks = shapes.map(() => "?").join(",");
    const rows = await ctx.q(
      "SELECT DISTINCT cp.problem, cp.shape, cp.expect, cp.summary, cp.verdict, cp.title, p.arity, " + ESTABLISHED + ", " +
      "(SELECT group_concat(a.status || coalesce(': ' || a.witness, ''), '; ') FROM answers a WHERE a.problem = cp.problem) AS answers, " +
      "(SELECT a.decl FROM answers a WHERE a.problem = cp.problem LIMIT 1) AS proof, (SELECT a.module FROM answers a WHERE a.problem = cp.problem LIMIT 1) AS module " +
      `FROM consequence_problems cp JOIN problems p ON p.name = cp.problem WHERE cp.shape IN (${marks})` +
      (system ? " AND cp.problem IN (SELECT problem FROM consequence_problems WHERE system = ?)" : "") +
      " ORDER BY cp.shape, cp.problem LIMIT 2000", system ? [...shapes, system] : shapes);
    const args = await argsOf(ctx, rows.map((r) => r.problem));
    return rows.map((r) => Object.assign(r, { args: args.get(r.problem) || {}, standing: standing(r) }));
  }
  function relationRow(r, base) {
    const a = r.args, plain = Object.fromEntries(Object.entries(a).map(([k, v]) => [k, v.system ? rel(v.system, base) : compactText(v.text)]));
    const lk = (k) => a[k] ? (a[k].system ? sysLink(a[k].system) : term(a[k].text)) : "";
    const what = REL_TEXT[SHAPE(r.shape)] || SHAPE(r.shape);
    const html = ui.esc(what).replace(/\{(S|T|mu|b|f|g|rules|tt|ff)\}/g, (_, k) => lk(k) || k);
    const sl = r.proof && typeof sourceLink === "function" ? sourceLink(r.module, r.proof) : "";
    return `<tr data-standing="${r.standing}"><td>${html}</td><td>${ui.link("problem", r.problem)}</td><td class="nw">${outcome(r)}</td>` +
      `<td>${ui.esc(r.standing)}</td><td>${r.answers ? ui.esc(compactText(r.answers)) : '<span class="muted">none</span>'}${r.proof ? ` by ${code(r.proof)}${sl ? " " + sl : ""}` : ""}</td></tr>`;
  }
  async function relationsTable(ctx, only) {
    let rs = await relations(ctx, null);
    if (only) rs = rs.filter((r) => Object.values(r.args).some((v) => v.system && only.has(v.system)));
    const cons = await ctx.q("SELECT o.system, o.operand, c.op FROM consequence_operands o JOIN consequence_systems c ON c.name = o.system ORDER BY o.system, o.pos LIMIT 2000");
    const arts = await ctx.q("SELECT name, value, interpretation FROM consequence_systems WHERE op = 'artifact' ORDER BY name LIMIT 2000").catch(() => []);
    let h = `<h3>Relations</h3><p class="muted">How the systems are related: constructions and artifacts by definition, and every
soundness, completeness (also within a measure bound), translation and Gentzen-closure problem, with where it stands —
<b>established</b> (proved), <b>counterevidence</b> (a counterexample or refutation, kept with its answer), <b>partial</b> (only an instance)
or <b>unknown</b>.</p><div class="tablebox"><table id="systems-relations"><thead><tr><th>relation</th><th>problem</th><th>outcome</th><th>standing</th><th>answers (witness), proof</th></tr></thead><tbody>`;
    for (const c of cons) if (!only || only.has(c.system)) h += `<tr data-standing="definition"><td>${sysLink(c.system)} is a ${ui.esc(c.op)} with operand ${sysLink(c.operand)}</td><td></td><td></td><td>by definition</td><td></td></tr>`;
    for (const c of arts) if (!only || only.has(c.name)) h += `<tr data-standing="definition"><td>${sysLink(c.name)} is ${ui.link("value", c.value)} read by ${ui.esc(c.interpretation)}</td><td></td><td></td><td>by definition</td><td></td></tr>`;
    h += rs.map((r) => relationRow(r, "")).join("");
    return h + `</tbody></table></div>`;
  }

  async function listPage(arg, ctx) {
    if (!has()) return `<h2>Consequence systems</h2>${missing}`;
    const view = new URLSearchParams((arg || "").replace(/^\?/, "")).get("view") || "all";
    const hasDef = await hasColumn(ctx, "consequence_interpretations", "definedness");
    const all = await ctx.q(
      "SELECT c.*, " + (hasDef ? "(SELECT ci.definedness FROM consequence_interpretations ci WHERE ci.name = c.interpretation) AS definedness, " : "") +
      "(SELECT count(*) FROM consequence_operands o WHERE o.system = c.name) AS n_operands " +
      "FROM consequence_systems c ORDER BY c.name LIMIT " + (LIMIT + 1));
    const gz = await gentzenOf(ctx);
    // proved shape evidence per system (THM only): the exact property, never a generic label
    const proved = new Map();
    for (const r of await ctx.q("SELECT DISTINCT cp.system, cp.shape, cp.problem FROM consequence_problems cp WHERE cp.role = 'S' AND cp.summary = 'THM' AND cp.shape IN (" +
        Object.keys(SHAPE_EVIDENCE).map(() => "?").join(",") + ") LIMIT 5000", Object.keys(SHAPE_EVIDENCE).map((k) => PREFIX + k))) {
      if (!proved.has(r.system)) proved.set(r.system, []);
      proved.get(r.system).push(r);
    }
    const certified = new Set([...gz].filter(([, l]) => l.some((x) => x.summary === "THM")).map(([k]) => k));
    const test = (VIEWS.find((v) => v[0] === view) || VIEWS[0])[2];
    const rows = all.filter((r) => test(r, certified));
    // the problems of each system, once each (a problem naming it as S and as T counts once)
    const probs = new Map();
    for (const r of await ctx.q("SELECT DISTINCT cp.system, cp.problem, cp.expect, cp.summary, cp.verdict, p.arity, " + ESTABLISHED + " " +
        "FROM consequence_problems cp JOIN problems p ON p.name = cp.problem LIMIT 20000")) {
      if (!probs.has(r.system)) probs.set(r.system, []);
      probs.get(r.system).push(r);
    }
    let h = `<h2>Consequence systems</h2>
<p class="muted">A consequence system <code>S : Ax → C → Prop</code> relates contexts to conclusions; <code>S Γ φ</code> reads
<code>Γ ⊢ φ</code>. A context may be a finite list <code>C₁, …, Cₙ</code>, a set or anything else, and <b>no structural rule is
implicit</b>: a system is reflexive, monotone or closed under cut only if a proof below says so. Every property is a problem
with Lean answers; a problem with no answer is <b>unknown</b>, not false.</p>
<div class="views" id="systems-views">${VIEWS.map(([id, label, t]) => { const n = all.filter((r) => t(r, certified)).length;
  return `<a class="viewbtn${id === view ? " on" : ""}" data-view="${id}" href="#/systems/?view=${id}">${ui.esc(label)} <span class="muted">${n}</span></a>`; }).join("")}</div>
<p class="muted">Views read the shape Lean recorded from each system's types (unit, list, finset, set or a scalar carrier, the element type,
<code>Signed</code> polarity on each side). <b>Raw sequents</b> are list-to-list relations of one formula type; <b>Gentzen-closed</b> are those with a
proved <code>gentzen_closed</code> certificate for a named rule profile.</p>
<div class="tablebox"><table id="systems-table"><thead><tr><th>system</th><th>title</th><th>construction</th><th>shape (contexts → conclusions)</th>
<th title="closed judgments: true / false / unknown">judgments</th><th title="problems with free arguments">questions</th><th title="expected statuses met / problems (unknown or unset is not met)">expectations</th></tr></thead><tbody>`;
    for (const r of rows.slice(0, LIMIT)) {
      const how = r.op === "erase" ? `erase of ${term(r.witness)}` : r.op === "decl" ? term(r.decl)
        : r.op === "artifact" ? `artifact ${ui.link("value", r.value)} read by ${ui.esc(r.interpretation)}`
        : `${ui.esc(r.op)} of ${r.n_operands} systems`;
      const ps = probs.get(r.name) || [];
      const cl = ps.filter((p) => p.arity === 0);
      const tru = cl.filter((p) => p.summary === "THM" || p.summary === "SAT").length;
      const fal = cl.filter((p) => p.summary === "UNS" || p.summary === "CSA").length;
      const n = summarize(ps), bad = n.mismatch + n.error;
      h += `<tr><td>${sysLink(r.name)}</td><td>${ui.esc(r.title || "")}</td><td>${how}</td>` +
        `<td>${shapeText(r)}${gz.has(r.name) ? gz.get(r.name).filter((x) => x.summary === "THM").map((x) => ` <span class="pill" title="${ui.esc(x.problem)}">closed: ${ui.esc(compactText(x.rules || "rules"))}</span>`).join("") : ""}` +
        (proved.get(r.name) || []).filter((x) => !/supported_/.test(x.shape)).map((x) => ` <span class="pill" title="proved: ${ui.esc(x.problem)}">${ui.esc(SHAPE_EVIDENCE[SHAPE(x.shape)])} ✓</span>`).join("") + `</td>` +
        `<td>${cl.length ? `${tru} / ${fal} / ${cl.length - tru - fal}` : ""}</td><td>${ps.length - cl.length || ""}</td>` +
        `<td>${n.total ? `${n.met} / ${n.total}${bad ? ` <b>(${bad} unexpected)</b>` : ""}` : ""}</td></tr>`;
    }
    h += `</tbody></table></div>`;
    if (rows.length > LIMIT) h += `<p class="muted">showing the first ${LIMIT}; use the SQL tab for the rest</p>`;
    if (!rows.length) h += `<p class="muted">${all.length ? "No system in this view." : "No consequence system is registered (<code>silmaril consequence_system</code>)."}</p>`;
    h += await relationsTable(ctx, view === "all" ? null : new Set(rows.map((r) => r.name)));
    h += `<h3>The standard questions</h3>
<p class="muted">Each is a shape <code>${ui.esc(PREFIX)}…</code> whose last arguments are the context Γ and the conclusion φ; an instance
fixes the systems and asks about the arguments left free. The statuses mean (for <code>S</code> fixed, Γ and φ free):</p>
<div class="tablebox"><table id="systems-questions"><thead><tr><th>shape</th><th>statement</th><th>THM</th><th>SAT</th><th>UNS</th><th>CSA</th></tr></thead><tbody>` +
      [["derives", "Γ ⊢ φ in S", "ctx phi"], ["context_universal", "Γ derives every φ in S", "ctx"], ["derives_bottom", "Γ ⊢ ff in S", "ctx"],
        ["sound_at", "S Γ φ → T Γ φ", "ctx phi"], ["complete_at", "T Γ φ → S Γ φ", "ctx phi"],
        ["translates_at", "S Γ φ → T (f Γ) (g φ)", "ctx phi"], ["reflects_at", "T (f Γ) (g φ) → S Γ φ", "ctx phi"]]
        .map(([s, st, free]) => { const r = READING[s][free]; return `<tr><td>${ui.esc(s)}</td><td>${code(st)}</td>` +
          ["THM", "SAT", "UNS", "CSA"].map((k) => `<td>${ui.esc(r[k] ? fill(r[k], {}) : "")}</td>`).join("") + "</tr>"; }).join("") +
      `</tbody></table></div>
<p class="muted"><b>Universal</b> (every context derives every conclusion), <b>context-universal</b> (one context derives every
conclusion) and <b>derives ff</b> (a context derives a chosen conclusion) are different properties; they coincide only under
structural rules a system may not have. Fixing Γ and φ gives the member judgment <code>Γ ⊢ φ</code>, a closed proposition:
true or false. The judgments column counts these as true / false / unknown; the expectations column counts expected statuses
met, which is not the same as true. Constructions name their operands on the system's page.</p>`;
    return h;
  }

  async function detailPage(name, ctx) {
    if (!has()) return missing;
    const [c] = await ctx.q("SELECT * FROM consequence_systems WHERE name = ? LIMIT 1", [name]);
    if (!c) return `<p class="err">no consequence system ${ui.esc(name)}</p>`;
    const operands = await ctx.q("SELECT operand FROM consequence_operands WHERE system = ? ORDER BY pos LIMIT 100", [name]);
    const usedBy = await ctx.q("SELECT DISTINCT system FROM consequence_operands WHERE operand = ? ORDER BY system LIMIT 100", [name]);
    let h = `<h2>consequence system <code>${ui.esc(name)}</code></h2>`;
    if (c.title) h += `<p><b>${ui.esc(c.title)}</b></p>`;
    if (c.doc) h += `<p>${ui.esc(c.doc)}</p>`;
    const OPS = { decl: "a Lean definition", union: "union (⊔): Γ ⊢ φ in some operand", inter: "intersection (⊓): Γ ⊢ φ in every operand",
      diff: "difference (\\): Γ ⊢ φ in the first operand and not in the second", erase: "erasure of a witness system: Γ ⊢ φ iff some derivation exists (Nonempty)",
      artifact: "an interpreted artifact: Γ ⊢ φ iff the artifact's CID-pinned bytes decode to a value v with I v Γ φ" };
    const src = typeof sourceLink === "function" ? sourceLink(c.module, c.decl) : "";
    const rows = [
      ["relates", `contexts ${term(c.contexts)} to conclusions ${term(c.conclusions)}`],
      ["shape", shapeText(c)],
      ["construction", ui.esc(OPS[c.op] || c.op)],
      ["Lean definition", code(c.decl) + ` <span class="muted">in ${ui.esc(c.module)}</span>${src ? " " + src : ""}`],
    ];
    if (c.reading) rows.push(["reading", c.reading === "semantic"
      ? "semantic consequence <span class=\"muted\">(Lean checked that it is the room's consequence)</span>"
      : "derivability <span class=\"muted\">(a proof system on the room's sentences; related to semantic consequence only by proved soundness)</span>"]);
    if (c.room) rows.push(["over the sentences of", `<a href="#/room/${encodeURIComponent(c.room)}">${ui.esc(c.room)}</a>` +
      (c.room_at ? ` <span class="muted">at</span> ${code(c.room_at)}` : "") + (c.room_lift ? ` <span class="muted">(sentences lifted by ULift)</span>` : "") +
      ` <span class="muted">— <a href="#/logic-consequence/">consequence systems of the logics</a></span>`]);
    if (c.op === "artifact" && c.value) rows.push(...await artifactRows(c, ctx));
    if (c.witness) rows.push(["witness system", term(c.witness) + ` <span class="muted">(a type of derivations of each Γ ⊢ φ)</span>`]);
    if (operands.length) rows.push(["operands", operands.map((o) => sysLink(o.operand)).join(", ")]);
    if (usedBy.length) rows.push(["used by", usedBy.map((u) => sysLink(u.system)).join(", ")]);
    if (c.source) rows.push(["source", ui.esc(c.source)]);
    h += `<dl>${rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("")}</dl>`;

    const ps = await ctx.q(
      "SELECT cp.problem, cp.shape, cp.role, cp.expect, cp.title, cp.summary, cp.verdict, p.arity, " + ESTABLISHED + ", " +
      "(SELECT group_concat(r.role, ' ') FROM consequence_shape_roles r WHERE r.shape = cp.shape) AS roles, " +
      "(SELECT 1 FROM deprecated_problems d WHERE d.problem = cp.problem LIMIT 1) AS deprecated " +
      "FROM consequence_problems cp JOIN problems p ON p.name = cp.problem " +
      "WHERE cp.system = ? ORDER BY cp.shape, p.arity DESC, cp.problem LIMIT " + LIMIT, [name]);
    // a problem naming this system in two roles (S and T of a translation into itself) is one row
    { const seen = new Map();
      for (const p of ps.splice(0)) { if (seen.has(p.problem)) seen.get(p.problem).role += ", " + p.role; else { seen.set(p.problem, p); ps.push(p); } } }
    for (const p of ps) p.roles = (p.roles || "").split(" ");
    const base = name.includes(".") ? name.slice(0, name.lastIndexOf(".") + 1) : "";
    const args = await argsOf(ctx, [...new Set(ps.map((p) => p.problem))]);
    const answers = new Map();
    if (ps.length) {
      const marks = ps.map(() => "?").join(",");
      for (const a of await ctx.q(`SELECT problem, status, witness, decl, module FROM answers WHERE problem IN (${marks}) ORDER BY problem, status LIMIT 2000`, ps.map((p) => p.problem))) {
        if (!answers.has(a.problem)) answers.set(a.problem, []);
        answers.get(a.problem).push(a);
      }
    }
    const rs = await relations(ctx, name);
    if (rs.length) {
      const groups = [["established", "Established"], ["counterevidence", "Counterevidence (kept)"], ["partial", "Partial (an instance only)"], ["unknown", "Unknown"]];
      h += `<h3>Evidence</h3><p class="muted">Soundness, completeness (exact measure and bound when bounded), translations and Gentzen closure
involving this system, grouped by where they stand. Established means the universal (or closed) statement is proved; a counterexample
or refutation is counterevidence; an instance alone is partial.</p>`;
      for (const [k, title] of groups) {
        const g = rs.filter((r) => r.standing === k);
        if (!g.length) continue;
        h += `<h4>${title}</h4><div class="tablebox"><table class="system-evidence" data-standing="${k}"><thead><tr><th>relation</th><th>problem</th><th>outcome</th><th>standing</th><th>answers (witness), proof</th></tr></thead><tbody>` +
          g.map((r) => relationRow(r, base)).join("") + `</tbody></table></div>`;
      }
    }
    h += `<h3>Problems</h3><p class="muted">Every standard consequence problem that names this system, as <b>S</b> (the system asked about)
or <b>T</b> (the system it is compared with or translated into). The reading says what the outcome means for the arguments left free;
a CSA answer written <code>⟨Γ, φ, h⟩</code> keeps its counterexample. No answer means unknown, not false.</p>`;
    if (!ps.length) {
      h += `<p class="muted">No standard consequence problem names this system.</p>`;
    } else {
      h += expectations(ps);
      const table = (id, list) => {
        let t = `<div class="tablebox"><table id="${id}"><thead><tr><th>problem</th><th>question</th><th>as</th><th>fixed</th><th>outcome</th><th>reading</th><th>answers (witness)</th></tr></thead><tbody>`;
        for (const p of list) {
          const a = args.get(p.problem) || {};
          const plain = Object.fromEntries(Object.entries(a).map(([k, v]) => [k, v.system ? rel(v.system, base) : compactText(v.text)]));
          const own = p.role.split(", ");
          const fixed = Object.entries(a).filter(([k]) => !own.includes(k))
            .map(([k, v]) => `${ui.esc(k)} = ${v.system ? sysLink(v.system) : term(v.text)}`).join("<br>");
          const ans = (answers.get(p.problem) || []).map((x) => {
            let w = "";
            try { const ws = x.witness ? JSON.parse(x.witness) : null; if (Array.isArray(ws) && ws.length) w = ": " + ws.map(term).join(", "); } catch { /* shown without */ }
            const sl = typeof sourceLink === "function" ? sourceLink(x.module, x.decl) : "";
            return `${ui.esc(x.status)}${w} by ${code(x.decl)}${sl ? " " + sl : ""}`;
          }).join("<br>");
          t += `<tr><td>${ui.link("problem", p.problem)}<div class="muted">${ui.esc(p.title || "")}</div></td>` +
            `<td>${ui.esc(SHAPE(p.shape))}</td><td>${ui.esc(p.role)}</td><td>${fixed}</td>` +
            `<td class="nw">${outcome(p)}</td><td>${ui.esc(reading(p, plain))}</td><td>${ans || '<span class="muted">none</span>'}</td></tr>`;
        }
        return t + `</tbody></table></div>`;
      };
      const closed = ps.filter((p) => p.arity === 0), open = ps.filter((p) => p.arity !== 0);
      if (closed.length) {
        h += `<h4>Judgments: closed, true or false</h4><p class="muted">Every argument is fixed, so each is one proposition: THM or SAT
means true, UNS or CSA false (a refutation is stored as UNS), no answer unknown.</p>` + table("system-judgments", closed);
      }
      if (open.length) {
        h += `<h4>Questions over the free arguments: SZS status</h4><p class="muted">Some arguments (Γ, φ) are free: THM holds for all of
them, SAT for some, UNS for none, CSA fails for some, NOC (stored <code>contingent</code>) is SAT and CSA together.</p>` + table("system-problems", open);
      }
    }
    return h;
  }

  // The artifact of an `op := artifact` system: the value and its CID-pinned bytes, the
  // interpretation (definition, ABI, environment), and the decode evidence (the value's `.is` and
  // `.parses` problems, when registered). Without a decode certificate the system is ⊥ only
  // because nothing decodes; that is never shown as a verified empty checker.
  async function artifactRows(c, ctx) {
    const out = [];
    const src = await ctx.q("SELECT pos, cid, format FROM value_sources WHERE value = ? ORDER BY pos LIMIT 10", [c.value]);
    out.push(["artifact", ui.link("value", c.value) + src.map((s) => ` — bytes ${ui.link("artifact", s.cid, s.cid.slice(0, 20) + "…")} read as ${ui.esc(s.format)}`).join("")]);
    if (Explorer.tables().has("consequence_interpretations")) {
      const [i] = await ctx.q("SELECT decl, input, abi, environment, doc FROM consequence_interpretations WHERE name = ? LIMIT 1", [c.interpretation]);
      out.push(["interpretation", ui.esc(c.interpretation) + (i ? `: ${term(i.decl)} reading ${term(i.input)}, ABI ${term(i.abi) || "none declared"}, environment ${term(i.environment) || "none declared"}` +
        (i.doc ? `<div class="muted">${ui.esc(i.doc)}</div>` : "") : "")]);
    }
    const ev = await ctx.q("SELECT p.name, s.summary, s.verdict, p.arity, p.expect FROM problems p LEFT JOIN summary s ON s.problem = p.name " +
      "WHERE p.name IN (?, ?) ORDER BY p.name LIMIT 2", [c.value + ".is", c.value + ".parses"]);
    if (c.env_term) out.push(["configuration", `${term(c.env_term)} <span class="muted">(the interpretation is partial: the system is its reading at this configuration, or ⊥ where it is undefined)</span>`]);
    out.push(["decode evidence", ev.length
      ? ev.map((e) => `${ui.link("problem", e.name)} ${ui.statusBadge({ summary: e.summary || "OPN", verdict: e.verdict || "unknown", arity: e.arity, expect: e.expect || null })}`).join(" · ") +
        `<div class="muted">The <code>.is</code> certificate says the bytes decode to the Lean module the theorems are about. Without it, a system
that derives nothing may only mean that the bytes do not decode.</div>`
      : `<span class="muted">none registered: the bytes are not tied to a Lean module, and an empty system may only mean that they do not decode</span>`]);
    if (c.env_term || (await hasColumn(ctx, "consequence_interpretations", "definedness") &&
        (await ctx.q("SELECT definedness FROM consequence_interpretations WHERE name = ? LIMIT 1", [c.interpretation]))[0]?.definedness === "partial")) {
      out.push(...await definednessRows(c, ctx, ev.some((e) => e.summary === "THM")));
    }
    return out;
  }

  // On an artifact's (or Wasm module's) page: the consequence systems its bytes denote.
  async function artifactSection(subject, ctx) {
    const t = Explorer.tables();
    if (!subject.cid || !t.has("consequence_systems") || !t.has("consequence_interpretations")) return "";
    const rows = await ctx.q(
      "SELECT c.name, c.title, c.interpretation, i.decl AS definition, i.abi, i.environment, vs.value, " +
      "(SELECT count(DISTINCT cp.problem) FROM consequence_problems cp WHERE cp.system = c.name) AS problems " +
      "FROM value_sources vs JOIN consequence_systems c ON c.value = vs.value AND c.op = 'artifact' " +
      "LEFT JOIN consequence_interpretations i ON i.name = c.interpretation " +
      "WHERE vs.cid = ? ORDER BY c.name LIMIT " + LIMIT, [subject.cid]);
    if (!rows.length) return "";
    return `<p class="muted">The consequence systems these bytes denote under a registered interpretation (Γ ⊢ φ; semantics, ABI and
environment as Lean definitions). Problems without a Lean answer are unknown. Nothing on this page runs the module.</p>` +
      await ui.table(rows, ["name", "title", "value", "interpretation", "definition", "abi", "environment", "problems"], {
        render: { name: (r) => sysLink(r.name), value: (r) => ui.link("value", r.value), definition: (r) => term(r.definition),
          abi: (r) => term(r.abi) || '<span class="muted">none declared</span>', environment: (r) => term(r.environment) || '<span class="muted">none declared</span>' },
        label: { name: "system" } });
  }
  Explorer.registerSection({ id: "consequence-systems", title: "Consequence systems", on: ["artifact", "wasm-module"], order: 55,
    render: artifactSection });

  // A family `fun x => T` over the configurations, at the configuration `e` (display only: the
  // types themselves were recorded by Lean; a constant family shows as its type).
  function family(t) {
    const m = /^fun (\S+) => (.*)$/.exec(t || "");
    if (!m) return `${t} e`;
    return new RegExp("\\b" + m[1].replace(/[^\w]/g, "\\$&") + "\\b").test(m[2]) ? `(${t}) e` : m[2];
  }

  // Evidence matrices (`consequence_matrix`): the protocol owner's cells, verbatim, with the
  // declarations they list as supporting references.
  async function matrixSection(ctx) {
    if (!Explorer.tables().has("consequence_matrix_cells")) return "";
    const cells = await ctx.q("SELECT * FROM consequence_matrix_cells ORDER BY matrix, pos LIMIT 500");
    if (!cells.length) return "";
    const ref = (t) => { const sl = typeof sourceLink === "function" ? sourceLink(t.module, t.name) : "";
      return `${term(t.name)}${sl ? " " + sl : ` <span class="muted" title="no source for ${ui.esc(t.module)} on this page">(${ui.esc(t.module)})</span>`}`; };
    let h = "";
    for (const m of [...new Set(cells.map((c) => c.matrix))]) {
      const cs = cells.filter((c) => c.matrix === m);
      const count = (k, v) => cs.filter((c) => c[k] === v).length;
      h += `<h3>Protocol evidence matrix <code>${ui.esc(m)}</code></h3>
<p class="muted">Protocol-provided evidence and strength classifications, one cell per protocol variant, copied verbatim from
<code>${ui.esc(cs[0].decl)}</code>; the listed declarations are supporting references (the registry checked that they exist, not that the
classification is right). <b>specStrategy</b> evidence is about a specification strategy, not a compiled component; <b>execution</b> evidence is
about a verified core module through an explicit byte codec. Evidence: ${count("evidence", "definitions")} definitions,
${count("evidence", "specStrategy")} spec strategy, ${count("evidence", "execution")} execution.</p>
<div class="tablebox"><table class="matrix-table" data-matrix="${ui.esc(m)}"><thead><tr><th>variant</th><th>reading</th><th>evidence</th><th>strength</th><th>note</th><th>supporting declarations</th></tr></thead><tbody>` +
        cs.map((c) => { let ts = []; try { ts = typeof c.theorems === "string" ? JSON.parse(c.theorems) : c.theorems; } catch { ts = []; }
          return `<tr data-evidence="${ui.esc(c.evidence)}" data-strength="${ui.esc(c.strength)}"><td>${term(c.variant)}</td><td>${term(c.reading)}</td>` +
            `<td>${ui.esc(c.evidence)}</td><td>${ui.esc(c.strength)}</td><td>${ui.esc(c.note)}</td><td>${ts.map(ref).join("<br>")}</td></tr>`; }).join("") +
        `</tbody></table></div>`;
    }
    return h;
  }

  // The Interpretations pane: every registered interpretation of a value as a language
  // (`language_interpretation`, `V → Set T`) or as a consequence system
  // (`consequence_interpretation`, `V → System Ax C`), from the existing tables, with what uses it.
  async function interpretationsPage(arg, ctx) {
    const t = Explorer.tables();
    let h = `<h2>Interpretations</h2>
<p class="muted">How a registered value (an artifact's decoded bytes) denotes a language or a consequence system. Each is a Lean definition
over the value's type; its ABI and environment, when declared, occur in that definition (a check of the metadata, not a proof that the
definition models execution). The problem counts are of distinct problems about its systems; they say what has been proved about
particular readings, not that every reading is sound or complete. <b>Definedness</b> is the declaration's: <i>total</i> means the definition gives a result for every value;
<i>partial</i> (a core <code>Interp Env V Ax C</code>) gives an optional system under a configuration <code>e : Env</code>, and a system read
through it is that reading or ⊥ where it is undefined — whether it is defined is a separate certificate (<code>artifact_defined</code>).
Applying it to an artifact can still fail earlier, when the bytes do not decode; a system's or language's page shows its decode evidence.</p>`;
    const rows = [];
    if (t.has("language_interpretations")) {
      for (const r of await ctx.q("SELECT i.name, i.decl, i.input, i.carrier AS output, i.abi, i.environment, i.doc, i.domain, " +
          "(SELECT group_concat(l.name, ' ') FROM languages l WHERE l.interpretation = i.name) AS users FROM language_interpretations i ORDER BY i.name LIMIT 500"))
        rows.push(Object.assign(r, { kind: "language", output: `Set (${r.output})` }));
    }
    if (t.has("consequence_interpretations")) {
      const d = await hasColumn(ctx, "consequence_interpretations", "definedness");
      for (const r of await ctx.q("SELECT i.name, i.decl, i.input, i.contexts, i.conclusions, i.abi, i.environment, i.doc, " +
          (d ? "i.definedness, i.env, " : "") +
          "(SELECT group_concat(c.name, ' ') FROM consequence_systems c WHERE c.interpretation = i.name) AS users, " +
          // distinct problems about its systems, by standing (no duplicates across roles)
          "(SELECT count(DISTINCT cp.problem) FROM consequence_problems cp JOIN consequence_systems c ON c.name = cp.system WHERE c.interpretation = i.name AND cp.summary = 'THM') AS n_est, " +
          "(SELECT count(DISTINCT cp.problem) FROM consequence_problems cp JOIN consequence_systems c ON c.name = cp.system WHERE c.interpretation = i.name AND cp.summary IN ('CSA','UNS','contingent')) AS n_counter, " +
          "(SELECT count(DISTINCT cp.problem) FROM consequence_problems cp JOIN consequence_systems c ON c.name = cp.system WHERE c.interpretation = i.name AND coalesce(cp.summary,'OPN') IN ('OPN','UNK')) AS n_unknown " +
          "FROM consequence_interpretations i ORDER BY i.name LIMIT 500"))
        rows.push(Object.assign(r, { kind: "system", output: r.definedness === "partial"
          ? `(e : ${r.env}) → Option (System (${family(r.contexts)}) (${family(r.conclusions)}))` : `System (${r.contexts}) (${r.conclusions})` }));
    }
    if (!rows.length) return h + `<p class="muted">No interpretation is registered.</p>`;
    h += `<div class="tablebox"><table id="interpretations-table"><thead><tr><th>interpretation</th><th>kind</th><th>reads</th><th>gives</th><th>ABI</th><th>environment</th><th>definedness</th><th>used by</th>
<th title="distinct problems about the systems read through it: proved (THM) / refuted or counterexample / unknown">problems</th></tr></thead><tbody>`;
    for (const r of rows) {
      const users = (r.users || "").split(" ").filter(Boolean);
      const userLink = (n) => r.kind === "system" ? sysLink(n) : `<a href="#/language/${encodeURIComponent(n)}">${ui.esc(n)}</a>`;
      h += `<tr data-kind="${r.kind}"><td>${ui.esc(r.name)}<div class="muted">${term(r.decl)}</div></td><td>${r.kind === "system" ? "consequence system" : "language"}</td>` +
        `<td>${term(r.input)}</td><td>${term(r.output)}</td><td>${term(r.abi) || '<span class="muted">none declared</span>'}</td>` +
        `<td>${term(r.environment) || '<span class="muted">none declared</span>'}</td>` +
        `<td>${r.definedness === "partial" ? `partial, at a configuration e : ${term(r.env)}` : "total"}</td>` +
        `<td>${users.length ? users.map(userLink).join("<br>") : '<span class="muted">unused</span>'}</td>` +
        `<td class="nw">${r.kind === "system" && (r.n_est || r.n_counter || r.n_unknown) ? `${r.n_est} proved / ${r.n_counter} counter / ${r.n_unknown} unknown` : ""}</td></tr>` +
        (r.doc ? `<tr class="doc"><td></td><td colspan="8" class="muted">${ui.esc(r.doc)}</td></tr>` : "");
    }
    h += `</tbody></table></div>` + await matrixSection(ctx) + `<h3>Usage</h3><pre class="usage">${ui.esc(`silmaril language_interpretation N := I (domain := D) (abi := A) (environment := E)   -- I : V → Set T
silmaril language L (domain := D) (op := artifact) (value := X) (interpretation := N)
silmaril consequence_interpretation N := I (abi := A) (environment := E)            -- I : V → System Ax C
silmaril consequence_system S (op := artifact) (value := X) (interpretation := N)
silmaril consequence_interpretation N := I                                             -- I : Interp Env V Ax C (partial)
silmaril consequence_system S (op := artifact) (value := X) (interpretation := N) (env := "e")   -- I.orBot e
silmaril instance D := silmaril.shapes.consequence.artifact_defined (X := X) (I := I) (e := e)`)}</pre>`;
    return h;
  }

  const style = document.createElement("style");
  style.textContent = ".views { display:flex; gap:6px; flex-wrap:wrap; margin:8px 0; } " +
    ".viewbtn { border:1px solid var(--line); border-radius:4px; padding:2px 8px; text-decoration:none; } .viewbtn.on { background:var(--panel); font-weight:600; } " +
    ".pill { font-size:11px; border:1px solid var(--line); border-radius:8px; padding:0 5px; white-space:nowrap; } " +
    "pre.usage { background:var(--panel); border:1px solid var(--line); padding:8px 10px; font:12px ui-monospace, monospace; overflow:auto; }";
  document.head.appendChild(style);

  Explorer.registerView({ id: "interpretations", title: "Interpretations", nav: 67, render: interpretationsPage });
  Explorer.registerView({ id: "systems", title: "Systems", nav: 66, render: listPage });
  Explorer.registerView({ id: "system", title: "System", tab: "systems", render: detailPage });
})();
