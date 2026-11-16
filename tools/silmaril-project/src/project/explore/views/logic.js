// The logic graph (docs/projects/logic-graph.md): institutions as nodes with comorphisms and morphisms
// as typed, directed edges, and one level down rooms (an institution at one signature) with
// corridors; the five registries; the coverage audit (declarations the registry omits, the pinned
// Hets logic graph, logic families not yet in this repository).
//   #/logic-graph/[<kind>:<name>][?level=…&kinds=…&q=…&layout=layered&group=0&isolated=0]   the graph viewer, a selection deep-linked
//   #/logics/[?q=…]  (also #/logic-table/)                every node and edge, searchable and sortable: the default view
//   #/institutions #/comorphisms #/morphisms #/rooms #/corridors   the registries
//   #/institution/<name> … #/corridor/<name>             one record, with its crosslinks
//   #/logic-coverage                                      the audit
// It reads the database only. Every node and edge is a Lean declaration whose type Lean checked;
// endpoints were found by Lean, not written by hand. A Hets relation is what the record claims
// (corresponds, fragment, related), never "Hets coverage" by itself.
(() => {
  const ui = Explorer.ui;
  const has = (t) => Explorer.tables().has(t);
  const missing = `<p class="muted">This database has no logic-graph tables (built by an older <code>sil project</code>).</p>`;
  const LIMIT = 5000;
  // The node and edge kinds. Colours: the explorer's categorical slots 1–3, validated for colour
  // vision deficiency; every edge kind is also told apart by its line style and its label.
  const KIND = {
    institution: { plural: "institutions", title: "Institutions", level: "institution", node: true,
      what: "a category of signatures with a functor into rooms (Inst)" },
    room: { plural: "rooms", title: "Rooms", level: "room", node: true,
      what: "sentences, a category of models and satisfaction: an institution at one signature" },
    comorphism: { plural: "comorphisms", title: "Comorphisms", level: "institution", color: "#2a78d6", line: "solid",
      what: "a logic translation A → B: signatures Φ : Sign_A → Sign_B, sentences forwards, models backwards" },
    morphism: { plural: "morphisms", title: "Morphisms", level: "institution", color: "#eb6834", line: "dashed",
      what: "a logic projection A → B: signatures Φ : Sign_A → Sign_B, sentences backwards, models forwards" },
    corridor: { plural: "corridors", title: "Corridors", level: "room", color: "#1baf7a", line: "dotted",
      what: "between rooms R₁ → R₂ (a comorphism at one signature): sentences forwards, models backwards" },
  };
  const EDGES = ["comorphism", "morphism", "corridor"];
  const NODES = ["institution", "room"];
  const short = (n) => { const p = String(n).split("."); return p.length > 2 ? p.slice(-2).join(".") : n; };
  const code = (s) => s == null || s === "" ? "" : `<code>${ui.esc(s)}</code>`;
  const rec = (kind, name, text) => name == null ? "" : `<a href="#/${kind}/${encodeURIComponent(name)}">${ui.esc(text == null ? name : text)}</a>`;
  const src = (module, decl) => typeof sourceLink === "function" ? sourceLink(module, decl) : "";
  const pill = (t, title) => `<span class="pill"${title ? ` title="${ui.esc(title)}"` : ""}>${ui.esc(t)}</span>`;
  const family = (r) => r.arity > 0 ? pill(`family, ${r.arity} ${r.arity === 1 ? "parameter" : "parameters"}`, r.params || "") : "";
  const hetsText = (r) => r.hets ? `${pill(r.hets_relation || "?", { corresponds: "the same logic or translation, as far as the Lean definition goes",
    fragment: "a fragment of it", related: "a comparable construction, not the same one" }[r.hets_relation] || "")} Hets <code>${ui.esc(r.hets)}</code>` : "";
  const edgeSwatch = (k) => `<svg width="34" height="10" aria-hidden="true"><line x1="1" y1="5" x2="26" y2="5" stroke="${KIND[k].color}" stroke-width="2.5"` +
    (KIND[k].line === "dashed" ? ' stroke-dasharray="6 3"' : KIND[k].line === "dotted" ? ' stroke-dasharray="2 3"' : "") +
    `/><path d="M26 1 L33 5 L26 9 z" fill="${KIND[k].color}"/></svg>`;

  const STYLE = "lg-style";
  function style() {
    if (document.getElementById(STYLE)) return;
    const s = document.createElement("style");
    s.id = STYLE;
    s.textContent =
      ".lg-tabs { display:flex; flex-wrap:wrap; gap:4px; margin:0 0 10px; } .lg-tabs a { border:1px solid var(--line); border-radius:4px; padding:2px 8px; text-decoration:none; background:var(--panel); } " +
      ".lg-tabs a.on { background:var(--accent); color:#fff; border-color:var(--accent); } .lg-tabs a span { color:inherit; opacity:.75; } " +
      ".lg-proved { color:#137333; font-weight:600; white-space:nowrap; } .lg-defined { color:#1a73e8; white-space:nowrap; } .lg-registered { color:#7b1fa2; white-space:nowrap; } .lg-absent { color:#80868b; white-space:nowrap; } " +
      "#lg-matrix td.lg-mx { min-width:120px; vertical-align:top; font-size:12px; } #lg-matrix .lg-mx-decls a { font-family:monospace; } #lg-matrix .lg-mx-note { font-size:11px; } " +
      ".lg-views { display:inline-flex; margin-right:10px; } .lg-views a { border-radius:0; } .lg-views a:first-child { border-radius:4px 0 0 4px; } .lg-views a:last-child { border-radius:0 4px 4px 0; border-left:0; } " +
      ".pill { font-size:11px; border:1px solid var(--line); border-radius:8px; padding:0 5px; white-space:nowrap; } " +
      "#lgwrap { display:flex; gap:12px; height:calc(100vh - 230px); min-height:440px; } " +
      "#lgcy { flex:1 1 auto; border:1px solid var(--line); background:var(--panel); min-width:0; position:relative; } " +
      "#lgcy:focus-visible { outline:3px solid var(--accent); outline-offset:1px; } " +
      "#lgside { flex:0 0 380px; overflow:auto; border:1px solid var(--line); background:var(--panel); padding:8px 10px; } " +
      "#lgside h3 { margin:4px 0 6px; font-size:14px; overflow-wrap:anywhere; } #lgside dd { overflow-wrap:anywhere; } .lg-empty { position:absolute; inset:0; display:flex; align-items:center; justify-content:center; color:var(--muted); padding:20px; text-align:center; } " +
      ".lg-legend { display:flex; flex-wrap:wrap; gap:4px 16px; align-items:center; font-size:13px; margin:4px 0 8px; } .lg-legend svg { vertical-align:middle; } " +
      ".lg-node { display:inline-block; width:16px; height:11px; border:1.5px solid #52514e; border-radius:3px; vertical-align:middle; background:#fff; } " +
      ".lg-node.room { border-radius:50%; background:#f1f3f5; } .lg-node.fam { border-style:dashed; } " +
      "table.lg-grid th button { font:inherit; font-weight:600; border:0; background:none; padding:0; cursor:pointer; color:inherit; } " +
      "table.lg-grid th[aria-sort=ascending] button::after { content:' ▲'; } table.lg-grid th[aria-sort=descending] button::after { content:' ▼'; } " +
      ".lg-stats { display:flex; flex-wrap:wrap; gap:8px; margin:6px 0 12px; } .lg-stat { border:1px solid var(--line); background:var(--panel); border-radius:6px; padding:6px 12px; min-width:110px; text-decoration:none; color:var(--fg); } " +
      ".lg-stat b { display:block; font-size:20px; font-variant-numeric:tabular-nums; } .lg-stat span { color:var(--muted); font-size:12px; } " +
      ".lg-dir { font-size:12px; color:var(--muted); } " +
      "@media (max-width: 800px) { #lgwrap { flex-direction:column; height:auto; } #lgcy { height:62vh; flex:0 0 auto; } #lgside { flex-basis:auto; max-height:none; } .lg-tabs a { padding:4px 8px; } }";
    document.head.appendChild(s);
  }

  // ---------- data ----------
  async function load(ctx) {
    const q = (t, sql) => has(t) ? ctx.q(sql + " LIMIT " + LIMIT) : Promise.resolve([]);
    const [institutions, rooms, comorphisms, morphisms, corridors, facts, kinds] = await Promise.all([
      q("institutions", "SELECT * FROM institutions ORDER BY name"),
      q("rooms", "SELECT * FROM rooms ORDER BY name"),
      q("comorphisms", "SELECT * FROM comorphisms ORDER BY name"),
      q("morphisms", "SELECT * FROM morphisms ORDER BY name"),
      q("corridors", "SELECT * FROM corridors ORDER BY name"),
      q("logic_facts", "SELECT * FROM logic_facts ORDER BY kind, edge, pos"),
      q("logic_edge_kinds", "SELECT * FROM logic_edge_kinds"),
    ]);
    const factsOf = new Map();
    for (const f of facts) { const k = f.kind + ":" + f.edge; if (!factsOf.has(k)) factsOf.set(k, []); factsOf.get(k).push(f); }
    const tag = (kind) => (r) => Object.assign(r, { kind, id: kind + ":" + r.name, facts: factsOf.get(kind + ":" + r.name) || [] });
    const { consequence, consRel } = await loadConsequence(ctx);
    return { institution: institutions.map(tag("institution")), room: rooms.map(tag("room")), comorphism: comorphisms.map(tag("comorphism")),
      morphism: morphisms.map(tag("morphism")), corridor: corridors.map(tag("corridor")), kinds, consequence, consRel };
  }
  // The consequence systems of the logics: those over a registered room (Lean checked the room and,
  // for a semantic reading, that the system is the room's consequence) and those registered with
  // the logic graph (`logic.consequence.*`), with the standard problems relating them.
  async function loadConsequence(ctx) {
    if (!has("consequence_systems")) return { consequence: [], consRel: [] };
    const consequence = await ctx.q("SELECT name, title, doc, reading, room, room_at, room_term, room_lift, decl, module, contexts, conclusions " +
      "FROM consequence_systems WHERE room IS NOT NULL OR name LIKE 'logic.consequence.%' ORDER BY name LIMIT 2000").catch(() => []);
    if (!consequence.length || !has("consequence_problems")) return { consequence, consRel: [] };
    const marks = consequence.map(() => "?").join(",");
    const rows = await ctx.q(`SELECT problem, shape, role, system, summary, title FROM consequence_problems WHERE problem IN ` +
      `(SELECT problem FROM consequence_problems WHERE system IN (${marks})) ORDER BY problem, pos LIMIT 5000`, consequence.map((c) => c.name)).catch(() => []);
    const by = new Map();
    for (const r of rows) {
      if (!by.has(r.problem)) by.set(r.problem, { problem: r.problem, shape: r.shape.replace(/^silmaril\.shapes\.consequence\./, ""), summary: r.summary, title: r.title });
      by.get(r.problem)[r.role] = r.system;
    }
    return { consequence, consRel: [...by.values()] };
  }
  const nodeKind = (k) => k === "corridor" ? "room" : "institution";
  const label = (r) => r.title || short(r.name);
  const params = (arg) => {
    const i = arg.indexOf("?");
    return { sel: decodeURIComponent(i < 0 ? arg : arg.slice(0, i)), p: new URLSearchParams(i < 0 ? "" : arg.slice(i + 1)) };
  };

  // The navigation of the logic pages: the Table | Graph views of the graph (a tab list; the search
  // text `q` is carried from one to the other), then the registries and the coverage. `on` is the
  // id of the current page; the table answers to `logics` (the default) and `logic-table`.
  function tabs(on, d, q) {
    const n = (k) => d ? ` <span>${d[k].length}</span>` : "";
    const qs = q ? "?q=" + encodeURIComponent(q) : "";
    const views = [["logics", "Table", "#/logics/" + qs], ["logic-graph", "Graph", "#/logic-graph/" + qs]];
    const cur = on === "logic-table" ? "logics" : on;
    const items = [["institutions", "Institutions" + n("institution")],
      ["comorphisms", "Comorphisms" + n("comorphism")], ["morphisms", "Morphisms" + n("morphism")], ["rooms", "Rooms" + n("room")],
      ["corridors", "Corridors" + n("corridor")],
      ["logic-consequence", "Consequence systems" + (d && d.consequence ? ` <span>${d.consequence.length}</span>` : "")], ["logic-coverage", "Coverage"]];
    return `<nav class="lg-tabs" aria-label="logic graph"><span class="lg-views" role="tablist" aria-label="view the logic graph as">` +
      views.map(([id, t, href]) => `<a role="tab" href="${href}" id="lg-tab-${id}" aria-selected="${id === cur}"${id === cur ? ' class="on" aria-current="page"' : ""}>${t}</a>`).join("") +
      `</span>` + items.map(([id, t]) => `<a href="#/${id}"${id === cur ? ' class="on" aria-current="page"' : ""}>${t}</a>`).join("") + `</nav>`;
  }
  function legend() {
    return `<div class="lg-legend" id="lg-legend" role="list" aria-label="legend">` +
      `<span role="listitem"><span class="lg-node"></span> institution</span>` +
      `<span role="listitem"><span class="lg-node room"></span> room</span>` +
      `<span role="listitem"><span class="lg-node fam"></span> family (has parameters)</span>` +
      EDGES.map((k) => `<span role="listitem" title="${ui.esc(KIND[k].what)}">${edgeSwatch(k)} ${k} <span class="lg-dir">(${k === "morphism" ? "sentences ←, models →" : "sentences →, models ←"})</span></span>`).join("") +
      `<span role="listitem"><svg width="34" height="10" aria-hidden="true"><line x1="1" y1="5" x2="33" y2="5" stroke="#9aa0a6" stroke-width="1.5" stroke-dasharray="1 2"/></svg> room is a fiber of</span>` +
      `<span role="listitem"><b>✓</b> has a proved fact</span></div>`;
  }

  // ---------- a sortable, filterable table over rows held in memory ----------
  // cols: [{ key, label, html(r), text(r), num }]. The filter matches every column's text.
  function grid(id, rows, cols, opts) {
    opts = opts || {};
    const txt = (c, r) => String(c.text ? c.text(r) : r[c.key] == null ? "" : r[c.key]);
    const body = rows.map((r, i) => `<tr data-i="${i}" data-text="${ui.esc(cols.map((c) => txt(c, r)).join(" ").toLowerCase())}">` +
      cols.map((c) => `<td${c.num ? ' class="num"' : ""}>${c.html ? c.html(r) : ui.esc(txt(c, r))}</td>`).join("") + "</tr>").join("");
    const html = `<div class="controls"><label>filter <input type="search" id="${id}-q" size="36" placeholder="name, declaration, module, Hets…" value="${ui.esc(opts.q || "")}"></label>` +
      `<span class="muted" id="${id}-n" aria-live="polite"></span></div>` +
      (rows.length ? `<div class="tablebox"><table class="lg-grid" id="${id}"><thead><tr>${cols.map((c, j) => `<th data-j="${j}" aria-sort="none"><button type="button">${ui.esc(c.label)}</button></th>`).join("")}</tr></thead><tbody>${body}</tbody></table></div>`
        : `<p class="muted">${opts.empty || "(none)"}</p>`);
    const init = () => {
      const t = document.getElementById(id), qi = document.getElementById(id + "-q"), n = document.getElementById(id + "-n");
      if (!qi) return;
      const apply = () => {
        if (!t) { n.textContent = ""; return; }
        const words = qi.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
        let shown = 0;
        for (const tr of t.tBodies[0].rows) { const ok = words.every((w) => tr.dataset.text.includes(w)); tr.hidden = !ok; if (ok) shown++; }
        n.textContent = `${shown} of ${rows.length}`;
        if (opts.onFilter) opts.onFilter(qi.value.trim());
      };
      qi.addEventListener("input", apply);
      if (t) for (const th of t.tHead.rows[0].cells) th.querySelector("button").addEventListener("click", () => {
        const j = +th.dataset.j, c = cols[j], dir = th.getAttribute("aria-sort") === "ascending" ? -1 : 1;
        for (const o of t.tHead.rows[0].cells) o.setAttribute("aria-sort", "none");
        th.setAttribute("aria-sort", dir > 0 ? "ascending" : "descending");
        const key = (tr) => { const r = rows[+tr.dataset.i]; return c.num ? +(r[c.key] || 0) : txt(c, r).toLowerCase(); };
        const trs = [...t.tBodies[0].rows].sort((a, b) => { const x = key(a), y = key(b); return (x < y ? -1 : x > y ? 1 : 0) * dir; });
        for (const tr of trs) t.tBodies[0].appendChild(tr);
      });
      apply();
    };
    return { html, init };
  }
  const factCell = (r) => r.facts.length ? r.facts.map((f) => `<span class="pill" title="${ui.esc(f.proof)}${f.instance_at ? " — only at " + ui.esc(f.instance_at) : " — for every instance"}${f.standard_axioms ? "" : " (non-standard axioms)"}">${ui.esc(f.property)}${f.instance_at ? " (at an instance)" : ""} ✓</span>`).join(" ") : "";
  const COLS = {
    institution: (d) => [
      { key: "name", label: "institution", html: (r) => rec("institution", r.name) },
      { key: "title", label: "title" },
      { key: "decl", label: "Lean declaration", html: (r) => code(r.decl) + (r.arity ? " " + family(r) : "") },
      { key: "edges", label: "edges", num: true, text: (r) => d.comorphism.concat(d.morphism).filter((e) => e.src === r.name || e.dst === r.name).length },
      { key: "rooms", label: "rooms", num: true, text: (r) => d.room.filter((x) => x.institution === r.name).length },
      { key: "hets", label: "Hets", html: hetsText, text: (r) => r.hets ? `${r.hets} ${r.hets_relation}` : "" },
      { key: "module", label: "module" }],
    room: () => [
      { key: "name", label: "room", html: (r) => rec("room", r.name) },
      { key: "institution", label: "fiber of", html: (r) => r.institution ? `${rec("institution", r.institution)} at ${code(r.signature)}` : '<span class="muted">—</span>', text: (r) => `${r.institution || ""} ${r.signature || ""}` },
      { key: "sen", label: "sentences", html: (r) => code(r.sen) },
      { key: "mod", label: "models", html: (r) => code(r.mod) },
      { key: "decl", label: "Lean declaration", html: (r) => code(r.decl) + (r.arity ? " " + family(r) : "") },
      { key: "module", label: "module" }],
    edge: (kind) => [
      { key: "name", label: kind, html: (r) => rec(kind, r.name) },
      { key: "src", label: "from", html: (r) => rec(nodeKind(kind), r.src) + (r.from_at ? ` <span class="muted">at ${ui.esc(r.from_at)}</span>` : "") },
      { key: "dst", label: "to", html: (r) => rec(nodeKind(kind), r.dst) + (r.to_at ? ` <span class="muted">at ${ui.esc(r.to_at)}</span>` : "") },
      { key: "title", label: "title" },
      { key: "facts", label: "facts", html: factCell, text: (r) => r.facts.map((f) => f.property).join(" ") },
      { key: "decl", label: "Lean declaration", html: (r) => code(r.decl) + (r.arity ? " " + family(r) : "") },
      { key: "hets", label: "Hets", html: hetsText, text: (r) => r.hets ? `${r.hets} ${r.hets_relation}` : "" },
      { key: "module", label: "module" }],
  };

  // ---------- the registries ----------
  function registry(kind) {
    return async (arg, ctx) => {
      style();
      if (!has("institutions")) return tabs(KIND[kind].plural) + missing;
      const d = await load(ctx);
      const rows = d[kind];
      const cols = kind === "institution" ? COLS.institution(d) : kind === "room" ? COLS.room() : COLS.edge(kind);
      const g = grid(`lg-${KIND[kind].plural}`, rows, cols, { q: params(arg).p.get("q") || "",
        empty: `No ${kind} is registered (<code>silmaril ${kind} &lt;name&gt; := &lt;decl&gt;</code>).` });
      const audit = has("logic_audit") ? (await ctx.q("SELECT count(*) AS n, sum(registered IS NULL) AS omitted FROM logic_audit WHERE object = ?", [kind]))[0] : null;
      const html = tabs(KIND[kind].plural, d) + `<h2>${KIND[kind].title} (${rows.length})</h2>` +
        `<p class="muted">A ${kind} is ${ui.esc(KIND[kind].what)}. Each row is a Lean declaration whose type Lean checked` +
        (EDGES.includes(kind) ? `; its endpoints were found by Lean among the registered ${nodeKind(kind)}s` : "") + ". " +
        (audit && audit.n ? `The audit found ${audit.n} declarations of this type in the scanned scope; ${audit.omitted || 0} are not registered (<a href="#/logic-coverage/?object=${kind}">coverage</a>).` : "") +
        `</p>` + g.html;
      return { html, init: g.init };
    };
  }

  // ---------- one record ----------
  function detail(kind) {
    return async (name, ctx) => {
      style();
      if (!has("institutions")) return missing;
      const d = await load(ctx);
      const r = d[kind].find((x) => x.name === name);
      if (!r) return tabs(KIND[kind].plural, d) + `<p class="err">no ${kind} ${ui.esc(name)}</p>`;
      const rows = [["is", ui.esc(KIND[kind].what)],
        ["Lean declaration", `${code(r.decl)} <span class="muted">in ${ui.esc(r.module)}</span> ${src(r.module, r.decl)}`],
        ["type", code(r.type)]];
      if (r.arity) rows.push(["parameters", `${code(r.params)} ${family(r)}`]);
      if (r.levels) rows.push(["universe parameters", code(r.levels)]);
      if (EDGES.includes(kind)) {
        const nk = nodeKind(kind);
        rows.push(["from", rec(nk, r.src) + (r.from_at ? ` <span class="muted">at</span> ${code(r.from_at)}` : "")]);
        rows.push(["to", rec(nk, r.dst) + (r.to_at ? ` <span class="muted">at</span> ${code(r.to_at)}` : "")]);
        const k = d.kinds.find((x) => x.kind === kind);
        if (k) rows.push(["direction", `sentences ${ui.esc(k.sentences)}; models ${ui.esc(k.models)}`]);
        rows.push(["facts", r.facts.length ? r.facts.map((f) => `<b>${ui.esc(f.property)}</b>${f.instance_at ? ` only at ${code(f.instance_at)}` : r.arity ? " for every instance" : ""} by ${code(f.proof)} <span class="muted">axioms: ${ui.esc(JSON.parse(f.axioms || "[]").join(", ") || "none")}${f.standard_axioms ? "" : " — non-standard"}</span>`).join("<br>")
          : '<span class="muted">none registered: no property of this edge is claimed</span>']);
        const parallel = d[kind].filter((x) => x !== r && x.src === r.src && x.dst === r.dst);
        if (parallel.length) rows.push(["parallel edges", parallel.map((x) => rec(kind, x.name)).join(", ")]);
        const back = EDGES.flatMap((k2) => d[k2].filter((x) => x.src === r.dst && x.dst === r.src).map((x) => rec(k2, x.name) + ` <span class="muted">(${k2})</span>`));
        if (back.length) rows.push(["opposite direction", back.join(", ")]);
      }
      if (kind === "room") {
        rows.push(["sentences", code(r.sen)], ["models", code(r.mod)]);
        rows.push(["fiber of", r.institution ? `${rec("institution", r.institution)} at the signature ${code(r.signature)}` : '<span class="muted">no registered institution found by Lean</span>']);
      }
      if (kind === "institution") {
        const rs = d.room.filter((x) => x.institution === r.name);
        if (rs.length) rows.push(["rooms", rs.map((x) => rec("room", x.name) + ` <span class="muted">at ${ui.esc(x.signature)}</span>`).join("<br>")]);
      }
      if (kind === "institution" || kind === "room") {
        const rooms = kind === "room" ? new Set([r.name]) : new Set(d.room.filter((x) => x.institution === r.name).map((x) => x.name));
        const cs = d.consequence.filter((c) => rooms.has(c.room));
        if (cs.length) rows.push(["consequence systems", cs.map((c) => consLink(c) + ` <span class="muted">${ui.esc(c.reading || "")}${c.room_at ? " at " + ui.esc(c.room_at) : ""}${kind === "institution" ? " over " + ui.esc(c.room) : ""}</span>`).join("<br>") +
          ` <br><a href="#/logic-consequence/">all consequence systems of the logics</a>`]);
      }
      if (kind === "institution" || kind === "room") {
        const out = EDGES.flatMap((k) => d[k].filter((e) => e.src === r.name && nodeKind(k) === kind).map((e) => `${edgeSwatch(k)} ${rec(k, e.name)} → ${rec(kind, e.dst)}`));
        const inc = EDGES.flatMap((k) => d[k].filter((e) => e.dst === r.name && nodeKind(k) === kind).map((e) => `${edgeSwatch(k)} ${rec(kind, e.src)} → ${rec(k, e.name)}`));
        rows.push(["outgoing", out.join("<br>") || '<span class="muted">none</span>'], ["incoming", inc.join("<br>") || '<span class="muted">none</span>']);
      }
      if (r.hets) rows.push(["Hets", hetsText(r) + ` <a href="#/logic-coverage">(pinned Hets list)</a>`]);
      if (r.source) rows.push(["source", ui.esc(r.source)]);
      if (r.scope) rows.push(["scope", ui.esc(r.scope)]);
      const h = tabs(KIND[kind].plural, d) + `<h2>${kind} <code>${ui.esc(r.name)}</code></h2>` + (r.title ? `<p><b>${ui.esc(r.title)}</b></p>` : "") +
        (r.doc ? `<p style="white-space:pre-wrap;max-width:860px">${ui.esc(r.doc)}</p>` : "") +
        `<p><a href="#/logic-graph/${encodeURIComponent(r.id)}">Show in the graph</a></p>` +
        `<dl>${rows.map(([k, v]) => `<dt>${ui.esc(k)}</dt><dd>${v}</dd>`).join("")}</dl>`;
      return h;
    };
  }

  // ---------- the table of everything ----------
  async function table(arg, ctx) {
    style();
    if (!has("institutions")) return tabs("logics") + missing;
    const d = await load(ctx);
    const all = [...NODES, ...EDGES].flatMap((k) => d[k]);
    const g = grid("lg-all", all, [
      { key: "kind", label: "kind", html: (r) => (EDGES.includes(r.kind) ? edgeSwatch(r.kind) + " " : "") + ui.esc(r.kind) },
      { key: "name", label: "name", html: (r) => rec(r.kind, r.name) },
      { key: "src", label: "from", html: (r) => r.src ? rec(nodeKind(r.kind), r.src) : "", text: (r) => r.src || "" },
      { key: "dst", label: "to", html: (r) => r.dst ? rec(nodeKind(r.kind), r.dst) : r.institution ? `<span class="muted">fiber of</span> ${rec("institution", r.institution)}` : "", text: (r) => r.dst || r.institution || "" },
      { key: "title", label: "title" },
      { key: "facts", label: "facts", html: factCell, text: (r) => r.facts.map((f) => f.property).join(" ") },
      { key: "arity", label: "params", num: true },
      { key: "hets", label: "Hets", html: hetsText, text: (r) => r.hets ? `${r.hets} ${r.hets_relation}` : "" },
      { key: "decl", label: "Lean declaration", html: (r) => code(r.decl) },
      { key: "module", label: "module" },
    ], { q: params(arg).p.get("q") || "", empty: "Nothing is registered.",
      onFilter: (q) => {
        history.replaceState(null, "", "#/logics/" + (q ? "?q=" + encodeURIComponent(q) : ""));
        const g = document.getElementById("lg-tab-logic-graph"); if (g) g.setAttribute("href", "#/logic-graph/" + (q ? "?q=" + encodeURIComponent(q) : ""));
      } });
    return { html: tabs("logics", d, params(arg).p.get("q") || "") + `<h2>Logic graph: every node and edge (${all.length})</h2>
<p class="muted">Search by any column (words are ANDed); click a header to sort. Edges go from → to as Lean writes their type.</p>` + legend() + g.html, init: g.init };
  }

  // ---------- consequence systems of the logics ----------
  const consLink = (c) => `<a href="#/system/${encodeURIComponent(c.name)}">${ui.esc(c.title || c.name)}</a>`;
  const READING = { derivability: "derivability (a proof system)", semantic: "semantic consequence (Lean checked: the room's consequence)" };
  const RELATION = { sound_at: "is sound for", tarski_closed: "satisfies identity, weakening and cut", complete_at: "is complete for",
    translates_at: "translates into", reflects_at: "translates conservatively (reflects) into" };
  const status = (r) => r.summary === "THM" ? `<span class="lg-proved" title="proved for every context and conclusion">✓ proved</span>` : ui.esc(r.summary || "open");
  async function consequencePage(arg, ctx) {
    style();
    if (!has("institutions")) return tabs("logic-consequence") + missing;
    const d = await load(ctx);
    const byName = new Map(d.consequence.map((c) => [c.name, c]));
    const roomOf = new Map(d.room.map((r) => [r.name, r]));
    const sys = (n) => byName.has(n) ? consLink(byName.get(n)) : `<a href="#/system/${encodeURIComponent(n)}">${ui.esc(n)}</a>`;
    const logic = (c) => {
      if (!c.room) return '<span class="muted">none: not over a registered room\'s sentences</span>';
      const rm = roomOf.get(c.room);
      return rec("room", c.room) + (c.room_at ? ` <span class="muted">at</span> ${code(c.room_at)}` : "") +
        (rm && rm.institution ? ` <span class="muted">fiber of</span> ${rec("institution", rm.institution)}` : "") + (c.room_lift ? ` <span class="muted">(sentences lifted by ULift)</span>` : "");
    };
    // `sound_at` S T is soundness when S is a derivability and T is not (a semantic consequence, or
    // HOL's sequent semantics, which is over propositions rather than a room's sentences); between two
    // derivabilities it says that every consequence of S is one of T
    const relName = (r) => r.shape !== "sound_at" ? (RELATION[r.shape] || r.shape)
      : (byName.get(r.S) || {}).reading === "derivability" && (byName.get(r.T) || {}).reading !== "derivability" ? "is sound for" : "is included in";
    const relOf = (c) => d.consRel.filter((r) => r.S === c.name || r.T === c.name).map((r) =>
      r.S === c.name ? `${ui.esc(relName(r))}${r.T ? " " + sys(r.T) : ""} ${status(r)}` : `${sys(r.S)} ${ui.esc(relName(r))} it ${status(r)}`).join("<br>");
    const q = params(arg).p.get("q") || "";
    const g = grid("lg-cons", d.consequence, [
      { key: "name", label: "system", html: consLink, text: (c) => `${c.name} ${c.title || ""}` },
      { key: "reading", label: "reading", html: (c) => c.reading ? ui.esc(c.reading) : '<span class="muted">—</span>' },
      { key: "room", label: "over the sentences of", html: logic, text: (c) => `${c.room || ""} ${c.room_at || ""}` },
      { key: "conclusions", label: "sentences", html: (c) => code(c.conclusions) },
      { key: "rel", label: "proved relations", html: relOf, text: (c) => d.consRel.filter((r) => r.S === c.name || r.T === c.name).map((r) => r.shape).join(" ") },
      { key: "decl", label: "Lean definition", html: (c) => code(c.decl) },
    ], { q, empty: "No consequence system of a logic is registered.",
      onFilter: (v) => history.replaceState(null, "", "#/logic-consequence/" + (v ? "?q=" + encodeURIComponent(v) : "")) });
    const rels = d.consRel.filter((r) => r.S);
    const relTable = rels.length ? `<div class="tablebox"><table class="lg-grid" id="lg-cons-rel"><thead><tr><th>system</th><th>relation</th><th>to</th><th>status</th><th>problem</th></tr></thead><tbody>` +
      rels.map((r) => `<tr><td>${sys(r.S)}</td><td>${ui.esc(relName(r))}</td><td>${r.T ? sys(r.T) : ""}</td><td>${status(r)}</td><td>${ui.link("problem", r.problem)}</td></tr>`).join("") +
      `</tbody></table></div>` : `<p class="muted">No relation is stated.</p>`;
    const matrix = await coverageMatrix(ctx, d);
    const html = tabs("logic-consequence", d) + `<h2>Consequence systems of the logics (${d.consequence.length})</h2>
<p style="max-width:860px">A consequence system relates a list of premises to a conclusion, <code>Γ ⊢ φ</code>. A logic has two kinds:
<b>derivability</b>, a proof system, and <b>semantic consequence</b>, truth in every model of the premises. They are separate
systems, and the only relation between them shown here is a proved one: <i>soundness</i>, derivability below semantic
consequence. "Is included in" relates two systems of one kind (every consequence of ZF is one of ZFC). No completeness is claimed. Each system names the registered room whose sentences it relates; Lean checks the
sentences and, for a semantic reading, that the system <i>is</i> the room's consequence (<code>roomSeq</code>, or
<code>roomTheorySeq</code> over the models of a theory such as PA or ZFC).</p>
<p class="muted" style="max-width:860px">Metamath's disjoint-variable conditions are part of its sentences (assertion frames), not premises.
The context of an MLTT judgment <code>Γ ⊢ J</code> is part of the judgment: the premises of these systems are whole judgments.
See <a href="#/systems">Systems</a> for every registered consequence system.</p>` + g.html + `<h3>Proved relations</h3>` + relTable + matrix;
    return { html, init: g.init };
  }

  // The coverage matrix (`consequence_matrix logic.consequence.coverage`): one row per family, one
  // column per feature; a cell is its status, the Lean declaration it is about and the supporting
  // theorems (each a link to its source), with the owner's note. Lean checked only that every named
  // declaration exists.
  const MARK = { proved: ["✓", "lg-proved"], defined: ["◆", "lg-defined"], registered: ["▣", "lg-registered"], absent: ["—", "lg-absent"], "not claimed": ["∅", "lg-absent"] };
  // a registered record's name in a note becomes a link to its page
  function recordLinks(text, d) {
    const kinds = [...NODES, ...EDGES];
    return ui.esc(text).replace(/logic\.[a-z0-9_]+(?:\.[a-z0-9_*]+)*/g, (n) => {
      for (const k of kinds) if (d[k].some((r) => r.name === n)) return rec(k, n);
      if (d.consequence.some((c) => c.name === n)) return `<a href="#/system/${encodeURIComponent(n)}">${n}</a>`;
      return n;
    });
  }
  async function coverageMatrix(ctx, d) {
    if (!has("consequence_matrix_cells")) return "";
    const cells = await ctx.q("SELECT pos, variant, reading, theorems, evidence, strength, note FROM consequence_matrix_cells WHERE matrix = ? ORDER BY pos LIMIT 2000",
      ["logic.consequence.coverage"]).catch(() => []);
    if (!cells.length) return "";
    const fams = [...new Set(cells.map((c) => c.variant))], feats = [...new Set(cells.map((c) => c.evidence))];
    const at = new Map(cells.map((c) => [c.variant + "\u0000" + c.evidence, c]));
    const srcLink = (n) => `<a href="#/source/${encodeURIComponent(n)}" title="${ui.esc(n)}">${ui.esc(n.split(".").slice(-1)[0])}</a>`;
    const cell = (c) => {
      if (!c) return "<td></td>";
      const [m, cls] = MARK[c.strength] || ["?", ""];
      let thms = []; try { thms = JSON.parse(c.theorems || "[]").map((t) => t.name); } catch (e) { thms = []; }
      return `<td class="lg-mx" data-strength="${ui.esc(c.strength)}" title="${ui.esc(c.note || c.strength)}"><span class="${cls}">${m} ${ui.esc(c.strength)}</span>` +
        `<div class="lg-mx-decls">${[c.reading, ...thms].map(srcLink).join(" ")}</div>${c.note ? `<div class="muted lg-mx-note">${recordLinks(c.note, d)}</div>` : ""}</td>`;
    };
    return `<h3 id="lg-coverage-matrix">Coverage matrix</h3><p class="muted" style="max-width:860px">Every logic family against every feature: its
abstract syntax, institution, derivability and semantic consequence, soundness, the structural and substitution laws, completeness,
concrete (S-expression) syntax and the institutions and consequence systems over it (formal definitions), and, separately, what is
registered here: the abstract systems and the concrete ones. Each cell names the Lean declarations (links to their source); Lean checked
that they exist. Registered records in a note link to their pages. ✓ proved, ◆ defined, ▣ registered, — absent, ∅ not claimed; every
absent or unclaimed cell says why.</p><div class="tablebox"><table class="lg-grid" id="lg-matrix"><thead><tr><th>family</th>` +
      feats.map((f) => `<th>${ui.esc(f)}</th>`).join("") + `</tr></thead><tbody>` +
      fams.map((v) => `<tr><th scope="row">${ui.esc(v)}</th>${feats.map((f) => cell(at.get(v + "\u0000" + f))).join("")}</tr>`).join("") +
      `</tbody></table></div>`;
  }

  // ---------- the graph ----------
  let cyi = null;
  async function graphView(arg, ctx) {
    style();
    if (!has("institutions")) return tabs("logic-graph") + missing;
    const d = await load(ctx);
    const { sel, p } = params(arg);
    const level = ["institution", "room", "both"].includes(p.get("level")) ? p.get("level") : (sel.startsWith("room:") || sel.startsWith("corridor:") ? "room" : "institution");
    const kinds = new Set((p.get("kinds") || EDGES.join(",")).split(",").filter((k) => EDGES.includes(k)));
    const total = NODES.reduce((n, k) => n + d[k].length, 0);
    const options = [...NODES, ...EDGES].flatMap((k) => d[k].map((r) => `<option value="${ui.esc(r.id)}"${r.id === sel ? " selected" : ""}>${ui.esc(k)}: ${ui.esc(r.name)}</option>`)).join("");
    const html = tabs("logic-graph", d, p.get("q") || "") + `<h2>Logic graph</h2>
<p class="muted">Registered institutions and the comorphisms and morphisms between them; one level down, rooms and the corridors between them.
Every arrow points from A to B as its Lean type <code>Inst.CoHom A B</code>, <code>Inst.Hom A B</code> or <code>Corridor A B</code> says.
This is the registry of this repository, not Hets's logic graph: see <a href="#/logic-coverage">Coverage</a> for how they relate and what is omitted.</p>
<div class="controls" role="group" aria-label="graph filters">
  <label>level <select id="lg-level"><option value="institution"${level === "institution" ? " selected" : ""}>institutions</option><option value="room"${level === "room" ? " selected" : ""}>rooms</option><option value="both"${level === "both" ? " selected" : ""}>both</option></select></label>
  ${EDGES.map((k) => `<label title="${ui.esc(KIND[k].what)}"><input type="checkbox" class="lg-kind" value="${k}"${kinds.has(k) ? " checked" : ""}> ${k}s</label>`).join("")}
  <label><input type="checkbox" id="lg-iso"${p.get("isolated") === "0" ? "" : " checked"}> unconnected nodes</label>
  <label>search <input type="search" id="lg-q" size="18" value="${ui.esc(p.get("q") || "")}" placeholder="name, title, Hets…"></label>
  <label>go to <select id="lg-go" style="max-width:16em"><option value="">—</option>${options}</select></label>
  <span>
  <button type="button" id="lg-fit" title="fit the graph to the view">Fit</button>
  <button type="button" id="lg-zin" aria-label="zoom in">+</button><button type="button" id="lg-zout" aria-label="zoom out">−</button>
  <label title="clusters: each region laid out on its own; layered: one left-to-right flow over everything">layout <select id="lg-layout"><option value="clusters">clusters</option><option value="layered"${p.get("layout") === "layered" ? " selected" : ""}>layered (one flow)</option></select></label>
  <label title="draw a box around the logics of each library region"><input type="checkbox" id="lg-group"${p.get("group") === "0" ? "" : " checked"}> group by region</label>
  <button type="button" id="lg-reset">Reset</button></span>
  <span class="muted" id="lg-count" aria-live="polite"></span>
</div>${legend()}
<div id="lgwrap"><div id="lgcy" tabindex="0" role="img" aria-label="logic graph; use the go-to list or the Table tab for a text view"></div>
<div id="lgside" aria-live="polite"><p class="muted">Select a node or an edge for its details (click, or use <b>go to</b>). Double-click opens its page.</p></div></div>`;
    const init = () => {
      if (typeof cytoscape !== "function") { document.getElementById("lgcy").innerHTML = `<div class="lg-empty">The graph library did not load; the <a href="#/logic-table">table</a> has the same content.</div>`; return; }
      const state = { level, kinds, q: p.get("q") || "", iso: p.get("isolated") !== "0", layout: p.get("layout") === "layered" ? "layered" : "clusters", group: p.get("group") !== "0", sel };
      const writeUrl = () => {
        const qs = new URLSearchParams();
        if (state.level !== "institution") qs.set("level", state.level);
        if (state.kinds.size !== EDGES.length) qs.set("kinds", [...state.kinds].join(","));
        if (state.q) qs.set("q", state.q);
        if (!state.iso) qs.set("isolated", "0");
        if (state.layout !== "clusters") qs.set("layout", state.layout);
        if (!state.group) qs.set("group", "0");
        const s = qs.toString();
        history.replaceState(null, "", "#/logic-graph/" + (state.sel ? encodeURIComponent(state.sel) : "") + (s ? "?" + s : ""));
        const t = document.getElementById("lg-tab-logics"); if (t) t.setAttribute("href", "#/logics/" + (state.q ? "?q=" + encodeURIComponent(state.q) : ""));
      };
      // Parallel edges of one kind between the same two nodes are drawn as one edge ("3 comorphisms"); selecting it lists them.
      let bundles = new Map(), bundleOf = new Map();
      const bundle = (edges) => {
        bundles = new Map(); bundleOf = new Map();
        for (const e of edges) {
          const s = nodeKind(e.kind) + ":" + e.src, t = nodeKind(e.kind) + ":" + e.dst, key = `${e.kind}|${s}|${t}`;
          if (!bundles.has(key)) bundles.set(key, { key, kind: e.kind, source: s, target: t, members: [] });
          bundles.get(key).members.push(e);
        }
        for (const b of bundles.values()) { b.id = b.members.length === 1 ? b.members[0].id : "bundle:" + b.key; for (const e of b.members) bundleOf.set(e.id, b); }
        return bundles;
      };
      // The clusters layout: each region laid out on its own (layered, top-down; its unconnected logics in a grid below), and the
      // regions packed in rows to the viewport's proportions. Deterministic: the same database draws the same picture.
      // Shelf packing: place the blocks (each { coll, w, h, x1, y1 }) in rows of about `width`.
      const pack = (blocks, width, gapX, gapY) => {
        let x = 0, y = 0, rowH = 0;
        for (const b of blocks) {
          if (x > 0 && x + b.w > width) { x = 0; y += rowH + gapY; rowH = 0; }
          b.coll.shift({ x: x - b.x1, y: y - b.y1 });
          x += b.w + gapX; rowH = Math.max(rowH, b.h);
        }
      };
      const block = (coll) => { const bb = coll.boundingBox({ includeLabels: false }); return { coll, w: bb.w, h: bb.h, x1: bb.x1, y1: bb.y1 }; };
      // The clusters layout: within each region, every connected component laid out on its own
      // (layered, top-down) and its unconnected logics in a grid, packed to a near-square block; then
      // the regions packed in rows to the viewport's proportions. Deterministic: the same database
      // draws the same picture.
      const clusters = () => {
        const groups = new Map();
        for (const n of cyi.nodes().filter((x) => !x.data("region"))) {
          const g = n.data("parent") || "all";
          if (!groups.has(g)) groups.set(g, cyi.collection());
          groups.set(g, groups.get(g).union(n));
        }
        const ratio = Math.max(0.6, (cyi.width() || 900) / (cyi.height() || 600));
        const regions = [];
        for (const [, ns] of [...groups].sort((a, b) => b[1].length - a[1].length || (a[0] < b[0] ? -1 : 1))) {
          const inner = ns.edgesWith(ns).filter((e) => !e.isLoop());
          const blocks = [];
          const seen = new Set();
          const comps = [];
          for (const n of ns) {
            if (seen.has(n.id())) continue;
            let comp = n.union(n), frontier = n.union(n);
            while (frontier.length) {
              const next = frontier.connectedEdges().intersection(inner).connectedNodes().intersection(ns).not(comp);
              comp = comp.union(next); frontier = next;
            }
            comp.forEach((x) => seen.add(x.id()));
            comps.push(comp);
          }
          const alone = cyi.collection().union(comps.filter((c) => c.length === 1).reduce((a, c) => a.union(c), cyi.collection()));
          for (const comp of comps.filter((c) => c.length > 1).sort((a, b) => b.length - a.length)) {
            comp.union(inner.intersection(comp.connectedEdges())).layout({ name: "dagre", rankDir: "TB", nodeSep: 18, rankSep: 60, edgeSep: 8, animate: false, fit: false }).run();
            blocks.push(block(comp));
          }
          if (alone.length) {
            const cols = Math.max(1, Math.ceil(Math.sqrt(alone.length * 1.6)));
            alone.sort((a, b) => (a.data("label") < b.data("label") ? -1 : 1)).forEach((n, i) => n.position({ x: (i % cols) * 175, y: Math.floor(i / cols) * 52 }));
            blocks.push(block(alone));
          }
          const area = blocks.reduce((a, b) => a + (b.w + 40) * (b.h + 50), 0);
          pack(blocks, Math.max(Math.sqrt(area * 1.4), ...blocks.map((b) => b.w)), 40, 50);
          regions.push(block(ns));
        }
        const area = regions.reduce((a, b) => a + (b.w + 60) * (b.h + 70), 0);
        pack(regions, Math.max(Math.sqrt(area * ratio), ...regions.map((b) => b.w)), 60, 70);
      };
      const draw = () => {
        const showInst = state.level !== "room", showRoom = state.level !== "institution";
        const nodes = [...(showInst ? d.institution : []), ...(showRoom ? d.room : [])];
        const ids = new Set(nodes.map((n) => n.id));
        const edges = EDGES.filter((k) => state.kinds.has(k)).flatMap((k) => d[k]).filter((e) => ids.has(nodeKind(e.kind) + ":" + e.src) && ids.has(nodeKind(e.kind) + ":" + e.dst));
        const fibers = state.level === "both" ? d.room.filter((r) => r.institution && ids.has("institution:" + r.institution)) : [];
        const touched = new Set([...edges.flatMap((e) => [nodeKind(e.kind) + ":" + e.src, nodeKind(e.kind) + ":" + e.dst]), ...fibers.flatMap((r) => [r.id, "institution:" + r.institution])]);
        const shownNodes = state.iso ? nodes : nodes.filter((n) => touched.has(n.id));
        // A region is the first segment of the record name, or the first two when that region would
        // hold more than 30 of the drawn nodes (the `logic` tree is split by topic)
        const first = (n) => n.name.split(".")[0];
        const sizes = new Map();
        for (const n of shownNodes) sizes.set(first(n), (sizes.get(first(n)) || 0) + 1);
        const regionOf = (n) => sizes.get(first(n)) > 30 ? n.name.split(".").slice(0, 2).join(".") : first(n);
        const regions = state.group ? [...new Set(shownNodes.map(regionOf))] : [];
        const els = regions.map((g) => ({ data: { id: "region:" + g, label: g, region: 1 } }))
          .concat(shownNodes.map((n) => ({ data: Object.assign({ id: n.id, label: label(n) + (n.arity ? " ⋯" : ""), kind: n.kind, fam: n.arity ? 1 : 0 },
            state.group ? { parent: "region:" + regionOf(n) } : {}) })))
          .concat([...bundle(edges).values()].map((b) => ({ data: { id: b.id, source: b.source, target: b.target, kind: b.kind, n: b.members.length,
            label: (b.members.length > 1 ? `${b.members.length} ${b.kind}s` : short(b.members[0].name)) + (b.members.some((e) => e.facts.length) ? " ✓" : "") } })))
          .concat(fibers.filter((r) => shownNodes.some((n) => n.id === r.id)).map((r) => ({ data: { id: "fiber:" + r.name, source: r.id, target: "institution:" + r.institution, kind: "fiber", label: "" } })));
        if (cyi) { cyi.destroy(); cyi = null; }
        const box = document.getElementById("lgcy");
        if (!box) return;
        box.querySelectorAll(".lg-empty").forEach((x) => x.remove());
        document.getElementById("lg-count").textContent = `${shownNodes.length} nodes, ${edges.length} edges shown (of ${total} nodes, ${EDGES.reduce((n, k) => n + d[k].length, 0)} edges)`;
        window.explore.logicGraph = { nodes: shownNodes.length, edges: edges.length, fibers: fibers.length, level: state.level };
        if (!shownNodes.length) {
          box.insertAdjacentHTML("beforeend", `<div class="lg-empty">${total ? "Nothing matches these filters. Reset, or choose another level." : "No institution or room is registered yet."}</div>`);
          return;
        }
        cyi = cytoscape({ container: box, elements: els, minZoom: 0.1, maxZoom: 3, wheelSensitivity: 0.25,
          style: [
            { selector: "node", style: { label: "data(label)", "text-wrap": "wrap", "text-max-width": 150, "font-size": 11, "text-valign": "center", "text-halign": "center",
              width: 160, height: 38, shape: "round-rectangle", "background-color": "#fff", color: "#0b0b0b", "border-width": 1.5, "border-color": "#52514e" } },
            { selector: "node[kind = 'room']", style: { shape: "ellipse", "background-color": "#f1f3f5", width: 140, height: 40 } },
            { selector: "node[fam = 1]", style: { "border-style": "dashed" } },
            { selector: "edge", style: { width: 2, "curve-style": "bezier", "target-arrow-shape": "triangle", "arrow-scale": 1.1, label: "data(label)", "font-size": 9,
              "text-rotation": "autorotate", "text-background-color": "#fcfcfb", "text-background-opacity": 0.9, "text-background-padding": 2, color: "#52514e" } },
            ...EDGES.map((k) => ({ selector: `edge[kind = '${k}']`, style: { "line-color": KIND[k].color, "target-arrow-color": KIND[k].color, "line-style": KIND[k].line === "solid" ? "solid" : KIND[k].line } })),
            { selector: "edge[kind = 'morphism']", style: { "line-dash-pattern": [7, 4] } },
            { selector: "edge[kind = 'corridor']", style: { "line-dash-pattern": [2, 3], width: 2.5 } },
            { selector: "edge:loop", style: { "loop-direction": "-30deg", "loop-sweep": "-70deg", "control-point-step-size": 70 } },
            { selector: "edge[kind = 'fiber']", style: { "line-color": "#9aa0a6", "target-arrow-shape": "none", "line-style": "dotted", width: 1.2 } },
            { selector: "node[region = 1]", style: { shape: "round-rectangle", "background-color": "#f4f6f8", "background-opacity": 0.6, "border-width": 1,
              "border-color": "#c9ced3", label: "data(label)", "text-valign": "top", "text-halign": "center", "font-size": 13, "font-weight": 600, color: "#52514e", padding: 14 } },
            { selector: ".faded", style: { opacity: 0.18 } },
            { selector: ".hit", style: { "underlay-color": "#eda100", "underlay-opacity": 0.45, "underlay-padding": 5 } },
            { selector: ":selected", style: { "border-width": 3, "border-color": "#2f5d9e", width: 3, "overlay-color": "#2f5d9e", "overlay-opacity": 0.12 } },
          ],
          layout: state.layout === "layered" && !state.group ? { name: "dagre", rankDir: "LR", nodeSep: 24, rankSep: 80, edgeSep: 10, animate: false } : { name: "preset" } });
        if (state.layout !== "layered" || state.group) clusters();
        cyi.on("tap", "node, edge", (e) => { if (e.target.data("region")) return;
          const b = [...bundles.values()].find((x) => x.id === e.target.id());
          select(b ? b.members[0].id : e.target.id(), false); });
        cyi.on("tap", (e) => { if (e.target === cyi) select("", false); });
        cyi.on("dbltap", "node, edge", (e) => { const id = state.sel && bundleOf.get(state.sel) && bundleOf.get(state.sel).id === e.target.id() ? state.sel : e.target.id();
          const [k, ...n] = id.split(":"); if (KIND[k]) location.hash = `#/${k}/${encodeURIComponent(n.join(":"))}`; });
        search();
        if (state.sel && cyi.getElementById(bundleOf.has(state.sel) ? bundleOf.get(state.sel).id : state.sel).length) select(state.sel, true); else fit();
      };
      // fit, without blowing a small graph up past a readable size
      const fit = () => { if (!cyi) return; cyi.fit(undefined, 24); if (cyi.zoom() > 1.2) { cyi.zoom(1.2); cyi.center(); } };
      const all = Object.fromEntries([...NODES, ...EDGES].flatMap((k) => d[k].map((r) => [r.id, r])));
      const side = document.getElementById("lgside");
      const select = (id, center) => {
        state.sel = id; writeUrl();
        const go = document.getElementById("lg-go"); if (go) go.value = all[id] ? id : "";
        if (!cyi) return;
        cyi.elements().unselect().removeClass("faded");
        const r = all[id];
        if (!r) { side.innerHTML = `<p class="muted">Select a node or an edge for its details (click, or use <b>go to</b>). Double-click opens its page.</p>`; search(); return; }
        const b = bundleOf.get(id);
        const el = cyi.getElementById(b ? b.id : id);
        if (el.length) {
          el.select();
          const near = el.isNode() ? el.closedNeighborhood() : el.union(el.connectedNodes());
          cyi.elements().not(near).not(near.parents()).addClass("faded");
          if (center) { cyi.fit(near.nodes().union(near.edges()), 80); if (cyi.zoom() > 1.4) cyi.zoom({ level: 1.4, position: el.isNode() ? el.position() : el.midpoint() }); }
        }
        const e = EDGES.includes(r.kind);
        let h = `<h3>${e ? edgeSwatch(r.kind) + " " : ""}${ui.esc(r.kind)} ${rec(r.kind, r.name)}</h3>` + (r.title ? `<p><b>${ui.esc(r.title)}</b></p>` : "") +
          `<p class="muted">${ui.esc(KIND[r.kind].what)}</p><dl>`;
        if (e) h += `<dt>from</dt><dd>${rec(nodeKind(r.kind), r.src)}${r.from_at ? " at " + code(r.from_at) : ""}</dd><dt>to</dt><dd>${rec(nodeKind(r.kind), r.dst)}${r.to_at ? " at " + code(r.to_at) : ""}</dd>` +
          `<dt>facts</dt><dd>${factCell(r) || '<span class="muted">none claimed</span>'}</dd>`;
        if (r.kind === "room") h += `<dt>sentences</dt><dd>${code(r.sen)}</dd><dt>models</dt><dd>${code(r.mod)}</dd>` + (r.institution ? `<dt>fiber of</dt><dd>${rec("institution", r.institution)} at ${code(r.signature)}</dd>` : "");
        if (!e) {
          const deg = EDGES.flatMap((k) => d[k].filter((x) => nodeKind(k) === r.kind && (x.src === r.name || x.dst === r.name)));
          h += `<dt>edges</dt><dd>${deg.length ? deg.map((x) => `${edgeSwatch(x.kind)} ${x.src === r.name ? "→ " + rec(r.kind, x.dst) : "← " + rec(r.kind, x.src)} <span class="muted">by</span> ${rec(x.kind, x.name, short(x.name))}`).join("<br>") : '<span class="muted">none</span>'}</dd>`;
        }
        h += `<dt>declaration</dt><dd>${code(r.decl)}${r.arity ? " " + family(r) : ""} ${src(r.module, r.decl)}</dd><dt>module</dt><dd>${ui.esc(r.module)}</dd>`;
        if (r.hets) h += `<dt>Hets</dt><dd>${hetsText(r)}</dd>`;
        h += `</dl>` + (r.doc ? `<p class="muted" style="white-space:pre-wrap">${ui.esc(r.doc.length > 600 ? r.doc.slice(0, 600) + "…" : r.doc)}</p>` : "") +
          `<p><a href="#/${r.kind}/${encodeURIComponent(r.name)}">Open the ${ui.esc(r.kind)}'s page</a></p>`;
        if (b && b.members.length > 1) h += `<p class="muted">One of ${b.members.length} parallel ${ui.esc(b.kind)}s drawn as one edge: ` +
          b.members.map((m) => `<a href="#/logic-graph/${encodeURIComponent(m.id)}" data-sel="${ui.esc(m.id)}">${ui.esc(short(m.name))}</a>`).join(", ") + `</p>`;
        if (el.length === 0) h = `<p class="note">Not drawn with the current filters.</p>` + h;
        side.innerHTML = h;
      };
      side.addEventListener("click", (e) => { const a = e.target.closest && e.target.closest("a[data-sel]"); if (!a) return; e.preventDefault(); select(a.dataset.sel, false); });
      const search = () => {
        if (!cyi) return;
        cyi.elements().removeClass("hit");
        const words = state.q.toLowerCase().split(/\s+/).filter(Boolean);
        if (!words.length) return;
        const text = (r) => [r.name, r.title, r.decl, r.hets, r.module, r.doc].join(" ").toLowerCase();
        const hits = cyi.elements().filter((el) => {   // region boxes are not records; a bundle matches when one of its edges does
          const b = [...bundles.values()].find((x) => x.id === el.id());
          const rs = b ? b.members : all[el.id()] ? [all[el.id()]] : [];
          return rs.some((r) => words.every((w) => text(r).includes(w))); });
        hits.addClass("hit");
        document.getElementById("lg-count").textContent += ` · ${hits.length} match${hits.length === 1 ? "" : "es"}`;
      };
      const $id = (x) => document.getElementById(x);
      $id("lg-level").addEventListener("change", (e) => { state.level = e.target.value; writeUrl(); draw(); });
      for (const c of document.querySelectorAll(".lg-kind")) c.addEventListener("change", () => {
        state.kinds = new Set([...document.querySelectorAll(".lg-kind")].filter((x) => x.checked).map((x) => x.value)); writeUrl(); draw(); });
      $id("lg-iso").addEventListener("change", (e) => { state.iso = e.target.checked; writeUrl(); draw(); });
      let timer = null;
      $id("lg-q").addEventListener("input", (e) => { clearTimeout(timer); timer = setTimeout(() => { state.q = e.target.value.trim(); writeUrl(); draw(); }, 200); });
      $id("lg-go").addEventListener("change", (e) => {
        const id = e.target.value, r = all[id];
        if (r && cyi && !cyi.getElementById(id).length) {   // not drawn: switch to its level and kinds
          state.level = NODES.includes(r.kind) ? r.kind : nodeKind(r.kind);
          if (EDGES.includes(r.kind)) state.kinds.add(r.kind);
          $id("lg-level").value = state.level;
          for (const c of document.querySelectorAll(".lg-kind")) c.checked = state.kinds.has(c.value);
          state.sel = id; writeUrl(); draw(); return;
        }
        select(id, true);
      });
      $id("lg-fit").addEventListener("click", fit);
      $id("lg-zin").addEventListener("click", () => cyi && cyi.zoom({ level: cyi.zoom() * 1.25, renderedPosition: { x: cyi.width() / 2, y: cyi.height() / 2 } }));
      $id("lg-zout").addEventListener("click", () => cyi && cyi.zoom({ level: cyi.zoom() / 1.25, renderedPosition: { x: cyi.width() / 2, y: cyi.height() / 2 } }));
      $id("lg-layout").addEventListener("change", (e) => { state.layout = e.target.value;
        if (state.layout === "layered") { state.group = false; $id("lg-group").checked = false; } writeUrl(); draw(); });
      $id("lg-group").addEventListener("change", (e) => { state.group = e.target.checked; writeUrl(); draw(); });
      $id("lg-reset").addEventListener("click", () => { location.hash = "#/logic-graph"; });
      // keyboard: + / − zoom, 0 fits, Escape clears the selection
      $id("lgcy").addEventListener("keydown", (e) => {
        if (!cyi) return;
        if (e.key === "+" || e.key === "=") $id("lg-zin").click();
        else if (e.key === "-") $id("lg-zout").click();
        else if (e.key === "0") $id("lg-fit").click();
        else if (e.key === "Escape") select("", false);
        else return;
        e.preventDefault();
      });
      draw();
    };
    return { html, init, dispose: () => { if (cyi) { cyi.destroy(); cyi = null; } } };
  }

  // ---------- coverage ----------
  async function coverage(arg, ctx) {
    style();
    if (!has("institutions")) return tabs("logic-coverage") + missing;
    const d = await load(ctx);
    const { p } = params(arg);
    let h = tabs("logic-coverage", d) + `<h2>Coverage</h2>
<p class="muted">Five separate questions, answered separately: what the registry omits from this repository's Lean declarations (the audit),
how the registry relates to the Hets logic graph (by the relations records claim), what each entry of the curated catalogue the registry was
ported from is here, what the graph leaves out and why, and which logic families have Lean developments that are not in this repository yet. None of them says that this repository covers Hets.</p>`;
    // 1. the audit
    const cov = has("logic_coverage") ? await ctx.q("SELECT * FROM logic_coverage ORDER BY object, layer") : [];
    const scope = has("logic_audit") ? await ctx.q("SELECT DISTINCT scope, module FROM logic_audit LIMIT 10") : [];
    h += `<h3>Audit of Lean declarations</h3>`;
    if (!cov.length) h += `<p class="muted">No audit in this database (<code>silmaril logic_audit</code>).</p>`;
    else {
      const tot = (k) => cov.reduce((n, r) => n + (r[k] || 0), 0);
      h += `<p class="muted">Every declaration under <code>${ui.esc(scope.map((s) => s.scope).join(", "))}</code> reachable from <code>${ui.esc(scope.map((s) => s.module).join(", "))}</code>
that is not a theorem and whose type, after its binders, is an institution, comorphism, morphism, room or corridor. A family (arity &gt; 0) is
registered as a family. <b>Generic</b> declarations are constructions over an arbitrary institution, room or map (a binder ranges over them,
as in theories <code>Inst.th A</code> or identities <code>CoHom.id A</code>): they are not nodes or edges, and the registry rejects them.
Other omissions are declarations of Raw modules reached through public imports (not an API), and edges whose endpoint is not a registered
declaration (an unnamed term such as <code>Inst.th FOL.inst</code> or a structure field). Proofs modules are not imported and not audited.</p>
<div class="lg-stats">${[["declarations", tot("declarations")], ["registered", tot("registered")], ["omitted", tot("omitted")], ["generic constructions", tot("generic")], ["closed (arity 0)", tot("closed")]]
  .map(([k, v]) => `<div class="lg-stat"><b>${v}</b><span>${k}</span></div>`).join("")}</div>`;
      h += await ui.table(cov, ["object", "layer", "declarations", "closed", "generic", "registered", "omitted", "omitted_generic"],
        { label: { omitted: "omitted (not generic)", omitted_generic: "omitted generic" } });
      const om = await ctx.q("SELECT name, decl, object, arity, generic, decl_module, layer FROM logic_audit WHERE registered IS NULL ORDER BY generic, layer, object, decl LIMIT " + LIMIT);
      const g = grid("lg-omitted", om, [
        { key: "object", label: "kind" }, { key: "decl", label: "declaration", html: (r) => code(r.decl) + " " + src(r.decl_module, r.decl) },
        { key: "generic", label: "why", text: (r) => r.generic ? "generic construction" : r.layer === "raw" ? "in a Raw module (not an API)" : "an endpoint is not a registered declaration" },
        { key: "arity", label: "arity", num: true }, { key: "decl_module", label: "module" }],
        { q: p.get("object") || "", empty: "Nothing is omitted." });
      h += `<h4>Omitted declarations (${om.length})</h4>` + g.html;
      var initOmitted = g.init;
    }
    // 2. Hets
    h += `<h3>Relation to the Hets logic graph</h3>`;
    if (!has("hets_coverage")) h += `<p class="muted">No Hets list in this database.</p>`;
    else {
      const hl = await ctx.q("SELECT h.*, l.hets_rev, l.hets_file FROM hets_coverage h LEFT JOIN hets_logics l ON l.hets_name = h.hets_name AND h.hets_kind = 'logic' ORDER BY h.hets_kind DESC, h.hets_name");
      const hc = await ctx.q("SELECT hets_name, hets_from, hets_to, hets_rev FROM hets_comorphisms");
      const ends = new Map(hc.map((c) => [c.hets_name, c]));
      const rev = (hl.find((r) => r.hets_rev) || hc[0] || {}).hets_rev || "";
      const nl = hl.filter((r) => r.hets_kind === "logic"), nc = hl.filter((r) => r.hets_kind === "comorphism");
      const cnt = (l, k) => l.filter((r) => r[k] > 0).length;
      h += `<p class="muted">The logics and comorphisms Hets registers (<code>logicList</code>, <code>comorphismList</code>) at
<a href="https://github.com/spechub/Hets/tree/${ui.esc(rev)}" target="_blank" rel="noopener noreferrer">spechub/Hets@${ui.esc(rev.slice(0, 12))}</a>, names only.
A record relates to one by its own claim: <b>corresponds</b>, <b>fragment</b> or <b>related</b>. Hets lists no institution morphisms.</p>
<div class="lg-stats"><div class="lg-stat"><b>${cnt(nl, "related")} / ${nl.length}</b><span>Hets logics with a related institution</span></div>
<div class="lg-stat"><b>${cnt(nl, "corresponds")} / ${nl.length}</b><span>… one that corresponds</span></div>
<div class="lg-stat"><b>${cnt(nc, "related")} / ${nc.length}</b><span>Hets comorphisms with a related edge</span></div>
<div class="lg-stat"><b>${cnt(nc, "corresponds")} / ${nc.length}</b><span>… one that corresponds</span></div></div>`;
      const relCell = (r) => r.records ? r.records.split(" ").map((x) => { const i = x.lastIndexOf(":"); const n = x.slice(0, i);
        const kind = r.hets_kind === "logic" ? "institution" : (d.comorphism.some((e) => e.name === n) ? "comorphism" : d.morphism.some((e) => e.name === n) ? "morphism" : "corridor");
        return `${rec(kind, n)} ${pill(x.slice(i + 1))}`; }).join("<br>") : '<span class="muted">none</span>';
      const g2 = grid("lg-hets", hl, [
        { key: "hets_kind", label: "Hets kind" },
        { key: "hets_name", label: "Hets name", html: (r) => code(r.hets_name) + (ends.has(r.hets_name) ? ` <span class="muted">${ui.esc(ends.get(r.hets_name).hets_from)} → ${ui.esc(ends.get(r.hets_name).hets_to)}</span>` : "") },
        { key: "flag", label: "Hets build flag", text: (r) => r.flag || "" },
        { key: "records", label: "registered records (relation)", html: relCell, text: (r) => r.records || "none" },
      ]);
      h += g2.html;
      var initHets = g2.init;
    }
    // 3. the curated catalogue, entry by entry
    h += `<h3>The curated catalogue, entry by entry</h3>`;
    const cat = has("logic_catalogue") ? await ctx.q("SELECT * FROM logic_catalogue ORDER BY entry DESC, catalogue_id") : [];
    if (!cat.length) h += `<p class="muted">No catalogue in this database.</p>`;
    else {
      const n = (e, st) => cat.filter((r) => r.entry === e && (!st || r.status === st)).length;
      const parse = (v) => { try { const x = JSON.parse(v || "[]"); return Array.isArray(x) ? x : []; } catch (e) { return []; } };
      h += `<p class="muted">The ${n("node")} logics and ${n("edge")} maps of the curated catalogue this registry was ported from, each with what it is here:
<b>registered</b> (a registered record), <b>represented</b> (an instance or endpoint of registered records), <b>not institution-typed</b>
(a logical system, proof calculus, translation of proofs, family of institutions or theorem: outside the five registry kinds) or
<b>prospective</b> (no Lean declaration). For every entry that has evidence (all but the prospective ones), Lean checked that each evidence
declaration exists here; for every entry, that each record it names is registered.
An empty list of pending families does not mean every entry is a registered institution or map: the statuses below say which are.</p>
<div class="lg-stats">${[["node", "logics"], ["edge", "maps"]].map(([e, t]) => ["registered", "represented", "not-institution-typed", "prospective"]
  .map((st) => `<div class="lg-stat"><b>${n(e, st)} / ${n(e)}</b><span>${t}: ${st.replace(/-/g, " ")}</span></div>`).join("")).join("")}</div>`;
      const g3 = grid("lg-catalogue", cat, [
        { key: "entry", label: "entry" }, { key: "catalogue_id", label: "id", html: (r) => code(r.catalogue_id) },
        { key: "title", label: "title" }, { key: "status", label: "status", html: (r) => pill(r.status) },
        { key: "records", label: "registered records", html: (r) => parse(r.records).map((x) => { const i = x.indexOf(":"); return rec(x.slice(0, i), x.slice(i + 1)); }).join("<br>"),
          text: (r) => parse(r.records).join(" ") },
        { key: "evidence", label: "Lean evidence", html: (r) => parse(r.evidence).map(code).join("<br>"), text: (r) => parse(r.evidence).join(" ") },
        { key: "reason", label: "reason", text: (r) => r.reason || "" }], { q: p.get("catalogue") || "" });
      h += g3.html;
      var initCat = g3.init;
    }
    // 4. what the graph leaves out
    h += `<h3>What the graph leaves out</h3>`;
    const ex = has("logic_exclusions") ? await ctx.q("SELECT * FROM logic_exclusions ORDER BY category, name") : [];
    if (!ex.length) h += `<p class="muted">No exclusions in this database.</p>`;
    else {
      const parse = (v) => { try { const x = JSON.parse(v || "[]"); return Array.isArray(x) ? x : []; } catch (e) { return []; } };
      const sum = (c) => ex.filter((r) => r.category === c).reduce((n, r) => n + r.count, 0);
      h += `<p class="muted">Declarations of an institution-graph type that no record can hold (each with its exact reason; Lean checked that each exists
and is not registered), modules not in this repository because they read fixtures generated by external tools, and the parts of the source
developments outside the institution graph.</p>
<div class="lg-stats">${[["unregistrable-declaration", "unregistrable declarations"], ["fixture-dependent", "fixture-dependent modules"], ["out-of-scope", "out-of-scope modules"]]
  .map(([c, t]) => `<div class="lg-stat"><b>${sum(c)}</b><span>${t}</span></div>`).join("")}</div>`;
      const g4 = grid("lg-exclusions", ex, [
        { key: "category", label: "category" }, { key: "title", label: "what", html: (r) => r.category === "unregistrable-declaration" ? code(r.title) : ui.esc(r.title) },
        { key: "count", label: "count", num: true }, { key: "reason", label: "reason" },
        { key: "modules", label: "declarations or modules", html: (r) => { const l = parse(r.decls).concat(parse(r.modules));
          return l.length > 3 ? `<details><summary>${l.length} listed</summary>${l.map(code).join("<br>")}</details>` : l.map(code).join("<br>"); },
          text: (r) => parse(r.decls).concat(parse(r.modules)).join(" ") }]);
      h += g4.html;
      var initEx = g4.init;
    }
    // 5. pending families
    h += `<h3>Logic families not yet in this repository</h3>`;
    const pend = has("logic_pending") ? await ctx.q("SELECT * FROM logic_pending ORDER BY name") : [];
    if (!pend.length) h += `<p class="muted">None listed in this database.</p>`;
    else {
      h += `<p class="muted">Lean developments of these families exist outside this repository and are being contributed in reviewed batches.
Until a family lands here, nothing in it is registered, and nothing here claims it.</p>`;
      h += await ui.table(pend, ["title", "nodes", "edges", "status"], { nowrap: ["nodes", "edges", "status"] });
    }
    return { html: h, init: () => { if (initOmitted) initOmitted(); if (initHets) initHets(); if (initCat) initCat(); if (initEx) initEx(); } };
  }

  // `#/logics` (the table) is the entry of the navigation; `#/logic-table` is the same view under its
  // earlier name, and `#/logic-graph/…` the graph (deep links to a selection keep working).
  Explorer.registerView({ id: "logics", title: "Logics", nav: 66, render: table });
  Explorer.registerView({ id: "logic-table", title: "Logic table", tab: "logics", render: table });
  Explorer.registerView({ id: "logic-graph", title: "Logic graph", tab: "logics", render: graphView });
  Explorer.registerView({ id: "logic-coverage", title: "Logic coverage", tab: "logics", render: coverage });
  Explorer.registerView({ id: "logic-consequence", title: "Consequence systems of the logics", tab: "logics", render: consequencePage });
  for (const k of [...NODES, ...EDGES]) {
    Explorer.registerView({ id: KIND[k].plural, title: KIND[k].title, tab: "logics", render: registry(k) });
    Explorer.registerView({ id: k, title: k, tab: "logics", render: detail(k) });
  }
})();
