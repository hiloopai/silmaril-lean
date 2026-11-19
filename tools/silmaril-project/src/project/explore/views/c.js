// ---------- C programs: the translation-validation corpus and the C TV theorems ----------
// Static files written by `c-pages` (tools/c-pages, `make pages`) next to the page:
//   c/theorems.json   the theorems of the checked C TV modules whose *statement* is a shape of
//                     Silmaril.Project.Shapes.CTV (listed by c-pages from their types, with axioms)
//   c/profiles.json   the coherence table of each target profile, with the theorems stating a row
//   c/programs/…      examples/c-programs: per program its representations and provenance.json
// The corpus's verdicts are compiled evidence (`ctv-pipeline`); no theorem is about a corpus
// program, and this view never attaches a theorem to one: a theorem is shown only under the
// statement c-pages read from its type.
(() => {
  const { esc, badge } = Explorer.ui;
  const cache = new Map();
  // Bounds: a fetched file at most FETCH_LIMIT bytes, a decompressed one at most INFLATE_LIMIT
  // (a gzip bomb stops with an error instead of exhausting memory).
  const FETCH_LIMIT = 8 << 20, INFLATE_LIMIT = 32 << 20;
  async function readBounded(stream, limit, what) {
    const rd = stream.getReader(), parts = [];
    let n = 0;
    for (;;) {
      const { done, value } = await rd.read();
      if (done) break;
      n += value.length;
      if (n > limit) { rd.cancel().catch(() => {}); throw new Error(`${what} exceeds the ${limit >> 20} MiB bound`); }
      parts.push(value);
    }
    const out = new Uint8Array(n);
    let o = 0;
    for (const p of parts) { out.set(p, o); o += p.length; }
    return out;
  }
  function cFetch(rel, how) {
    const key = how + ":" + rel;
    if (!cache.has(key)) cache.set(key, fetch("c/" + rel).then(async (r) => {
      if (!r.ok) throw new Error(`c/${rel}: HTTP ${r.status}`);
      let bytes = await readBounded(r.body, FETCH_LIMIT, `c/${rel}`);
      if (how === "json") return JSON.parse(new TextDecoder("utf-8").decode(bytes));
      if (rel.endsWith(".gz")) {
        bytes = await readBounded(new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip")), INFLATE_LIMIT,
          `c/${rel} (decompressed)`);
      }
      return bytes;
    }));
    return cache.get(key).catch((e) => { cache.delete(key); throw e; });
  }
  // The project database's record of a registered corpus file (silmaril/artifacts.toml, written by
  // scripts/c-tv/corpus.py --register): its SHA-256 and CID, or null.
  async function registered(ctx, name) {
    if (!ctx || !Explorer.tables().has("artifacts")) return null;
    const rows = await ctx.q("SELECT name, cid, sha256, size FROM artifacts WHERE name = ?", [name]);
    return rows[0] || null;
  }
  const HASH_NOTE = "a hash match detects corrupted or changed bytes only: it says nothing about who produced " +
    "them, and nothing about their semantic relation to the C source";
  const missing = (e) => `<p class="err">The C page data is not available here (${esc(e.message || e)}). ` +
    "It is written by <code>c-pages</code> (<code>make pages</code>) next to the page.</p>";
  const hex = (buf) => [...new Uint8Array(buf)].map((b) => b.toString(16).padStart(2, "0")).join("");
  const sha256 = async (bytes) => hex(await crypto.subtle.digest("SHA-256", bytes));
  const enc = encodeURIComponent;
  const plink = (name) => `<a href="#/c-program/${enc(name)}">${esc(name)}</a>`;
  const short = (s) => s ? `<code title="${esc(s)}">${esc(s.slice(0, 12))}</code>` : "";
  // Trust tags: what an edge or a verdict rests on (Silmaril.Cerberus.TV.Provenance.Evidence).
  const TAG = {
    kernel: ["ok", "kernel", "a kernel-checked theorem whose statement is this claim"],
    compiled: ["warn", "compiled", "computed by compiled Lean code (ctv-pipeline, cerb-lean, cfront); backed by the soundness theorems only up to the Lean compiler and runtime"],
    external: ["muted", "external", "output of an external tool taken as given (gcc -E, clang): not checked"],
    oracle: ["muted", "oracle", "agreement with another implementation on this input: testing"],
    missing: ["err", "missing", "no evidence: this edge is a gap of the pipeline"],
    ubonly: ["err", "only through source UB", "validated, but the source reaches undefined behaviour, which admits every observation: not a validation of defined behaviour"],
    sanity: ["muted", "sanity run", "one run of one native build, checked against the Core's allowed observations (Spec.check): not compiler correctness"],
  };
  const tag = (k) => { const t = TAG[k] || ["muted", k, ""]; return `<span class="ctag ctag-${t[0]}" data-tag="${esc(t[1])}" title="${esc(t[2])}">${esc(t[1])}</span>`; };
  const evidenceKind = (ev) => typeof ev === "string" ? ev : Object.keys(ev || { missing: 1 })[0];
  const repoLink = (path, line, text) => {
    const f = typeof repoFile === "function" ? repoFile(path) : null;
    return f ? `<a href="${esc(f.blob)}${line ? "#L" + line : ""}" target="_blank" rel="noopener noreferrer" class="srclink">${esc(text || path)}</a>` : `<code>${esc(text || path)}</code>`;
  };
  const moduleFile = (m) => m.startsWith("tests.") ? m.replace(/\./g, "/") + ".lean" : m.replace(/\./g, "/") + ".lean";
  const shapeShort = (s) => s.replace(/^silmaril\.shapes\.c\.tv\./, "");
  const routeCell = (rep, prov, route) => {
    const r = rep && rep.routes[route];
    if (r && r.status === "elaborated") {
      const e = r.explore, o = (e.sample[0] || {}).outcome || {};
      return `Core: ${esc(o.kind || "?")}${o.exit != null ? " " + esc(o.exit) : ""}${e.limited ? " (bounded)" : ""}`;
    }
    if (r) return `<span class="err">elaborator rejects</span>`;
    if (prov.failures[`${route}.tail`]) return `<span class="err">frontend rejects</span>`;
    if (route === "clang" && prov.failures["clang-ast"]) return `<span class="err">clang rejects</span>`;
    return "—";
  };

  if (!document.getElementById("c-style")) {
    const st = document.createElement("style");
    st.id = "c-style";
    st.textContent = ".cstage{border:1px solid var(--line);border-radius:6px;padding:8px 12px;margin:8px 0;background:var(--panel)}" +
      ".cstage h3{margin:0 0 4px 0;font-size:1em}.cstage pre{max-height:420px;overflow:auto;white-space:pre-wrap;word-break:break-all;font-size:12px}" +
      ".cnote{border-left:3px solid #e8963a;padding:4px 10px;margin:8px 0}" +
      ".ctag{display:inline-block;font-size:11px;line-height:1.4;padding:0 6px;border-radius:9px;border:1px solid;white-space:nowrap}" +
      ".ctag-ok{color:#1d6b35;border-color:#2e9d4f;background:#e9f6ed}.ctag-warn{color:#8a4d00;border-color:#e8963a;background:#fdf1e3}" +
      ".ctag-muted{color:#555;border-color:#aaa;background:#f3f3f3}.ctag-err{color:#a12020;border-color:#d64545;background:#fbeaea}";
    document.head.appendChild(st);
  }

  async function index() {
    let idx, thms, profs;
    try { [idx, thms, profs] = await Promise.all([cFetch("programs/index.json", "json"), cFetch("theorems.json", "json"), cFetch("profiles.json", "json")]); }
    catch (e) { return missing(e); }
    let h = '<h2>C programs</h2><p><a href="#/c-torture" id="ctorturelink">GCC torture suite: the pinned manifest and one status per case (not coverage)</a></p>';
    h += `<p class="cnote">Translation validation of C programs over the Lean port of Cerberus's Core semantics (${repoLink("docs/projects/c-tv.md", null, "docs/projects/c-tv.md")}). ` +
      "Each stage below is a separate representation with its own producer, and each edge has its own evidence. " +
      `${tag("compiled")} verdicts were computed by compiled Lean code; only ${tag("kernel")} rows are kernel-checked theorems. ` +
      "This corpus is not GCC torture coverage.</p>";
    const progs = await Promise.all(idx.programs.map(async (p) => {
      const prov = await cFetch(`programs/${p.name}/provenance.json`, "json");
      let rep = null;
      try { rep = await cFetch(`programs/${p.name}/report.json`, "json"); } catch (e) { rep = null; }
      return { p, prov, rep };
    }));
    // One status per program (disjoint), and how many programs have each.
    const counts = new Map();
    for (const { p } of progs) counts.set(p.status, (counts.get(p.status) || 0) + 1);
    h += `<h3>Corpus (${progs.length} programs)</h3><p class="muted" id="cstatuses">One status per program, counts summing to ${progs.length}: ` +
      [...counts].map(([k, n]) => `<code>${esc(k)}</code> ${n}`).join(", ") +
      `. A route agreement is compiled evidence: not a kernel proof, and not evidence that either frontend implements C.</p>`;
    h += `<table id="cprograms"><thead><tr><th>program</th><th>status</th><th>Cerberus route</th><th>Clang route</th>` +
      "<th>route agreement</th><th>native runs (sanity)</th><th>dropped / warnings</th><th>evidence</th></tr></thead><tbody>";
    for (const { p, prov, rep } of progs) {
      const v = Object.entries(p.verdicts || {});
      const cross = v.length ? v.map(([k, x]) => `${esc(k)}: <b>${esc(x)}</b>`).join("<br>") : "—";
      const obs = rep && rep.observations.length ? rep.observations.map((o) => `${esc(o.name)} ${esc(o.termination)}: ` +
        (Object.keys(o.check).length ? Object.entries(o.check).map(([k, x]) => `${esc(k)} ${esc(x)}`).join(", ") : "no Core")).join("<br>") : "—";
      const drops = prov.losses.map((l) => l.blocking
          ? `<span class="err closs-blocking"><b>${esc(l.route)} drops ${esc(l.construct)}: blocking</b></span>`
          : `<span class="muted closs-neutral">${esc(l.route)} drops ${esc(l.construct)} (not blocking)</span>`).concat(
        prov.warnings.map((w) => `<span class="err" title="${esc(w)}">producer self-report differs from the clang that ran</span>`)).join("<br>");
      const blocked = new Set(prov.blockedRoutes || []);
      const rc = (r) => routeCell(rep, prov, r) + (blocked.has(r) ? ' <span class="err cblocked"><b>source correspondence blocked</b></span>' : "");
      h += `<tr data-program="${esc(p.name)}" data-status="${esc(p.status)}"><td>${plink(p.name)}</td><td><code>${esc(p.status)}</code></td><td>${rc("cerberus")}</td><td>${rc("clang")}</td>` +
        `<td>${cross}</td><td>${obs}</td><td>${drops}</td><td>${v.length ? tag("compiled") + (v.some(([, x]) => /source UB/.test(x)) ? " " + tag("ubonly") : "") : tag("missing")}</td></tr>`;
    }
    h += "</tbody></table>";
    h += `<h3>Kernel-checked theorems (${thms.theorems.length})</h3><p class="muted">Every theorem of ${thms.modules.map((m) => repoLink(moduleFile(m), null, m)).join(" and ")} whose statement is a C TV shape, ` +
      "read by <code>c-pages</code> from the theorem's type. The programs here are constructed Core files (the elaborated " +
      "<code>return a + b;</code> family of <code>Silmaril.Project.CTV.Examples</code>), not corpus programs.</p>";
    h += '<table id="cthms"><thead><tr><th>theorem</th><th>registered row</th><th>shape</th><th>arguments</th><th>axioms</th><th>evidence</th></tr></thead><tbody>';
    for (const t of thms.theorems) {
      h += `<tr data-theorem="${esc(t.name)}"><td>${repoLink(moduleFile(t.module), t.line, t.name.split(".").pop())}</td>` +
        `<td>${t.row ? `<a href="#/problem/${enc(t.row)}"><code>${esc(t.row.replace(/^silmaril\.c_tv\./, ""))}</code></a>` : '<span class="muted">—</span>'}</td>` +
        `<td>${t.negated ? "¬ " : ""}<code>${esc(shapeShort(t.shape))}</code></td><td>${t.args.map((a) => `<code>${esc(a.replace(/^Silmaril\.(Project\.(Shapes\.)?CTV(\.Examples)?|Cerberus\.(TV|Spec))\./, ""))}</code>`).join(" ")}</td>` +
        `<td class="muted">${esc(t.axioms.join(", "))}</td><td>${tag("kernel")}</td></tr>`;
    }
    h += "</tbody></table>";
    for (const pr of profs) {
      h += `<h3>Profile <code>${esc(pr.decl)}</code></h3><p class="muted">${esc(pr.name)}. Coherence of the Core semantics with the profile per scalar type ` +
        "(<code>Profile.issues</code>); necessary, not sufficient for a result to transfer to the target.</p>";
      h += `<table class="cprofile" data-profile="${esc(pr.decl)}"><thead><tr><th>type</th><th>coherent</th><th>issues</th><th>theorem</th></tr></thead><tbody>`;
      for (const r of pr.scalars) {
        h += `<tr data-scalar="${esc(r.scalar)}"><td><code>${esc(r.scalar)}</code></td><td>${r.coherent ? "yes" : '<span class="err">no</span>'}</td>` +
          `<td>${r.issues.map((i) => esc(`${i.kind}: ${i.what}`)).join("<br>")}</td>` +
          `<td>${r.theorems.length ? r.theorems.map((t) => `${tag("kernel")} <code>${esc((t.negated ? "¬ " : "") + t.name.split(".").pop())}</code>`).join("<br>") : tag("compiled")}</td></tr>`;
      }
      h += "</tbody></table>";
    }
    return h;
  }

  const STAGES = [
    ["source", "Source", "source.c"],
    ["preprocessed", "Preprocessed (gcc -E)", "preprocessed.i"],
    ["clangAst", "Clang AST (JSON)", "clang-ast.json.gz"],
    ["typedAil", "Typed Ail, Cerberus route", "cerberus.tail.sexp"],
    ["typedAil", "Typed Ail, Clang route", "clang.tail.sexp"],
    ["core", "Core, Cerberus route", "cerberus.core.sexp.gz"],
    ["core", "Core, Clang route", "clang.core.sexp.gz"],
  ];
  const VIEW_LIMIT = 200000;

  async function program(name, ctx) {
    let prov, rep = null, thms, provBytes;
    try { [prov, thms, provBytes] = await Promise.all([cFetch(`programs/${name}/provenance.json`, "json"), cFetch("theorems.json", "json"),
      cFetch(`programs/${name}/provenance.json`, "bytes")]); }
    catch (e) { return missing(e); }
    try { rep = await cFetch(`programs/${name}/report.json`, "json"); } catch (e) { rep = null; }
    // Two stages may have the same bytes (gcc -E of a file without directives is the file): an
    // artifact is looked up by SHA-256 only for an edge's source, first artifact first, and an
    // input (no producer) has no incoming edge.
    const bySha = new Map();
    for (const a of Object.values(prov.artifacts)) if (!bySha.has(a.sha256)) bySha.set(a.sha256, a);
    // The edge that produced each artifact (refinement edges between Cores are the Validation section's).
    const into = new Map(prov.edges.filter((e) => e.relation === "produces" || e.relation === "elaborates").map((e) => [e.target, e]));
    let h = `<h2>C program <code>${esc(name)}</code></h2>`;
    h += `<p class="muted">${esc(prov.language)}, target <code>${esc(prov.target)}</code>, profile <code>${esc(prov.profile)}</code>; ` +
      `source ${repoLink(`examples/c-programs/${name}/source.c`)}; produced at <code>${esc(prov.repositoryRevision)}</code> by ` +
      `${esc(prov.tools.gcc)}, ${esc(prov.tools.clang)}.</p>`;
    // A theorem is about a corpus program only if c-pages read that program from its statement (`program`);
    // no current statement names one, and a theorem is never matched by its name.
    // The project database's record of this program's source and provenance (registered artifacts).
    const [regSrc, regProv] = await Promise.all([registered(ctx, `silmaril.c_tv.corpus.${name}.source`),
      registered(ctx, `silmaril.c_tv.corpus.${name}.provenance`)]);
    const provSum = await sha256(provBytes);
    const srcRec = prov.artifacts["source.c"];
    const dbRow = (label, reg, ok) => !reg ? `<li class="err" data-db="${label}" data-ok="false">${esc(label)}: not registered in the project database</li>`
      : `<li class="${ok ? "" : "err"}" data-db="${label}" data-ok="${ok}">${esc(label)}: registered as <code>${esc(reg.name)}</code> (CID <code>${esc(String(reg.cid).slice(0, 16))}…</code>); ` +
        (ok ? "the served bytes' SHA-256 equals the database's" : "<b>the served bytes' SHA-256 differs from the database's</b>") + "</li>";
    h += `<ul id="cdb">${dbRow("provenance.json", regProv, regProv && regProv.sha256 === provSum)}` +
      `${dbRow("source.c", regSrc, regSrc && srcRec && regSrc.sha256 === srcRec.sha256)}</ul>` +
      `<p class="muted">${esc(HASH_NOTE)}.</p>`;
    const kernel = thms.theorems.filter((t) => t.program === name);
    h += `<p class="cnote" id="ckernel">Kernel-checked theorems about this program: <b>${kernel.length}</b>. ` +
      (kernel.length ? "" : "No theorem's statement is about this program's Core; its verdicts below are compiled evidence.") + "</p>";
    for (const l of prov.losses) h += l.blocking
      ? `<p class="err closs" data-blocking="true"><b>Blocking: the ${esc(l.route)} route dropped ${esc(l.construct)}</b> (${esc(l.rule)}). ${esc(l.why || "")}. ` +
        `That route's typed Ail, Core and verdicts do not correspond to this source, whatever their evidence says.</p>`
      : `<p class="muted closs" data-blocking="false">Not blocking: the ${esc(l.route)} route dropped ${esc(l.construct)} (${esc(l.rule)}). ${esc(l.why || "")}.</p>`;
    for (const w of prov.warnings) h += `<p class="err cwarn">Warning: ${esc(w)}</p>`;
    h += "<h3>Stages</h3>";
    for (const [stage, title, file] of STAGES) {
      const a = prov.artifacts[file];
      const route = file.split(".")[0];
      const key = { "cerberus.tail.sexp": "cerberus.tail", "clang.tail.sexp": "clang.tail", "clang-ast.json.gz": "clang-ast", "preprocessed.i": "preprocessed" }[file];
      if (!a) {
        const f = key && prov.failures[key];
        const rr = rep && rep.routes[route];
        const why = f ? (typeof f === "string" ? f : f.output) : rr && rr.status !== "elaborated" ? `${rr.stage || rr.status}: ${rr.why}` : "not produced";
        h += `<div class="cstage" data-stage="${esc(file)}" data-present="no"><h3>${esc(title)} ${tag("missing")}</h3><pre class="err">${esc(why)}</pre></div>`;
        continue;
      }
      const e = a.producer ? into.get(a.sha256) : null;
      const src = e ? bySha.get(e.source) : null;
      h += `<div class="cstage" data-stage="${esc(file)}" data-present="yes"><h3>${esc(title)} ${e ? tag(evidenceKind(e.evidence)) : ""}</h3>` +
        `<p class="muted">${esc(file)}: ${a.bytes} bytes, SHA-256${a.sha256Of ? " (" + esc(a.sha256Of) + ")" : ""} ${short(a.sha256)}` +
        (a.producer ? `; produced by <code>${esc(a.producer.tool)}</code> ${esc(a.producer.version)}` : "; input") +
        (e ? `; ${esc(e.relation)} from <code>${esc(src ? src.file : e.source.slice(0, 12))}</code> (${esc(JSON.stringify(e.evidence))})` : "") + "</p>" +
        (e && e.sourceCorrespondence ? `<p class="err cblocked"><b>Source correspondence ${esc(e.sourceCorrespondence)}</b></p>` : "") +
        `<button type="button" class="cview" data-file="${esc(file)}" data-sha="${esc(a.sha256)}">view</button> <span class="csha muted"></span><pre class="cbody" hidden></pre></div>`;
    }
    h += "<h3>Validation</h3>";
    if (!rep) h += `<p>${tag("missing")} No route elaborated; nothing was explored or validated.</p>`;
    else {
      h += '<table id="cexplore"><thead><tr><th>route</th><th>status</th><th>endings</th><th>exhaustive</th><th>gap / stuck / UB</th><th>transitions</th><th>x86-64 per-type check (necessary filter)</th></tr></thead><tbody>';
      for (const [r, v] of Object.entries(rep.routes)) {
        if (v.status !== "elaborated") { h += `<tr><td>${esc(r)}</td><td class="err">${esc(v.status)}</td><td colspan="4">${esc(v.why || "")}</td></tr>`; continue; }
        const x = v.explore;
        // Endings are collected per run, with repetitions (one per interleaving): shown grouped.
        const groups = new Map();
        for (const s of x.sample) { const k = `${s.outcome.kind}${s.outcome.exit != null ? " " + s.outcome.exit : ""}${s.stdout ? " stdout " + JSON.stringify(s.stdout) : ""}`; groups.set(k, (groups.get(k) || 0) + 1); }
        const shown = [...groups].map(([k, n]) => esc(k) + (n > 1 ? ` <span class="muted">×${n}</span>` : "")).join("<br>");
        h += `<tr><td>${esc(r)}</td><td>elaborated</td><td>${shown}<br><span class="muted">${x.endings} endings${x.endings > x.sample.length ? `, first ${x.sample.length} shown` : ""}</span></td>` +
          `<td>${x.limited ? '<span class="err">no (bounded)</span>' : "yes"}</td><td>${x.gap ? "gap " : ""}${x.stuck ? "stuck " : ""}${x.ub ? "UB" : ""}${!x.gap && !x.stuck && !x.ub ? "none" : ""}</td><td>${x.steps}</td>` +
          `<td class="capplies" data-applies="${v.applicability ? v.applicability.applies : ""}">${v.applicability ? (v.applicability.applies ? "passes" : '<span class="err">fails</span>') +
            ` <span class="muted">(reachable Core names ${esc(v.applicability.mentions.join(", ") || "nothing")})</span>` +
            v.applicability.blockers.map((b) => `<br><span class="err">${esc(b.type)}: ${esc(b.issues.join("; "))}</span>`).join("") : "—"}</td></tr>`;
      }
      h += "</tbody></table>";
      h += '<p class="muted">A pair of routes is a <b>frontend agreement</b>: the Core of one frontend refines the other\'s (Core to Core). It says nothing about a compiler\'s output (the compiler-origin relation is <code>c.compiles_to</code>).</p>';
      h += '<table id="cpairs"><thead><tr><th>source</th><th>target</th><th>relation</th><th>verdict</th><th>source UB-free (validateUBFree)</th><th>covered only by source UB</th><th>evidence</th></tr></thead><tbody>';
      for (const p of rep.pairs) h += `<tr data-ubfree="${p.validatedUBFree}"><td>${esc(p.source)}</td><td>${esc(p.target)}</td><td>${esc(p.relation || "")}</td><td><b>${esc(p.verdict)}</b></td>` +
        `<td>${p.validatedUBFree ? "yes" : '<span class="err">no</span>'}</td><td>${p.coveredOnlyByUB ? '<span class="err">yes</span>' : "no"}</td>` +
        `<td>${p.verdict === "validated" || p.verdict === "refuted" ? tag("compiled") + (p.verdict === "validated" && !p.validatedUBFree ? " " + tag("ubonly") : "") : tag("missing")}</td></tr>`;
      if (!rep.pairs.length) h += `<tr><td colspan="5">${tag("missing")} fewer than two routes elaborated: no cross-validation</td></tr>`;
      h += "</tbody></table>";
      h += '<table id="cobs"><thead><tr><th>native run</th><th>termination</th><th>allowed by the Core (Spec.check)</th><th>evidence</th></tr></thead><tbody>';
      for (const o of rep.observations) h += `<tr><td>${esc(o.name)}</td><td>${esc(o.termination)}, ${o.stdoutBytes} stdout bytes</td>` +
        `<td>${Object.entries(o.check).map(([k, x]) => `${esc(k)}: ${esc(x)}`).join(", ") || "no Core"}</td><td>${tag("sanity")}</td></tr>`;
      h += "</tbody></table>";
      h += `<p class="muted">Profile ${esc(rep.profile)}; elaborator ${esc(rep.elaborator)}; bounds depth ${rep.bounds.depth}, budget ${rep.bounds.budget}; runtime maps ${repoLink(rep.runtime)}.</p>`;
    }
    const init = async () => {
      for (const b of document.querySelectorAll("button.cview")) b.addEventListener("click", async () => {
        const box = b.parentElement, pre = box.querySelector("pre.cbody"), out = box.querySelector(".csha");
        try {
          const bytes = await cFetch(`programs/${name}/${b.dataset.file}`, "bytes");
          const sum = await sha256(bytes);
          out.textContent = sum === b.dataset.sha
            ? `SHA-256 matches provenance.json (${HASH_NOTE})`
            : `SHA-256 MISMATCH with provenance.json: these bytes are not the recorded ones (${sum})`;
          out.className = "csha " + (sum === b.dataset.sha ? "muted" : "err");
          out.dataset.match = String(sum === b.dataset.sha);
          let text = new TextDecoder("utf-8").decode(bytes.subarray(0, VIEW_LIMIT));
          if (b.dataset.file.endsWith(".json.gz") && bytes.length <= VIEW_LIMIT) { try { text = JSON.stringify(JSON.parse(text), null, 1); } catch (e) { /* keep the text */ } }
          pre.textContent = text + (bytes.length > VIEW_LIMIT ? `\n… (${bytes.length - VIEW_LIMIT} more bytes not shown)` : "");
          pre.hidden = false;
        } catch (e) { out.textContent = String(e.message || e); out.className = "csha err"; }
      });
    };
    return { html: h, init };
  }

  // The GCC torture report: one status per case of the pinned manifest, never presented as coverage.
  async function torture() {
    let rep;
    try {
      const bytes = await cFetch("torture/tv-report.json.gz", "bytes");
      rep = JSON.parse(new TextDecoder("utf-8").decode(bytes));
    } catch (e) { return missing(e); }
    const rows = rep.cases, n = rep.denominator;
    const statuses = [...new Set(rows.map((r) => r.status))];
    const count = (f) => rows.filter(f).length;
    let h = "<h2>GCC C torture suite</h2>";
    h += `<p class="cnote" id="tnotcoverage"><b>Not coverage.</b> No torture test is translation-validated here. ` +
      `The ${count((r) => r.status === "cross-validated")} <code>cross-validated</code> cases are trivial frontend agreements (Core to Core, compiled evidence): ` +
      "see the highlights below. Validating a torture test needs, beyond these, a precise per-type check and the compiler-origin relation " +
      `(${repoLink("benchmarks/gcc-torture/README.md", null, "the gap roadmap")}, ${repoLink("docs/projects/c-tv.md", null, "c-tv.md")}).</p>`;
    h += `<p class="muted">Manifest: GCC <code>${esc(rep.manifest.revision.slice(0, 12))}</code>, SHA-256 <code>${esc(rep.manifest.sha256.slice(0, 12))}…</code>; ` +
      `every attempted case's source was checked against it during the run (${count((r) => r.sourceVerified)} verified). ` +
      `Tools: ${esc(rep.tools.gcc)}, ${esc(rep.tools.clang)}; profile <code>${esc(rep.options.pipeline.profile)}</code>; ` +
      `native runs capped at ${rep.native.timeoutSeconds} s, ${rep.native.addressSpaceBytes >> 20} MiB, ${rep.native.stdoutBytes >> 20} MiB of stdout.</p>`;
    h += `<table id="tstatus"><thead><tr><th>status</th><th>compile/</th><th>execute/</th><th>total</th></tr></thead><tbody>`;
    for (const st of statuses) h += `<tr data-status="${esc(st)}"><td><code>${esc(st)}</code></td><td>${count((r) => r.status === st && r.case.startsWith("compile/"))}</td>` +
      `<td>${count((r) => r.status === st && r.case.startsWith("execute/"))}</td><td>${count((r) => r.status === st)}</td></tr>`;
    h += `<tr><td><b>denominator</b></td><td>${count((r) => r.case.startsWith("compile/"))}</td><td>${count((r) => r.case.startsWith("execute/"))}</td><td><b>${n}</b></td></tr></tbody></table>`;
    const xv = rows.filter((r) => r.status.startsWith("cross-validated"));
    h += `<h3>Highlights: the cross-validated cases</h3><table id="thighlights"><thead><tr><th>case</th><th>status</th><th>why it is not coverage</th></tr></thead><tbody>`;
    for (const r of xv) {
      const why = [];
      if (r.compileOnly) why.push("<b>compile-only test</b>: it is about compiling, its evidence must be function-level (no function-level edge exists for it yet); its whole-program behaviour is incidental");
      if (r.targetConditional) why.push("<b>architecture-gated</b>: <code>#if</code> on a target macro selects the test; on x86-64 it preprocesses to a trivial <code>main</code> returning 0");
      why.push("frontend agreement only (Core to Core, compiled); no per-type check passes and no compiler-origin edge");
      h += `<tr data-case="${esc(r.case)}" data-compile-only="${!!r.compileOnly}" data-target-conditional="${!!r.targetConditional}"><td><code>${esc(r.case)}</code></td>` +
        `<td><code>${esc(r.status)}</code></td><td>${why.join("<br>")}</td></tr>`;
    }
    h += "</tbody></table>";
    h += `<p class="muted">Compile-only cases elaborated without <code>main</code>: ${count((r) => r.status === "no-main")} (<code>no-main</code>; the function-level gap: their evidence would be per function). ` +
      `Cases with a route that dropped a construct: ${count((r) => r.blocked)}. Native runs that hit a cap: ${count((r) => r.native && ["timeout", "stdout-limit"].includes(r.native.ended))}.</p>`;
    return h;
  }

  Explorer.registerView({ id: "c", title: "C programs", nav: 87, render: index });
  Explorer.registerView({ id: "c-torture", title: "GCC torture", tab: "c", render: () => torture() });
  Explorer.registerView({ id: "c-program", title: "C program", tab: "c", render: (arg, ctx) => program(arg, ctx) });
})();
