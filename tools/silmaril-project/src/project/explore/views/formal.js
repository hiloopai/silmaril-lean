// Formal rows (docs/projects/formal-rows.md): each logic's interpretations, the roles of its
// theorems (soundness, consistency, nontriviality, satisfiability, inclusion), its concrete
// presentations and its concrete problems.
//   #/formal/                       the rows, as a table
//   #/formal-row/<name>             one logic: systems, interpretations, presentations, properties, problems
//   #/formal-property/<name>        one theorem with its role, its statement and its axioms
//   #/formal-problem/<name>         one concrete problem, in each presentation, with its checked claims
//   #/presentation/<name>           one S-expression presentation
//   #/derivation-system/<name>      one derivation system: judgments, proof formats, checked claims
//   #/derivation/<name>             one concrete proof: its formats, proof tree, indexed steps and verdicts
// Lean checked every role and claim from the theorems' types (Silmaril.Project.Registry.Formal):
// a name alone never stands for a property.
(() => {
  const ui = Explorer.ui;
  const has = (t) => Explorer.tables().has(t);
  const missing = `<p class="muted">This database has no formal-row tables (built by an older <code>sil project</code>).</p>`;
  const code = (s) => s == null || s === "" ? "" : `<code>${ui.esc(s)}</code>`;
  const link = (route, name, text) => name == null ? "" : `<a href="#/${route}/${encodeURIComponent(name)}">${ui.esc(text == null ? name : text)}</a>`;
  const srcOf = (decl) => decl ? `<a class="fr-src" href="#/source/${encodeURIComponent(decl)}" title="the Lean source of ${ui.esc(decl)}">source</a>` : "";
  const list = (v) => { try { const x = typeof v === "string" ? JSON.parse(v) : v; return Array.isArray(x) ? x : []; } catch (e) { return []; } };
  const obj = (v) => { try { const x = typeof v === "string" ? JSON.parse(v) : v; return x && typeof x === "object" && !Array.isArray(x) ? x : null; } catch (e) { return null; } };
  const STD = ["Classical.choice", "Quot.sound", "propext"];
  const axiomsText = (ax) => { const a = list(ax); const extra = a.filter((x) => !STD.includes(x));
    return extra.length ? `<span class="fr-warn">non-standard axioms: ${ui.esc(extra.join(", "))}</span>`
      : `<span class="muted" title="${ui.esc(a.join(", ") || "none")}">standard axioms only</span>`; };
  const ROLE = { soundness: "soundness", consistency: "consistency", nontriviality: "nontriviality",
    satisfiability: "satisfiability (a model)", inclusion: "inclusion" };
  const ROLE_DOC = {
    soundness: "System.SoundFor S I: every derived consequence holds in every model of the premises",
    consistency: "System.ConsistentWrt S ff Γ: the context does not derive the chosen falsity",
    nontriviality: "System.ContextConsistent S Γ: some conclusion is not derived",
    satisfiability: "Room.Satisfiable or Satisfaction.Satisfiable: the theory has a model",
    inclusion: "S ≤ T: every consequence of S is one of T" };

  function style() {
    if (document.getElementById("fr-style")) return;
    const s = document.createElement("style");
    s.id = "fr-style";
    s.textContent = ".fr-ok { color:#137333; font-weight:600; white-space:nowrap; } .fr-none { color:#80868b; } .fr-warn { color:#b3261e; } " +
      ".fr-sexp { background:#f6f8fa; border:1px solid #d0d7de; border-radius:4px; padding:8px; white-space:pre-wrap; word-break:break-word; font-size:13px; max-width:900px; } " +
      ".fr-src { font-size:12px; margin-left:6px; } .fr-claims dt { font-weight:600; } .fr-claims dd { margin:0 0 8px 16px; } " +
      "table.fr-rows td { vertical-align:top; } .fr-variant { max-width:420px; font-size:13px; } " +
      ".fr-bad { color:#b3261e; font-weight:600; white-space:nowrap; } .fr-tree, .fr-tree ul { list-style:none; padding-left:18px; margin:0; } " +
      ".fr-tree li { margin:2px 0; } .fr-tree .fr-rule { font-weight:600; color:#1a73e8; } .fr-tree code { font-size:12px; } " +
      "table.fr-steps tr.fr-hl td { background:#fff4ce; } table.fr-steps td { vertical-align:top; } " +
      "@media (max-width: 700px) { table.fr-rows th:nth-child(3), table.fr-rows td:nth-child(3) { display:none; } }";
    document.head.appendChild(s);
  }

  async function load(ctx) {
    const [rows, props, problems, pres, dsys, ders] = await Promise.all([
      ctx.q("SELECT * FROM logic_rows ORDER BY coalesce(row_order, 999), name LIMIT 500"),
      ctx.q("SELECT * FROM logic_properties ORDER BY name LIMIT 2000"),
      ctx.q("SELECT * FROM logic_problems ORDER BY name LIMIT 2000"),
      ctx.q("SELECT * FROM presentations ORDER BY name LIMIT 2000"),
      has("derivation_systems") ? ctx.q("SELECT * FROM derivation_systems ORDER BY name LIMIT 2000") : [],
      has("derivations") ? ctx.q("SELECT * FROM derivations ORDER BY name LIMIT 2000") : [],
    ]);
    return { rows, props, problems, pres, dsys, ders, prop: new Map(props.map((p) => [p.name, p])), problem: new Map(problems.map((p) => [p.name, p])),
      presentation: new Map(pres.map((p) => [p.name, p])), dsysMap: new Map(dsys.map((x) => [x.name, x])), der: new Map(ders.map((x) => [x.name, x])) };
  }

  // A small S-expression reader for Lean's printed proofs (atoms and lists; no strings).
  function readSExp(text) {
    const toks = text.match(/[()]|[^\s()]+/g) || [];
    let i = 0;
    const one = () => { const t = toks[i++]; if (t !== "(") return t; const xs = []; while (i < toks.length && toks[i] !== ")") xs.push(one()); i++; return xs; };
    return toks.length ? one() : null;
  }
  const showSExp = (e) => Array.isArray(e) ? `(${e.map(showSExp).join(" ")})` : String(e);
  // The tree format: (assume J) | (infer RULE J tree*)
  function treeHtml(e) {
    if (!Array.isArray(e)) return `<li><code>${ui.esc(showSExp(e))}</code></li>`;
    if (e[0] === "assume") return `<li><span class="fr-rule">assume</span> <code>${ui.esc(showSExp(e[1]))}</code></li>`;
    if (e[0] === "infer") {
      const subs = e.slice(3);
      return `<li><span class="fr-rule">${ui.esc(showSExp(e[1]))}</span> <code>${ui.esc(showSExp(e[2]))}</code>` +
        (subs.length ? `<ul>${subs.map(treeHtml).join("")}</ul>` : "") + `</li>`;
    }
    return `<li><code>${ui.esc(showSExp(e))}</code></li>`;
  }
  const shortName = (s) => String(s || "");
  const verdictBadge = (v) => v.accepted
    ? `<span class="fr-ok" title="${ui.esc(v.statement)}">✓ accepted by <code>${ui.esc(shortName(v.checker))}</code></span>`
    : `<span class="fr-bad" title="${ui.esc(v.statement)}">✗ rejected by <code>${ui.esc(shortName(v.checker))}</code>${v.stage ? ` at ${ui.esc(v.stage)}` : ""}</span>`;
  const derivationRow = (x) => `<tr><td>${link("derivation", x.name, x.title || x.name)}</td><td>${code(x.conclusion)}</td>` +
    `<td>${list(x.verdicts).map(verdictBadge).join("<br>")}</td><td class="num">${list(x.steps).length}</td></tr>`;
  const derivationTable = (xs, id) => `<div class="tablebox"><table class="lg-grid" id="${id}"><thead><tr><th>derivation</th><th>conclusion</th><th>verdicts (Lean-checked)</th><th>steps</th></tr></thead><tbody>` +
    xs.map(derivationRow).join("") + `</tbody></table></div>`;
  const claimRole = { locally_sound: "locally sound", agrees: "agrees with" };

  const status = (ps, role) => {
    const xs = ps.filter((p) => p.role === role);
    return xs.length ? `<span class="fr-ok" title="${ui.esc(xs.map((p) => p.statement).join("\n"))}">✓ proved (${xs.length})</span>`
      : `<span class="fr-none" title="no theorem with this role is registered">—</span>`;
  };

  async function table(arg, ctx) {
    style();
    if (!has("logic_rows")) return missing;
    const d = await load(ctx);
    const body = d.rows.map((r) => {
      const ps = list(r.properties).map((n) => d.prop.get(n)).filter(Boolean);
      const prs = list(r.presentations).map((n) => d.presentation.get(n)).filter(Boolean);
      const def = prs.find((p) => p.is_default) || prs[0];
      return `<tr><td>${link("formal-row", r.name, r.title)}</td>` +
        `<td>${def ? `${link("presentation", def.name, def.codec_name)} <span class="muted">v${ui.esc(def.codec_version)}</span>${prs.length > 1 ? ` <span class="muted">+${prs.length - 1}</span>` : ""}` : '<span class="fr-none">—</span>'}</td>` +
        `<td class="fr-variant">${ui.esc(r.variant || "")}</td>` +
        `<td>${status(ps, "soundness")}</td><td>${status(ps, "consistency")}</td>` +
        `<td>${(() => { const mn = ps.filter((p) => p.role === "satisfiability" || p.role === "nontriviality");
          return mn.length ? `<span class="fr-ok" title="${ui.esc(mn.map((p) => p.statement).join("\n"))}">✓ proved (${mn.length})</span>` : '<span class="fr-none">—</span>'; })()}</td>` +
        `<td>${status(ps, "inclusion")}</td>` +
        `<td class="num">${list(r.problems).length}</td>` +
        `<td>${(() => { const ds = list(r.derivations).map((n) => d.der.get(n)).filter(Boolean);
          if (!ds.length) return '<span class="fr-none">—</span>';
          const acc = ds.filter((x) => list(x.verdicts).some((v) => v.accepted)).length;
          return `<span class="fr-ok" title="checked proofs (accepted by some checker) / registered proofs">✓ ${acc}</span> <span class="muted">/ ${ds.length}</span>`; })()}</td></tr>`;
    }).join("");
    return `<h2>Formal rows: interpretation, soundness and consistency (${d.rows.length})</h2>
<p style="max-width:900px">Each row is a logic with its consequence systems, its interpretations in Lean, its S-expression presentations and its
concrete problems. A ✓ links a theorem whose <b>statement</b> Lean checked against its role (soundness is <code>System.SoundFor S I</code>,
consistency is <code>System.ConsistentWrt S ff Γ</code>, and so on) for the row's registered system; a name alone never counts.
Every result is relative to Lean's own consistency and to the stated models; none is claimed for arbitrary added axioms.
See <a href="https://github.com/hiloopai/silmaril-lean/blob/main/docs/projects/formal-rows.md">formal-rows.md</a> for the acceptance matrix.</p>
<div class="tablebox"><table class="lg-grid fr-rows" id="fr-rows"><thead><tr><th>logic</th><th>default presentation</th><th>variant and semantics</th>
<th>soundness</th><th>consistency</th><th>model / nontriviality</th><th>inclusions</th><th>problems</th><th>proofs</th></tr></thead><tbody>${body}</tbody></table></div>`;
  }

  function propertyRow(p) {
    return `<tr><td>${link("formal-property", p.name)}</td><td title="${ui.esc(ROLE_DOC[p.role] || "")}">${ui.esc(ROLE[p.role] || p.role)}</td>` +
      `<td>${p.system ? link("system", p.system) : ""}${p.target ? ` → ${link("system", p.target)}` : ""}</td>` +
      `<td>${code(p.statement)}</td><td>${axiomsText(p.axioms)}</td><td>${code(p.decl)}${p.arg ? ` <span class="muted">at ${ui.esc(p.arg)}</span>` : ""}${srcOf(p.decl)}</td></tr>`;
  }

  async function rowPage(name, ctx) {
    style();
    if (!has("logic_rows")) return missing;
    const d = await load(ctx);
    const r = d.rows.find((x) => x.name === name);
    if (!r) return `<p class="err">no formal row ${ui.esc(name)}</p>`;
    const ps = list(r.properties).map((n) => d.prop.get(n)).filter(Boolean);
    const prs = list(r.presentations).map((n) => d.presentation.get(n)).filter(Boolean);
    const pbs = list(r.problems).map((n) => d.problem.get(n)).filter(Boolean);
    let h = `<p><a href="#/formal/">← formal rows</a></p><h2>${ui.esc(r.title)}</h2>`;
    if (r.variant) h += `<p class="fr-variant" style="max-width:900px">${ui.esc(r.variant)}</p>`;
    h += `<dl>`;
    if (r.institution) h += `<dt>institution</dt><dd>${link("institution", r.institution)}</dd>`;
    h += `<dt>consequence systems</dt><dd>${list(r.systems).map((s) => link("system", s)).join("<br>") || "—"}</dd>`;
    h += `<dt>interpretations</dt><dd>${list(r.interpretations).map((i) => `${code(i)}${srcOf(i)}`).join("<br>") || "—"}</dd></dl>`;
    h += `<h3>Presentations</h3><div class="tablebox"><table class="lg-grid" id="fr-presentations"><thead><tr><th>presentation</th><th>codec</th><th>version</th><th>default</th><th>abstract syntax</th><th>Lean</th></tr></thead><tbody>` +
      prs.map((p) => `<tr><td>${link("presentation", p.name, p.title || p.name)}</td><td>${code(p.codec_name)}</td><td>${ui.esc(p.codec_version)}</td><td>${p.is_default ? "default" : ""}</td><td>${code(p.abstract_type)}</td><td>${code(p.decl)}${srcOf(p.decl)}</td></tr>`).join("") +
      `</tbody></table></div>`;
    h += `<h3>Properties</h3><p class="muted">Each statement was checked by Lean against its role.</p><div class="tablebox"><table class="lg-grid" id="fr-properties"><thead><tr><th>property</th><th>role</th><th>system</th><th>statement</th><th>axioms</th><th>theorem</th></tr></thead><tbody>` +
      ps.map(propertyRow).join("") + `</tbody></table></div>`;
    h += `<h3>Concrete problems</h3>` + (pbs.length ? `<div class="tablebox"><table class="lg-grid" id="fr-problems"><thead><tr><th>problem</th><th>S-expression (default presentation)</th><th>claims</th></tr></thead><tbody>` +
      pbs.map((p) => `<tr><td>${link("formal-problem", p.name, p.title || p.name)}</td><td><code>${ui.esc(p.sexp)}</code></td><td>${claimsShort(p)}</td></tr>`).join("") +
      `</tbody></table></div>` : `<p class="muted">None registered.</p>`);
    const dss = list(r.derivation_systems).map((n) => d.dsysMap.get(n)).filter(Boolean);
    const drs = list(r.derivations).map((n) => d.der.get(n)).filter(Boolean);
    if (dss.length) h += `<h3>Derivation systems</h3><div class="tablebox"><table class="lg-grid" id="fr-dsys"><thead><tr><th>derivation system</th><th>judgments</th><th>proof formats</th><th>claims (Lean-checked)</th></tr></thead><tbody>` +
      dss.map((x) => `<tr><td>${link("derivation-system", x.name, x.title || x.name)}</td><td>${x.judgments ? link("presentation", x.judgments) : code(x.judgment)}</td>` +
        `<td>${list(x.formats).map((f) => link("presentation", f, (d.presentation.get(f) || {}).codec_name || f)).join("<br>")}</td>` +
        `<td>${list(x.claims).map((c) => `<span class="fr-ok" title="${ui.esc(c.statement)}">✓ ${ui.esc(claimRole[c.role] || c.role)}</span>`).join(" ")}</td></tr>`).join("") +
      `</tbody></table></div>`;
    if (drs.length) h += `<h3>Derivations</h3>` + derivationTable(drs, "fr-derivations");
    return h;
  }

  async function derivationSystemPage(name, ctx) {
    style();
    if (!has("derivation_systems")) return missing;
    const d = await load(ctx);
    const x = d.dsysMap.get(name);
    if (!x) return `<p class="err">no derivation system ${ui.esc(name)}</p>`;
    const row = d.rows.find((r) => list(r.derivation_systems).includes(name));
    let h = `<p>${row ? link("formal-row", row.name, "← " + row.title) : ""}</p><h2>derivation system: ${ui.esc(x.title || x.name)}</h2>`;
    h += `<p class="muted" style="max-width:900px">Proofs are explicit objects (trees or indexed lines) whose every step is checked to be an instance of its rule
(<code>DerivationSystem.Instance</code>); raw rule names are elaborated by untrusted code and then checked.</p><dl>`;
    h += `<dt>system</dt><dd>${code(x.decl)}${x.arg ? ` <span class="muted">at ${ui.esc(x.arg)}</span>` : ""}${srcOf(x.decl)}</dd>`;
    h += `<dt>judgments</dt><dd>${code(x.judgment)}${x.judgments ? ` in ${link("presentation", x.judgments)}` : ""}</dd>`;
    h += `<dt>proof formats</dt><dd>${list(x.formats).map((f) => link("presentation", f, (d.presentation.get(f) || {}).codec_name || f)).join("<br>") || "—"}</dd></dl>`;
    h += `<h3>Claims</h3><dl class="fr-claims" id="fr-dsys-claims">`;
    for (const c of list(x.claims)) {
      h += `<dt>${ui.esc(claimRole[c.role] || c.role)}${c.role === "agrees" && x.system ? ` ${link("system", x.system)}` : ""}${c.interpretation ? ` <span class="muted">for ${ui.esc(c.interpretation)}</span>` : ""}</dt>` +
        `<dd>${code(c.statement)}<br>by ${code(c.proof)} · ${axiomsText(c.axioms)}</dd>`;
    }
    h += `</dl>`;
    const drs = d.ders.filter((y) => y.system === name);
    h += `<h3>Derivations</h3>` + (drs.length ? derivationTable(drs, "fr-dsys-derivations") : `<p class="muted">None registered.</p>`);
    return h;
  }

  async function derivationPage(arg, ctx) {
    style();
    if (!has("derivations")) return missing;
    const i = arg.indexOf("?"), name = decodeURIComponent(i < 0 ? arg : arg.slice(0, i));
    const sel = new URLSearchParams(i < 0 ? "" : arg.slice(i + 1)).get("presentation");
    const d = await load(ctx);
    const x = d.der.get(name);
    if (!x) return `<p class="err">no derivation ${ui.esc(name)}</p>`;
    const rend = obj(x.renderings) || {};
    const keys = Object.keys(rend);
    const cur = sel && rend[sel] != null ? sel : x.presentation;
    const row = d.rows.find((r) => list(r.derivations).includes(name));
    let h = `<p>${row ? link("formal-row", row.name, "← " + row.title) : ""}</p><h2>${ui.esc(x.title || x.name)}</h2>`;
    h += `<dl><dt>derivation system</dt><dd>${link("derivation-system", x.system, (d.dsysMap.get(x.system) || {}).title || x.system)}</dd>` +
      `<dt>conclusion</dt><dd>${code(x.conclusion)}</dd><dt>proof object</dt><dd>${code(x.decl)}${srcOf(x.decl)}</dd></dl>`;
    h += `<h3>Verdicts</h3><p class="muted">Each is a Lean theorem <code>check e = r</code> about an encoding of this proof, proved by the kernel.</p><ul id="fr-verdicts">` +
      list(x.verdicts).map((v) => `<li>${verdictBadge(v)} <span class="muted">on ${ui.esc((d.presentation.get(v.format) || {}).codec_name || v.format)}</span><br>${code(v.statement)} by ${code(v.proof)}${srcOf(v.proof)} · ${axiomsText(v.axioms)}</li>`).join("") + `</ul>`;
    const dv = obj(x.derives);
    if (dv) h += `<p><span class="fr-ok">✓ derives</span> ${x.derives_system ? link("system", x.derives_system) : ""}: ${code(dv.statement)} by ${code(dv.proof)}${srcOf(dv.proof)} · ${axiomsText(dv.axioms)}</p>`;
    h += `<h3>Proof tree</h3><ul class="fr-tree" id="fr-tree">${treeHtml(readSExp(rend[x.presentation] != null ? rend[x.presentation] : x.sexp))}</ul>`;
    const steps = list(x.steps);
    h += `<h3>Indexed steps</h3><p class="muted">The tree flattened into lines (<code>ProofTree.lines</code>); each step cites earlier lines.</p>` +
      `<div class="tablebox"><table class="lg-grid fr-steps" id="fr-steps"><thead><tr><th>#</th><th>rule</th><th>judgment</th><th>premises</th></tr></thead><tbody>` +
      steps.map((st) => `<tr id="fr-step-${st.index}" data-prem="${list(st.premises).join(",")}"><td class="num">${st.index}</td><td>${st.kind === "assume" ? "assume" : `<span class="fr-rule">${ui.esc(st.rule)}</span>`}</td>` +
        `<td><code>${ui.esc(st.judgment)}</code></td><td>${list(st.premises).map((k) => `<a href="#fr-step-${k}" data-step="${k}">${k}</a>`).join(", ")}</td></tr>`).join("") +
      `</tbody></table></div>`;
    h += `<h3>S-expression</h3><label>format <select id="fr-dpres">${(keys.length ? keys : [x.presentation]).map((k) => {
      const pr = d.presentation.get(k);
      return `<option value="${ui.esc(k)}"${k === cur ? " selected" : ""}>${ui.esc(pr ? `${pr.codec_name} v${pr.codec_version}` : k)}</option>`; }).join("")}</select></label>`;
    h += `<pre class="fr-sexp" id="fr-dsexp">${ui.esc(rend[cur] != null ? rend[cur] : x.sexp)}</pre>`;
    const init = () => {
      const s = document.getElementById("fr-dpres");
      if (s) s.addEventListener("change", () => {
        document.getElementById("fr-dsexp").textContent = rend[s.value] != null ? rend[s.value] : x.sexp;
        history.replaceState(null, "", `#/derivation/${encodeURIComponent(name)}?presentation=${encodeURIComponent(s.value)}`);
      });
      const tb = document.getElementById("fr-steps");
      if (tb) {
        tb.addEventListener("mouseover", (ev) => {
          const tr = ev.target.closest("tr[data-prem]");
          tb.querySelectorAll("tr.fr-hl").forEach((r) => r.classList.remove("fr-hl"));
          if (!tr) return;
          for (const k of tr.dataset.prem.split(",").filter(Boolean)) { const r = document.getElementById("fr-step-" + k); if (r) r.classList.add("fr-hl"); }
        });
        tb.addEventListener("click", (ev) => {
          const a = ev.target.closest("a[data-step]");
          if (!a) return;
          ev.preventDefault();
          const r = document.getElementById("fr-step-" + a.dataset.step);
          if (r) { r.scrollIntoView({ block: "center" }); r.classList.add("fr-hl"); }
        });
      }
    };
    return { html: h, init };
  }

  const claimsShort = (p) => [["derived", "derived"], ["entailed", "entailed"], ["truth", "true"]]
    .filter(([k]) => obj(p[k])).map(([, t]) => `<span class="fr-ok">✓ ${t}</span>`).join(" ");

  async function problemPage(arg, ctx) {
    style();
    if (!has("logic_problems")) return missing;
    const i = arg.indexOf("?"), name = decodeURIComponent(i < 0 ? arg : arg.slice(0, i));
    const sel = new URLSearchParams(i < 0 ? "" : arg.slice(i + 1)).get("presentation");
    const d = await load(ctx);
    const p = d.problem.get(name);
    if (!p) return `<p class="err">no concrete problem ${ui.esc(name)}</p>`;
    const rend = obj(p.renderings) || {};
    const keys = Object.keys(rend);
    const cur = sel && rend[sel] != null ? sel : p.presentation;
    const row = d.rows.find((r) => list(r.problems).includes(name));
    let h = `<p>${row ? link("formal-row", row.name, "← " + row.title) : ""}</p><h2>${ui.esc(p.title || p.name)}</h2>`;
    h += `<label>presentation <select id="fr-pres">${(keys.length ? keys : [p.presentation]).map((k) => {
      const pr = d.presentation.get(k);
      return `<option value="${ui.esc(k)}"${k === cur ? " selected" : ""}>${ui.esc(pr ? `${pr.codec_name} v${pr.codec_version}` : k)}</option>`; }).join("")}</select></label>`;
    h += `<pre class="fr-sexp" id="fr-sexp">${ui.esc(rend[cur] != null ? rend[cur] : p.sexp)}</pre>`;
    h += `<p class="muted">Computed by Lean by running the presentation's printer on the sentence; the decoder reads it back to exactly this sentence.</p>`;
    h += `<dl><dt>sentence</dt><dd>${code(p.sentence)} ${code(p.decl)}${srcOf(p.decl)}</dd></dl>`;
    h += `<h3>Claims</h3><dl class="fr-claims">`;
    for (const [k, title, by] of [["derived", "derived", p.system], ["entailed", "a semantic consequence", p.entailed_by], ["truth", "true in a model", p.interpretation]]) {
      const c = obj(p[k]);
      if (!c) continue;
      h += `<dt>${ui.esc(title)}${by ? ` — ${k === "truth" ? code(by) : link("system", by)}` : ""}</dt><dd>${code(c.statement)}<br>` +
        `by ${code(c.proof)}${srcOf(c.proof)}${c.context && c.context !== "[]" ? ` <span class="muted">from ${ui.esc(c.context)}</span>` : ""} · ${axiomsText(c.axioms)}</dd>`;
    }
    h += `</dl>`;
    const init = () => {
      const s = document.getElementById("fr-pres");
      if (s) s.addEventListener("change", () => {
        document.getElementById("fr-sexp").textContent = rend[s.value] != null ? rend[s.value] : p.sexp;
        history.replaceState(null, "", `#/formal-problem/${encodeURIComponent(name)}?presentation=${encodeURIComponent(s.value)}`);
      });
    };
    return { html: h, init };
  }

  async function propertyPage(name, ctx) {
    style();
    if (!has("logic_properties")) return missing;
    const d = await load(ctx);
    const p = d.prop.get(name);
    if (!p) return `<p class="err">no property ${ui.esc(name)}</p>`;
    const row = d.rows.find((r) => list(r.properties).includes(name));
    let h = `<p>${row ? link("formal-row", row.name, "← " + row.title) : ""}</p><h2>${ui.esc(ROLE[p.role] || p.role)}: <code>${ui.esc(p.name)}</code></h2>`;
    h += `<p class="muted">${ui.esc(ROLE_DOC[p.role] || "")}. Lean checked the statement below against this role.</p><dl>`;
    h += `<dt>statement</dt><dd>${code(p.statement)}</dd>`;
    h += `<dt>theorem</dt><dd>${code(p.decl)}${p.arg ? ` <span class="muted">at ${ui.esc(p.arg)}</span>` : ""}${srcOf(p.decl)}</dd>`;
    if (p.system) h += `<dt>system</dt><dd>${link("system", p.system)}</dd>`;
    if (p.target) h += `<dt>target</dt><dd>${link("system", p.target)}</dd>`;
    if (p.interpretation) h += `<dt>interpretation</dt><dd>${code(p.interpretation)}</dd>`;
    if (p.falsity) h += `<dt>falsity</dt><dd>${code(p.falsity)}</dd>`;
    if (p.context) h += `<dt>context</dt><dd>${code(p.context)}</dd>`;
    h += `<dt>axioms</dt><dd>${axiomsText(p.axioms)} ${code(list(p.axioms).join(", "))}</dd></dl>`;
    return h;
  }

  async function presentationPage(name, ctx) {
    style();
    if (!has("presentations")) return missing;
    const d = await load(ctx);
    const p = d.presentation.get(name);
    if (!p) return `<p class="err">no presentation ${ui.esc(name)}</p>`;
    const row = d.rows.find((r) => list(r.presentations).includes(name));
    const siblings = d.pres.filter((q) => q.abstract_type === p.abstract_type && q.name !== p.name);
    let h = `<p>${row ? link("formal-row", row.name, "← " + row.title) : ""}</p><h2>presentation <code>${ui.esc(p.codec_name)}</code> v${ui.esc(p.codec_version)}</h2>`;
    if (p.title) h += `<p><b>${ui.esc(p.title)}</b></p>`;
    h += `<dl><dt>abstract syntax</dt><dd>${code(p.abstract_type)}</dd><dt>codec</dt><dd>${code(p.decl)}${srcOf(p.decl)}</dd>` +
      `<dt>default</dt><dd>${p.is_default ? "the row's default presentation" : "an alternative presentation"}</dd>` +
      `<dt>other presentations of the same abstract syntax</dt><dd>${siblings.map((q) => link("presentation", q.name, `${q.codec_name} v${q.codec_version}`)).join("<br>") || "none"}</dd></dl>`;
    h += `<p class="muted" style="max-width:860px">A presentation is not the logic: the logic is its abstract syntax, and each presentation's decoder accepts
exactly its canonical forms (<code>SExpCodec.decode_eq_some_iff</code>).</p>`;
    const pbs = d.problems.filter((q) => obj(q.renderings) && obj(q.renderings)[name] != null);
    if (pbs.length) h += `<h3>Problems in this presentation</h3>` + pbs.map((q) => `<p>${link("formal-problem", q.name + "?presentation=" + name, q.title || q.name)}<br><code>${ui.esc(obj(q.renderings)[name])}</code></p>`).join("");
    return h;
  }

  Explorer.registerView({ id: "formal", title: "Formal", nav: 65, render: table });
  Explorer.registerView({ id: "formal-row", title: "Formal row", tab: "formal", render: rowPage });
  Explorer.registerView({ id: "formal-problem", title: "Concrete problem", tab: "formal", render: problemPage });
  Explorer.registerView({ id: "formal-property", title: "Property", tab: "formal", render: propertyPage });
  Explorer.registerView({ id: "presentation", title: "Presentation", tab: "formal", render: presentationPage });
  Explorer.registerView({ id: "derivation-system", title: "Derivation system", tab: "formal", render: derivationSystemPage });
  Explorer.registerView({ id: "derivation", title: "Derivation", tab: "formal", render: derivationPage });
})();
