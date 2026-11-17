// The Headers tab: C headers by two routes. The subset reader's route: the header as
// `Header.read` reads it, each prototype as every versioned ABI definition lowers it (or refuses
// it, with the reason), the System V scalar call plan, and each aggregate's layout under two data
// models. The clang route: a pinned clang import's provenance, counts and entries (from the
// generated literal `Pinned.<Name>.entries`), each entry's status for every ABI definition
// (claimable, unsupported or internal, with the reason) and, for a claimable prototype, its
// lowering and call plan. Data: headers/index.json (`header-pages`, silmaril.header-pages/2).
// Every value is computed by the definitions the conformance rows and layout theorems use. A
// layout column names a theorem only when the data carries its `proof` (header-pages checked the
// theorem's statement exactly against the table and its axioms); every other column says
// "computed, not a theorem". Every string of the data goes through `esc`.
(() => {
  const DATA = "headers/index.json", SCHEMA = "silmaril.header-pages/2";
  const enc = encodeURIComponent;
  let cached = null;
  async function load() {
    if (!cached) cached = fetch(DATA).then((r) => { if (!r.ok) throw new Error(`${DATA}: HTTP ${r.status}`); return r.json(); })
      .then((d) => { if (d.schema !== SCHEMA) throw new Error(`${DATA}: schema ${d.schema}, expected ${SCHEMA}`); return d; })
      .catch((e) => { cached = null; throw e; });
    return cached;
  }
  if (typeof document !== "undefined" && document.getElementById && !document.getElementById("hdr-style")) {
    const st = document.createElement("style");
    st.id = "hdr-style";
    st.textContent = `.hdr-refused{color:#a33}.hdr-ok{color:#174}.hdr-internal{color:#777}.hdr-plan{font-size:90%;color:#555}
      table.hdr td,table.hdr th{padding:2px 8px;vertical-align:top;border-bottom:1px solid #eee}
      table.hdr-prov th{text-align:left;font-weight:normal;color:#555}
      .hdr-note{background:#fff8e6;border-left:3px solid #d90;padding:6px 10px;max-width:70em}`;
    document.head.appendChild(st);
  }
  const lowerCell = (l) => !l ? '<span class="muted">—</span>'
    : l.refused != null ? `<span class="hdr-refused" title="the ABI definition's lowering refuses this prototype">refused: ${esc(l.refused)}</span>`
    : `<span class="hdr-ok">${esc(l.ok)}</span>` + (l.plan ? (l.plan.ok ? `<div class="hdr-plan">args: ${esc(l.plan.ok.arguments.join(" · ") || "none")}<br>result: ${esc(l.plan.ok.result)}<br><span class="muted" data-stack>outgoing stack: ${esc(l.plan.ok.stackSize)} B${l.planNote ? " · " + esc(l.planNote) : ""}</span></div>`
      : `<div class="hdr-plan hdr-refused">plan refused: ${esc(l.plan.refused)}</div>`) : "");

  // A layout column's theorem: its name, linked to its source line when the page knows the
  // sources (`repoFile`, provenance.js), and its padding theorem; or "computed, not a theorem".
  const thmRef = (t, what) => {
    const f = typeof repoFile === "function" && typeof t.file === "string" ? repoFile(t.file) : null;
    const name = `<code>${esc(t.decl)}</code>`;
    return f ? `<a data-thm="${esc(what)}" data-decl="${esc(t.decl)}" href="${esc(f.blob)}${Number.isInteger(t.line) ? "#L" + t.line : ""}" target="_blank" rel="noopener noreferrer" title="${esc(f.path)}${Number.isInteger(t.line) ? ":" + esc(t.line) : ""}">${name}</a>`
      : `<span data-thm-name="${esc(what)}" data-decl="${esc(t.decl)}">${name}</span>`;
  };
  const isThm = (t) => !!t && typeof t.decl === "string" && t.status === "proved";
  function proofCell(L) {
    if (!L) return "";
    const p = L.proof;
    if (!isThm(p) || !isThm(p.padding))
      return `<span class="muted" data-computed title="${esc(L.proofNote || "")}">computed, not a theorem</span>`;
    const title = `header-pages checked the statement exactly: ${p.statement || ""}; axioms: ${(Array.isArray(p.axioms) ? p.axioms.join(", ") : "") || "none"} (standard only)`;
    return `<span class="hdr-ok" title="${esc(title)}">theorem</span> ${thmRef(p, "layout")}` +
      `<br><span class="muted">padding counts:</span> ${thmRef(p.padding, "padding")}`;
  }

  function layoutTable(a, dms) {
    const names = a.members.map((m) => m.name);
    let h = '<table class="hdr"><thead><tr><th>member</th><th>type</th>' + dms.map((dm) => `<th>${esc(dm)}<br><span class="muted">bit offset / bits</span></th>`).join("") + "</tr></thead><tbody>";
    for (const [i, m] of a.members.entries()) {
      h += `<tr data-member="${esc(m.name)}"><td><code>${esc(m.name)}</code></td><td><code>${esc(m.type)}</code>${m.bits != null ? ` : ${esc(m.bits)}` : ""}</td>` +
        dms.map((dm) => { const L = a.layouts[dm]; if (!L || L.refused != null) return "<td></td>";
          const s = L.ok.members.find((x) => x.name === names[i]); return `<td>${s ? `${esc(s.bitOffset)} / ${esc(s.bits)}` + (s.bitOffset % 8 === 0 && s.bits % 8 === 0 ? ` <span class="muted">(byte ${esc(s.bitOffset / 8)}, ${esc(s.bits / 8)} B)</span>` : "") : ""}</td>`; }).join("") + "</tr>";
    }
    h += "<tr><th colspan=2>size / align</th>" + dms.map((dm) => { const L = a.layouts[dm];
      return `<td data-dm="${esc(dm)}">${!L ? "" : L.refused != null ? `<span class="hdr-refused">refused: ${esc(L.refused)}</span>` : `<b>${esc(L.ok.size)} / ${esc(L.ok.align)}</b>`}</td>`; }).join("") + "</tr>";
    h += '<tr><th colspan=2>padding <span class="muted">(bytes no named member occupies; contents unspecified)</span></th>' + dms.map((dm) => { const L = a.layouts[dm];
      return `<td data-pad="${esc(dm)}">${!L || L.refused != null || !L.ok.padding ? "" : L.ok.padding.length === 0 ? "none" :
        `${esc(L.ok.paddingBytes)} B: ` + L.ok.padding.map(([lo, hi]) => `[${esc(lo)}, ${esc(hi)})`).join(" ")}` +
        `${L && L.refused == null && L.ok.paddingBits != null ? ` <span class="muted">(${esc(L.ok.paddingBits)} padding bits)</span>` : ""}</td>`; }).join("") + "</tr>";
    h += '<tr><th colspan=2>kernel theorem <span class="muted">(this column\'s slots, size, alignment and padding counts)</span></th>' +
      dms.map((dm) => `<td data-proof="${esc(dm)}">${proofCell(a.layouts[dm])}</td>`).join("") + "</tr>";
    return h + "</tbody></table>";
  }

  // The subset reader's route.
  function subsetSection(d, h) {
    if (h.read == null) return '<h3 data-route="subset">Subset reader route</h3><p class="muted" data-read="none">No subset-reader route for this header.</p>';
    let x = '<h3 data-route="subset">Subset reader route</h3>' +
      `<p>files: ${(h.files || []).map((f) => `<code>${esc(f.path)}</code>`).join(", ")} · root <code>${esc(h.root)}</code>` +
      (h.text != null ? `<br><span class="muted" data-text>read from the compiled-in constant <code>${esc(h.text)}</code>, the text its layout theorems are about (the file must equal it for a theorem to be named)</span>` : "") + "</p>" +
      `<p class="hdr-note">Computed by <code>Silmaril.Data.Layout.Header.read</code>, each ABI definition's <code>lower</code> and the layout definitions (<code>bitLayout</code>), run on these files: these are the values the conformance rows and layout theorems are about, not theorems themselves. ` +
      `A layout column that names a theorem is the exception: <code>header-pages</code> checked that the theorem states exactly this column's layout of this header's definitions, with only the standard axioms.</p>`;
    if (h.read.refused != null) return x + `<p class="hdr-refused" data-read="refused">The subset reader refuses this header: ${esc(h.read.refused)}</p>`;
    const abis = d.abis.map((a) => a.name);
    x += "<h4>Prototypes</h4>" + `<p class="muted">${d.abis.map((a) => `<code>${esc(a.name)}</code> = ${esc(a.id)}`).join(" · ")}</p>` +
      '<div class="tablebox"><table class="hdr"><thead><tr><th>C prototype</th>' + abis.map((a) => `<th>${esc(a)}</th>`).join("") + "</tr></thead><tbody>" +
      (h.prototypes || []).map((p) => `<tr data-fn="${esc(p.name)}"><td><code>${esc(p.c)}</code>${p.quals ? `<br><span class="muted" title="qualifiers by pointer level (Header.quals?)">quals ${esc(p.quals)}</span>` : ""}</td>` +
        abis.map((a) => `<td data-abi="${esc(a)}">${lowerCell(p.lowering[a])}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
    if ((h.typedefs || []).length) x += "<h4>Typedefs</h4><ul>" + h.typedefs.map((t) => `<li><code>${esc(t.name)}</code> = <code>${esc(t.type)}</code></li>`).join("") + "</ul>";
    if ((h.enums || []).length) x += "<h4>Enums</h4><ul>" + h.enums.map((e) => `<li><code>enum ${esc(e.tag)}</code>: ${e.constants.map(([c, v]) => `${esc(c)} = ${esc(v)}`).join(", ")}</li>`).join("") + "</ul>";
    if ((h.aggregates || []).length) x += "<h4>Aggregates</h4>" + h.aggregates.map((a) => `<h4 data-agg="${esc(a.tag)}"><code>${esc(a.kind)} ${esc(a.tag)}</code></h4>` + layoutTable(a, d.dataModels)).join("");
    return x;
  }

  // A status cell's text: what `Conformance.status` says, with the reason.
  const statusText = (s) => !s ? "—" : s.status === "claimable" ? "claimable"
    : s.status === "notFunction" ? "not a function" : `${s.status}: ${s.why}`;
  const statusCell = (s, l) => {
    const cls = !s ? "muted" : s.status === "claimable" ? "hdr-ok" : s.status === "unsupported" ? "hdr-refused" : "hdr-internal";
    return `<span class="${cls}">${esc(statusText(s))}</span>` + (s && s.status === "claimable" && l ? `<div class="hdr-plan">${lowerCell(l)}</div>` : "");
  };

  // The clang route of one pinned import.
  function clangSection(d, c) {
    const p = c.provenance || {}, n = c.counts || {}, abis = d.abis.map((a) => a.name);
    const row = (k, v) => `<tr data-prov="${esc(k)}"><th>${esc(k)}</th><td>${v}</td></tr>`;
    let x = `<h3 data-route="clang">Clang route: <code>${esc(c.value)}</code></h3><p class="muted">clang read ${esc(c.relation)}.</p>` +
      `<p class="hdr-note">The entries are the generated literal <code>${esc(c.literal)}</code> and the provenance is the committed <code>.prov</code>; ` +
      `each status is computed by <code>Machine.Abi.Conformance.status</code> with each ABI definition's conventions, and each lowering and call plan by the same definitions as the subset route: ` +
      `${esc(d.clangNote || "")}.</p>` +
      '<h4>Provenance</h4><table class="hdr hdr-prov"><tbody>' +
      row("image", `<code>${esc(p.image)}</code>`) + row("clang", esc(p.clang)) + row("target", `<code>${esc(p.target)}</code>`) +
      row("std", `<code>${esc(p.std)}</code>`) + row("command", `<code>${esc(p.command)}</code>`) +
      row("defines", (p.defines || []).length ? p.defines.map((x) => `<code>${esc(x)}</code>`).join(", ") : '<span class="muted">none</span>') +
      row("includes", (p.includes || []).length ? p.includes.map((x) => `<code>${esc(x)}</code>`).join(", ") : '<span class="muted">none</span>') +
      (p.source != null ? row("source", `<code>${esc(p.source)}</code>`) : "") +
      row("inputs", (p.inputs || []).map((i) => `<code>${esc(i.file)}</code> <span class="muted">sha256 ${esc(i.sha256)}</span>`).join("<br>")) +
      row("JSON", `<code>${esc(p.artifact)}</code> <span class="muted">${esc(p.jsonBytes)} bytes, sha256 ${esc(p.jsonSha256)}</span>`) +
      row("filter", `<code>${esc(p.filter)}</code> <span class="muted">sha256 ${esc(p.filterSha256)}</span>`) + "</tbody></table>";
    x += `<h4>Counts</h4><p data-clang-counts><span data-count="total">${esc(n.total)}</span> entries · <span data-count="functions">${esc(n.functions)}</span> functions · ` +
      `<span data-count="implicit">${esc(n.implicit)}</span> implicit · <span data-count="unsupported">${esc(n.unsupported)}</span> the import does not read (with its reason)</p>` +
      '<table class="hdr"><thead><tr><th>ABI</th><th>conventions</th><th>interface functions</th><th>claimable</th><th>unsupported</th></tr></thead><tbody>' +
      d.abis.map((a) => { const k = (c.abiCounts || {})[a.name] || {};
        return `<tr data-abi-count="${esc(a.name)}"><td><code>${esc(a.name)}</code></td><td>${(a.clangCcs || []).map((x) => `<code>${esc(x)}</code>`).join(", ")}${a.clangCcsNote ? `<br><span class="muted" data-ccs-note>${esc(a.clangCcsNote)}</span>` : ""}</td>` +
          `<td data-n="interface">${esc(k.interface)}</td><td data-n="claimable">${esc(k.claimable)}</td><td data-n="unsupported">${esc(k.unsupported)}</td></tr>`; }).join("") + "</tbody></table>";
    x += '<h4>Entries</h4><div class="tablebox"><table class="hdr"><thead><tr><th>#</th><th>name</th><th>kind</th><th>location</th><th>C declaration</th><th>convention</th><th>attributes</th><th>symbol</th>' +
      abis.map((a) => `<th>${esc(a)}</th>`).join("") + "</tr></thead><tbody>" +
      (c.entries || []).map((e, i) => {
        const decl = !e.decl ? "" : e.decl.unsupported != null ? `<span class="hdr-refused" data-c="unsupported">import: ${esc(e.decl.unsupported)}</span>` : `<code data-c="ok">${esc(e.decl.ok)}</code>`;
        const kind = esc(e.kind) + (e.implicit ? ' <span class="muted" data-implicit>implicit</span>' : "") +
          (e.storage != null ? ` · ${esc(e.storage)}` : "") + (e.inline ? " · inline" : "") + (e.variadic ? " · variadic" : "");
        return `<tr data-entry="${esc(i)}" data-name="${esc(e.name)}"><td>${esc(i)}</td><td><code>${esc(e.name)}</code></td><td>${kind}</td>` +
          `<td>${e.loc ? `<code>${esc(e.loc.file)}:${esc(e.loc.line)}</code>` : ""}</td><td>${decl}</td>` +
          `<td data-cc>${e.cc != null ? `<code>${esc(e.cc)}</code>` : ""}</td><td data-attrs>${(e.attrs || []).map((a) => esc(a)).join(", ")}</td>` +
          `<td data-symbol>${e.symbol != null ? `<code>${esc(e.symbol)}</code>` : ""}${e.asmLabel != null ? `<br><span class="muted" data-asm>asm label <code>${esc(e.asmLabel)}</code></span>` : ""}</td>` +
          abis.map((a) => `<td data-cabi="${esc(a)}" data-status="${esc(e.status && e.status[a] ? e.status[a].status : "")}">${statusCell(e.status && e.status[a], e.lowering && e.lowering[a])}</td>`).join("") + "</tr>";
      }).join("") + "</tbody></table></div>";
    return x;
  }

  function headerPage(d, h) {
    let x = `<h2><a href="#/headers">Headers</a> / ${esc(h.title)}</h2><p class="muted">${esc(h.note || "")}</p>`;
    x += subsetSection(d, h);
    x += h.clang ? clangSection(d, h.clang) : '<h3 data-route="clang">Clang route</h3><p class="muted" data-clang="none">No pinned clang import of this header.</p>';
    return x;
  }

  async function view(arg) {
    let d;
    try { d = await load(); } catch (e) {
      return `<h2>Headers</h2><p class="muted">The header data is not available (${esc(e.message)}); <code>make pages</code> writes it with <code>header-pages</code>.</p>`;
    }
    if (arg) {
      const h = d.headers.find((x) => x.id === decodeURIComponent(arg));
      return h ? headerPage(d, h) : `<p>No header <code>${esc(arg)}</code>.</p>`;
    }
    return "<h2>Headers</h2><p>C headers by two routes: as the subset reader reads them, with each prototype's lowering under every versioned ABI definition and each aggregate's layout under two data models; and as a pinned clang import, with each declaration's status for every ABI definition.</p>" +
      `<p class="hdr-note">${esc(d.note)}; ${esc(d.clangNote || "")}</p><table class="hdr"><thead><tr><th>header</th><th>subset reader</th><th>prototypes</th><th>aggregates</th><th>clang route</th></tr></thead><tbody>` +
      d.headers.map((h) => `<tr data-header="${esc(h.id)}"><td><a href="#/headers/${esc(enc(h.id))}">${esc(h.title)}</a></td><td>${h.read == null ? '<span class="muted">—</span>' : h.read.refused != null ? `<span class="hdr-refused">refused</span>` : '<span class="hdr-ok">read</span>'}</td>` +
        `<td>${esc((h.prototypes || []).length)}</td><td>${esc((h.aggregates || []).length)}</td>` +
        `<td data-clang-total>${h.clang ? `<code>${esc(h.clang.value)}</code>: ${esc(h.clang.counts ? h.clang.counts.total : "")} entries` : '<span class="muted">—</span>'}</td></tr>`).join("") + "</tbody></table>";
  }
  registerView({ id: "headers", title: "Headers", nav: 85.7, render: (arg) => view(arg) });
})();
