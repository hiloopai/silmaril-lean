// The Headers tab: C headers as the subset reader reads them, each prototype as every versioned
// ABI definition lowers it (or refuses it, with the reason), the System V scalar call plan, and
// each aggregate's layout under two data models. Data: headers/index.json (`header-pages`,
// silmaril.header-pages/1). Every value is computed by the definitions the conformance rows and
// layout theorems use; none is shown as a theorem.
(() => {
  const DATA = "headers/index.json", SCHEMA = "silmaril.header-pages/1";
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
    st.textContent = `.hdr-refused{color:#a33}.hdr-ok{color:#174}.hdr-plan{font-size:90%;color:#555}
      table.hdr td,table.hdr th{padding:2px 8px;vertical-align:top;border-bottom:1px solid #eee}
      .hdr-note{background:#fff8e6;border-left:3px solid #d90;padding:6px 10px;max-width:70em}`;
    document.head.appendChild(st);
  }
  const lowerCell = (l) => !l ? '<span class="muted">—</span>'
    : l.refused != null ? `<span class="hdr-refused" title="the ABI definition's lowering refuses this prototype">refused: ${esc(l.refused)}</span>`
    : `<span class="hdr-ok">${esc(l.ok)}</span>` + (l.plan ? (l.plan.ok ? `<div class="hdr-plan">args: ${esc(l.plan.ok.arguments.join(" · ") || "none")}<br>result: ${esc(l.plan.ok.result)}</div>`
      : `<div class="hdr-plan hdr-refused">plan refused: ${esc(l.plan.refused)}</div>`) : "");

  function layoutTable(a, dms) {
    const names = a.members.map((m) => m.name);
    let h = '<table class="hdr"><thead><tr><th>member</th><th>type</th>' + dms.map((dm) => `<th>${esc(dm)}<br><span class="muted">bit offset / bits</span></th>`).join("") + "</tr></thead><tbody>";
    for (const [i, m] of a.members.entries()) {
      h += `<tr data-member="${esc(m.name)}"><td><code>${esc(m.name)}</code></td><td><code>${esc(m.type)}</code>${m.bits != null ? ` : ${esc(m.bits)}` : ""}</td>` +
        dms.map((dm) => { const L = a.layouts[dm]; if (!L || L.refused != null) return "<td></td>";
          const s = L.ok.members.find((x) => x.name === names[i]); return `<td>${s ? `${esc(s.bitOffset)} / ${esc(s.bits)}` + (s.bitOffset % 8 === 0 && s.bits % 8 === 0 ? ` <span class="muted">(byte ${s.bitOffset / 8}, ${s.bits / 8} B)</span>` : "") : ""}</td>`; }).join("") + "</tr>";
    }
    h += "<tr><th colspan=2>size / align</th>" + dms.map((dm) => { const L = a.layouts[dm];
      return `<td data-dm="${esc(dm)}">${!L ? "" : L.refused != null ? `<span class="hdr-refused">refused: ${esc(L.refused)}</span>` : `<b>${esc(L.ok.size)} / ${esc(L.ok.align)}</b>`}</td>`; }).join("") + "</tr>";
    return h + "</tbody></table>";
  }

  function headerPage(d, h) {
    let x = `<h2><a href="#/headers">Headers</a> / ${esc(h.title)}</h2><p class="muted">${esc(h.note || "")}</p>` +
      `<p>files: ${h.files.map((f) => `<code>${esc(f.path)}</code>`).join(", ")} · root <code>${esc(h.root)}</code></p>` +
      `<p class="hdr-note">Computed by <code>Silmaril.Data.Layout.Header.read</code>, each ABI definition's <code>lower</code> and the layout definitions (<code>bitLayout</code>), run on these files: these are the values the conformance rows and layout theorems are about, not theorems themselves.</p>`;
    if (h.read.refused != null) return x + `<p class="hdr-refused" data-read="refused">The subset reader refuses this header: ${esc(h.read.refused)}</p>`;
    const abis = d.abis.map((a) => a.name);
    x += "<h3>Prototypes</h3>" + `<p class="muted">${d.abis.map((a) => `<code>${esc(a.name)}</code> = ${esc(a.id)}`).join(" · ")}</p>` +
      '<div class="tablebox"><table class="hdr"><thead><tr><th>C prototype</th>' + abis.map((a) => `<th>${esc(a)}</th>`).join("") + "</tr></thead><tbody>" +
      (h.prototypes || []).map((p) => `<tr data-fn="${esc(p.name)}"><td><code>${esc(p.c)}</code>${p.quals ? `<br><span class="muted" title="qualifiers by pointer level (Header.quals?)">quals ${esc(p.quals)}</span>` : ""}</td>` +
        abis.map((a) => `<td data-abi="${esc(a)}">${lowerCell(p.lowering[a])}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
    if ((h.typedefs || []).length) x += "<h3>Typedefs</h3><ul>" + h.typedefs.map((t) => `<li><code>${esc(t.name)}</code> = <code>${esc(t.type)}</code></li>`).join("") + "</ul>";
    if ((h.enums || []).length) x += "<h3>Enums</h3><ul>" + h.enums.map((e) => `<li><code>enum ${esc(e.tag)}</code>: ${e.constants.map(([c, v]) => `${esc(c)} = ${esc(v)}`).join(", ")}</li>`).join("") + "</ul>";
    if ((h.aggregates || []).length) x += "<h3>Aggregates</h3>" + h.aggregates.map((a) => `<h4 data-agg="${esc(a.tag)}"><code>${esc(a.kind)} ${esc(a.tag)}</code></h4>` + layoutTable(a, d.dataModels)).join("");
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
    return "<h2>Headers</h2><p>C headers as the subset reader reads them, with each prototype's lowering under every versioned ABI definition and each aggregate's layout under two data models.</p>" +
      `<p class="hdr-note">${esc(d.note)}</p><table class="hdr"><thead><tr><th>header</th><th>read</th><th>prototypes</th><th>aggregates</th></tr></thead><tbody>` +
      d.headers.map((h) => `<tr data-header="${esc(h.id)}"><td><a href="#/headers/${enc(h.id)}">${esc(h.title)}</a></td><td>${h.read.refused != null ? `<span class="hdr-refused">refused</span>` : '<span class="hdr-ok">read</span>'}</td>` +
        `<td>${(h.prototypes || []).length}</td><td>${(h.aggregates || []).length}</td></tr>`).join("") + "</tbody></table>";
  }
  registerView({ id: "headers", title: "Headers", nav: 85.7, render: (arg) => view(arg) });
})();
