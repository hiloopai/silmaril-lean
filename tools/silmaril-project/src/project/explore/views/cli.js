// ---------- CLI: verified input/output of ELF executables, and CLI specifications ----------
// Data: elf/cli.json, written by `elf-pages` (tools/elf-pages). Every Lean link of a record is a
// declaration name that elf-pages found in the checked environment; its kind, status, axioms,
// statement and source line are read from that declaration. A record's other fields (the input,
// output and model it describes) are the registry's reading of those statements.
(() => {
  let cliData = null;
  async function cliJson() {
    if (!cliData) cliData = fetch("elf/cli.json").then((r) => { if (!r.ok) throw new Error(`elf/cli.json: HTTP ${r.status}`); return r.json(); })
      .catch((e) => { cliData = null; throw e; });
    return cliData;
  }
  if (!document.getElementById("cli-style")) {
    const st = document.createElement("style");
    st.id = "cli-style";
    st.textContent = "button.linkish { border:0; background:none; padding:0; color:var(--accent); text-decoration:underline; cursor:pointer; font:inherit; text-align:left; }";
    document.head.appendChild(st);
  }
  const missing = (e) => `<p class="err">The CLI page data is not available here (${esc(e.message || e)}). It is written by <code>elf-pages</code> (<code>make pages</code>).</p>`;
  const STATUS_CLASS = (s) => s === "proved" || s.startsWith("proved by") ? "prov-lean" : s === "specification" || s === "trusted model" || s === "definition" || s === "uninstantiated shape" ? "prov-browser" : "st-bad";
  // Whether the declaration is checked to be about the record (elf-pages' association check: its
  // statement mentions, or has a subterm definitionally equal to, an anchor of every group).
  function assocCell(e) {
    if (e.association === "checked")
      return `<span class="prov prov-lean" title="${esc("about: " + e.about.map((g) => g.join(" | ")).join("; "))}">checked: about this record</span>`;
    if (e.association === "curated") return '<span class="st st-bad">curated reference (association not checked)</span>';
    return '<span class="muted">—</span>';
  }
  const counts = (e) => e.status === "proved" && e.association === "checked";
  function statusPill(e) {
    const t = `${e.kind}; axioms: ${e.axioms.join(", ") || "none"}`;
    const cls = STATUS_CLASS(e.status);
    return cls === "st-bad" ? `<span class="st st-bad" title="${esc(t)}">${esc(e.status)}</span>` : `<span class="prov ${cls}" title="${esc(t)}">${esc(e.status)}</span>`;
  }
  function declCell(e) {
    const f = typeof repoFile === "function" ? repoFile(e.file) : null;
    const src = f ? ` <a href="${esc(f.blob)}${e.line ? "#L" + e.line : ""}" target="_blank" rel="noopener noreferrer">source</a>`
      : ` <span class="muted">${esc(e.file.split("/").pop())}${e.line ? ":" + e.line : ""}</span>`;
    return `<code title="${esc(e.decl)}">${esc(e.decl.split(".").slice(-2).join("."))}</code>${src}`;
  }
  function edgesTable(edges) {
    return '<div class="tablebox"><table class="cli-edges"><thead><tr><th>role</th><th>declaration</th><th>status</th><th>about this record</th><th>summary (curated)</th><th>statement</th></tr></thead><tbody>' +
      edges.map((e) => `<tr data-role="${esc(e.role)}" data-assoc="${esc(e.association || "")}"><td>${esc(e.role)}</td><td>${declCell(e)}</td><td>${statusPill(e)}</td><td>${assocCell(e)}</td><td>${esc(e.note)}</td>` +
        `<td><details><summary class="muted">${esc(e.kind)}</summary><pre class="code">${esc(e.statement)}</pre></details></td></tr>`).join("") + "</tbody></table></div>";
  }
  const dl = (pairs) => pairs.length ? "<dl>" + pairs.map(([k, v]) => `<dt>${esc(k)}</dt><dd>${esc(v)}</dd>`).join("") + "</dl>" : '<p class="muted">none</p>';
  function tabs(on) {
    return '<div class="elf-tabs">' + [["verified I/O (ELF)", "#/cli"], ["specifications", "#/cli-specs"]]
      .map(([t, h]) => `<a href="${h}" class="${t.startsWith(on) ? "on" : ""}">${esc(t)}</a>`).join("") + "</div>";
  }
  const verdict = (r) => {
    // a verdict needs a proof checked to be about this record, not a theorem that merely exists
    const proved = r.edges.some((e) => e.role.startsWith("proves") && counts(e));
    const open = r.edges.filter((e) => e.role.startsWith("open"));
    return proved ? `<span class="prov prov-lean">verified under the stated model</span>${open.length ? ` <span class="st" title="obligations that would remove trusted assumptions">${open.length} open obligation${open.length > 1 ? "s" : ""}</span>` : ""}`
      : '<span class="st st-bad">no verified input/output pair</span>';
  };

  async function cliIo(arg) {
    let d;
    try { d = await cliJson(); } catch (e) { return missing(e); }
    let h = "<h2>CLI</h2>" + tabs("verified") +
      "<p>Executables with a <b>verified input/output relation</b>: what the run is given, what it shows, the machine, loader, C library and system-call model the proof is stated in, and every Lean declaration involved with its status read from the checked environment. " +
      "<b>Trusted</b> parts of a model are listed as such; <b>open obligations</b> are the statements that would remove them, not proved here; a <b>shape</b> with no instance is neither. " +
      "A proof counts for a record only when it is <b>checked to be about that record</b>: its statement mentions the record's binary, model and specification (or a term definitionally equal to them). The one-line summaries are curated text; a theorem's status does not certify them.</p>";
    h += '<div class="tablebox"><table><thead><tr><th>executable</th><th>level</th><th>input</th><th>output</th><th>status</th></tr></thead><tbody>' +
      d.io.map((r) => `<tr id="cli-io-${esc(r.id)}"><td><button type="button" class="linkish" data-go="cli-rec-${esc(r.id)}">${esc(r.title)}</button>${r.elfSlug ? `<br><a href="#/elf-file/${encodeURIComponent(r.elfSlug)}">ELF tab</a>` : ""}</td>` +
        `<td>${esc(r.level)}</td><td>${r.input.map(([k, v]) => `<b>${esc(k)}</b>: ${esc(v)}`).join("<br>")}</td>` +
        `<td>${r.output.map(([k, v]) => `<b>${esc(k)}</b>: <code>${esc(v)}</code>`).join("<br>") || '<span class="muted">—</span>'}</td><td>${verdict(r)}</td></tr>`).join("") + "</tbody></table></div>";
    for (const r of d.io) {
      h += `<h2 id="cli-rec-${esc(r.id)}">${esc(r.title)}</h2><p class="muted"><code>${esc(r.binary)}</code> · SHA-256 <code>${esc(r.sha256)}</code>${r.elfSlug ? ` · <a href="#/elf-file/${encodeURIComponent(r.elfSlug)}">bytes, parts and functions</a>` : ""}</p>` +
        `<div class="grid"><div><h3>Input</h3>${dl(r.input)}</div><div><h3>Output</h3>${dl(r.output)}</div><div><h3>Model</h3>${dl(r.model)}</div></div>` +
        `<h3>Lean</h3>${edgesTable(r.edges)}` + (r.limits.length ? `<h3>Limits</h3><ul>${r.limits.map((l) => `<li>${esc(l)}</li>`).join("")}</ul>` : "");
    }
    return { html: h, init: wireGo };
  }

  // In-page jumps without touching the hash (the hash is the route).
  function wireGo() {
    for (const b of document.querySelectorAll("main button[data-go]"))
      b.addEventListener("click", () => document.getElementById(b.dataset.go)?.scrollIntoView({ block: "start" }));
  }

  async function cliSpecs(arg) {
    let d;
    try { d = await cliJson(); } catch (e) { return missing(e); }
    let h = "<h2>CLI</h2>" + tabs("specifications") +
      "<p>Specifications of command-line programs: sentences of the CLI institution (<code>Silmaril.Cli.Institution</code>) and argument grammars (<code>Silmaril.Cli.Spec</code>). " +
      "Each row keeps the <b>specification</b>, the <b>implementation</b> it is about and the <b>refinement proofs</b> apart; a specification with no refinement proof is only a specification.</p>";
    h += '<div class="tablebox"><table><thead><tr><th>specification</th><th>kind</th><th>level</th><th>implementation</th><th>refinement</th></tr></thead><tbody>' +
      d.specs.map((r) => {
        const ref = r.edges.filter((e) => e.role.startsWith("refinement") && counts(e));
        return `<tr id="cli-spec-${esc(r.id)}"><td><button type="button" class="linkish" data-go="cli-spec-rec-${esc(r.id)}">${esc(r.title)}</button></td><td>${esc(r.kind)}</td><td>${esc(r.level)}</td>` +
          `<td>${r.implementation.map(([k, v]) => `<b>${esc(k)}</b>: <code>${esc(v)}</code>`).join("<br>")}</td>` +
          `<td>${ref.length ? ref.map((e) => `${statusPill(e)} ${declCell(e)}`).join("<br>") : '<span class="muted">none</span>'}</td></tr>`;
      }).join("") + "</tbody></table></div>";
    for (const r of d.specs) {
      h += `<h2 id="cli-spec-rec-${esc(r.id)}">${esc(r.title)}</h2>${edgesTable(r.edges)}` + (r.notes.length ? `<ul>${r.notes.map((n) => `<li>${esc(n)}</li>`).join("")}</ul>` : "");
    }
    return { html: h, init: wireGo };
  }

  registerView({ id: "cli", title: "CLI", nav: 86, render: cliIo });
  registerView({ id: "cli-specs", title: "CLI specifications", tab: "cli", render: cliSpecs });
})();
