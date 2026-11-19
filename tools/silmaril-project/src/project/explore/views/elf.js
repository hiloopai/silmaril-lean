// ---------- ELF: pinned executables, their checked parts, bytes and an unverified disassembly ----------
// Static files written by `elf-pages` (tools/elf-pages, `make pages`) next to the page:
// elf/index.json, elf/f/<slug>.json (a file: header, segments, sections, loader view, symbols,
// theorems with their byte windows, axioms and source lines, and the coverage of every byte),
// elf/dis/<slug>.json (objdump's listing, external and unverified) and elf/blob/<slug>.bin (the
// file). Which bytes a theorem covers comes from its statement (`PartIs F windows reader value`,
// `ZerosAt F offset length`), read by elf-pages from the checked environment; this view only
// draws what those files say.
(() => {
  const elfCache = new Map();
  function elfFetch(rel, how) {
    if (!elfCache.has(rel)) elfCache.set(rel, fetch("elf/" + rel).then((r) => {
      if (!r.ok) throw new Error(`elf/${rel}: HTTP ${r.status}`);
      return how === "bytes" ? r.arrayBuffer().then((b) => new Uint8Array(b)) : r.json();
    }));
    return elfCache.get(rel).catch((e) => { elfCache.delete(rel); throw e; });
  }
  const elfJson = (rel) => elfFetch(rel, "json");
  const elfMissing = (e) => `<p class="err">The ELF page data is not available here (${esc(e.message || e)}). ` +
    "It is written by <code>elf-pages</code> (<code>make pages</code>) next to the page.</p>";
  const enc = encodeURIComponent;
  const hx = (n) => n == null ? "" : "0x" + Number(n).toString(16);
  const hx8 = (n) => Number(n).toString(16).padStart(8, "0");
  const num = (s) => { const t = String(s || "").trim().toLowerCase(); if (!t) return null; const v = t.startsWith("0x") ? parseInt(t.slice(2), 16) : /^[0-9]+$/.test(t) ? parseInt(t, 10) : parseInt(t, 16); return Number.isFinite(v) ? v : null; };
  const flink = (slug, text) => `<a href="#/elf-file/${enc(slug)}">${esc(text)}</a>`;
  const blink = (slug, off, len, text) => `<a href="#/elf-bytes/${enc(slug)}/${hx(off)}${len ? "/" + len : ""}" title="bytes ${esc(hx(off))}${len ? "+" + len : ""}">${esc(text == null ? hx(off) : text)}</a>`;
  const dlink = (slug, at, text) => `<a href="#/elf-disasm/${enc(slug)}/${esc(at)}">${esc(text)}</a>`;
  const CLASS_TEXT = {
    decoded: "decoded: inside the windows of a checked part (PartIs): the bytes the specification's reader reads to produce a value a theorem states",
    zeros: "zeros: a checked ZerosAt theorem says these bytes are zero (padding)",
    raw: "raw: not parsed. The byte is inside a section or loaded segment whose extent a checked theorem states (a section body such as .progbits (offset, length), read with an empty window, or a program header), but no theorem says anything about its contents beyond their being the pinned file's bytes (code, constants, data, unread string bytes)",
    unknown: "unknown: in no section, segment, checked part or checked padding",
  };
  const DIS_WARNING = "UNVERIFIED: external disassembler output (GNU objdump), not checked in Lean. elf-pages compared each row's bytes " +
    "with the file's bytes at that address; the decoding (instruction boundaries, mnemonics, operands) is objdump's alone, and no " +
    "theorem relates it to the ELF parts. Code-looking bytes, or bytes in an executable section, are not thereby executed.";

  // Styles of this view only (the shell's stylesheet is shared by every view).
  if (!document.getElementById("elf-style")) {
    const st = document.createElement("style");
    st.id = "elf-style";
    st.textContent = `
.elf-tabs { display:flex; gap:4px; margin:6px 0 10px; } .elf-tabs a { padding:3px 10px; border:1px solid var(--line); border-radius:4px; text-decoration:none; }
.elf-tabs a.on { background:var(--accent); color:#fff; border-color:var(--accent); }
.elf-c-decoded { background:#dff3e5; } .elf-c-zeros { background:#e8edf3; color:#7b8794; } .elf-c-raw { background:#fff3d6; } .elf-c-unknown { background:#fbdada; }
.elf-key span { display:inline-block; padding:0 6px; margin-right:8px; border:1px solid var(--line); border-radius:3px; font-size:12px; }
.elf-cov { display:flex; height:16px; width:100%; max-width:860px; border:1px solid var(--line); border-radius:3px; overflow:hidden; }
.elf-cov a { display:block; height:100%; }
.elf-cov .elf-c-decoded { background:#4caf6e; } .elf-cov .elf-c-zeros { background:#aab7c4; } .elf-cov .elf-c-raw { background:#e8b84a; } .elf-cov .elf-c-unknown { background:#d64545; }
.elf-hexwrap { display:flex; gap:14px; align-items:flex-start; flex-wrap:wrap; }
table.elf-hex td { border:0; padding:0 1px; font-size:12px; } table.elf-hex td.o { color:var(--muted); padding-right:8px; } table.elf-hex td.v { color:#7b6aa8; padding-right:8px; }
table.elf-hex span.b { display:inline-block; width:2.1em; text-align:center; cursor:pointer; border-radius:2px; }
table.elf-hex span.b.sel { outline:2px solid var(--accent); outline-offset:-1px; font-weight:700; }
table.elf-hex td.a { padding-left:10px; white-space:pre; color:#444; }
#elf-side { flex:1 1 320px; max-width:520px; border:1px solid var(--line); background:var(--panel); padding:8px 10px; font-size:13px; }
.elf-warn { border-left:4px solid var(--fails); background:#fdecec; padding:6px 10px; margin:8px 0; max-width:1000px; font-weight:600; }
.elf-warn.sticky { position:sticky; top:0; z-index:2; }
table.elf-dis td { border:0; border-bottom:1px solid #f0f2f4; padding:1px 8px 1px 0; } table.elf-dis tr.lbl td { color:#a3157a; font-weight:600; padding-top:6px; }
table.elf-dis tr.hit td { background:#fff1b8; }
.elf-ok { color:#1f7a3a; } .elf-bad { color:var(--fails); font-weight:600; }
`;
    document.head.appendChild(st);
  }

  // A theorem: its status (from its axioms), its short name and its source line.
  function thmCell(t) {
    if (!t) return '<span class="muted">none</span>';
    const st = t.status === "checked" ? `<span class="prov prov-lean" title="checked by the Lean kernel (decide +kernel on kernel bytes); axioms: ${esc(t.axioms.join(", ") || "none")} (standard only, no native evaluation)">kernel ✓</span>`
      : t.status === "sorry" ? '<span class="st st-bad" title="depends on sorryAx">sorry</span>'
      : `<span class="st st-bad" title="axioms: ${esc(t.axioms.join(", "))}">extra axioms</span>`;
    const f = typeof repoFile === "function" ? repoFile(t.file) : null;
    const src = f ? ` <a href="${esc(f.blob)}${t.line ? "#L" + t.line : ""}" target="_blank" rel="noopener noreferrer">source</a>`
      : ` <span class="muted" title="${esc(t.file)}">${esc(t.file.split("/").pop())}${t.line ? ":" + t.line : ""}</span>`;
    return `${st} <code title="${esc(t.decl)}">${esc(t.short)}</code>${src}`;
  }
  const thmByDecl = (d) => new Map(d.theorems.map((t) => [t.decl, t]));
  function covBar(slug, size, runs) {
    return '<div class="elf-cov">' + runs.map(([o, n, c]) => `<a class="elf-c-${esc(c)}" style="width:${(100 * n / size).toFixed(4)}%" ` +
      `href="#/elf-bytes/${enc(slug)}/${hx(o)}/${n}" title="${esc(c)}: ${n} B at ${hx(o)}"></a>`).join("") + "</div>";
  }
  function covKey(sum) {
    return '<p class="elf-key">' + ["decoded", "zeros", "raw", "unknown"].map((c) =>
      `<span class="elf-c-${c}" title="${esc(CLASS_TEXT[c])}">${c}: ${sum[c] ?? 0} B</span>`).join("") + "</p>" +
      '<p class="muted elf-covnote">Only <b>decoded</b> bytes have parsed content in a theorem. <b>Raw</b> bytes lie in checked ranges, but their contents ' +
      "(code, constants, data) are not parsed or given meaning. <b>Unknown: 0</b> means every byte lies in some checked range; it does not mean every payload is decoded.</p>";
  }
  function tabs(slug, on) {
    return '<div class="elf-tabs">' + [["overview", `#/elf-file/${enc(slug)}`], ["bytes", `#/elf-bytes/${enc(slug)}/0x0`],
      ["functions", `#/elf-funcs/${enc(slug)}`], ["disassembly (unverified)", `#/elf-disasm/${enc(slug)}`],
      ["regions", `#/elf-regions/${enc(slug)}`], ["graph", `#/elf-graph/${enc(slug)}`],
      ["theorems", `#/elf-file/${enc(slug)}/theorems`]].map(([t, h]) =>
      `<a href="${h}" class="${t.startsWith(on) ? "on" : ""}">${esc(t)}</a>`).join("") + "</div>";
  }
  function head(d, on) {
    const ko = d.theorems.every((t) => t.kernelOnly);
    return `<h2><a href="#/elf">ELF</a> / ${esc(d.title)}</h2>` +
      `<p class="muted"><code>${esc(d.path)}</code> · ${d.size} B · SHA-256 <code>${esc(d.sha256)}</code> · ${esc(d.header.type)} ${esc(d.header.machine)}</p>` +
      `<p>${d.theorems.length} theorems in ${[...new Set(d.theorems.map((t) => t.module))].map((m) => `<code>${esc(m)}</code>`).join(", ")}, ` +
      (ko ? '<span class="prov prov-lean">all kernel-only (propext, Classical.choice, Quot.sound)</span>' : '<span class="st st-bad">some use other axioms</span>') +
      ". Each part is the ELF specification's reader run on the pinned file's bytes inside the windows its theorem states.</p>" + tabs(d.slug, on);
  }

  // ---------- index ----------
  async function elfIndex() {
    let ix, ds;
    try { ix = await elfJson("index.json"); ds = await Promise.all(ix.files.map((f) => elfJson(`f/${enc(f.slug)}.json`))); } catch (e) { return elfMissing(e) + await compilerArtifactIndex("elf"); }
    let h = "<h2>ELF</h2><p>Pinned ELF files, read by the Lean ELF specification (<code>Silmaril.Elf.read</code>) part by part on kernel bytes. " +
      "Each part (header, program and section headers, section names and bodies, the loader's view, zero padding) is a theorem checked by the kernel " +
      "on the exact bytes of the file (<code>include_bytes</code>); the byte coverage of each file is derived from those theorems' statements.</p>";
    h += '<div class="tablebox"><table><thead><tr><th>file</th><th>type</th><th>size</th><th>sections</th><th>segments</th><th>functions</th><th>theorems</th><th>axioms</th><th>coverage</th><th>SHA-256</th></tr></thead><tbody>' +
      ix.files.map((f, i) => `<tr><td>${flink(f.slug, f.title)}<br><span class="muted">${esc(f.path)}</span></td><td>${esc(f.type)} ${esc(f.machine)}</td>` +
        `<td class="num">${f.size}</td><td class="num">${f.sections}</td><td class="num">${f.segments}</td><td class="num"><a href="#/elf-funcs/${enc(f.slug)}">${f.functions ?? ""}</a></td><td class="num">${f.theorems}</td>` +
        `<td>${f.kernelOnly ? '<span class="prov prov-lean">kernel-only</span>' : '<span class="st st-bad">other</span>'}</td>` +
        `<td style="min-width:260px">${covBar(f.slug, f.size, ds[i].coverage)}${covKey(f.coverageSummary)}</td>` +
        `<td><code title="${esc(f.sha256)}">${esc(f.sha256.slice(0, 16))}…</code></td></tr>`).join("") + "</tbody></table></div>";
    return h + await compilerArtifactIndex("elf");
  }

  // ---------- one file: overview and theorems ----------
  async function elfFile(arg) {
    const [slug, sub] = arg.split("/");
    let d;
    try { d = await elfJson(`f/${enc(slug)}.json`); } catch (e) { return elfMissing(e); }
    const T = thmByDecl(d);
    const th = (n) => thmCell(n ? T.get(n) : null);
    if (sub === "theorems") return head(d, "theorems") + theoremList(d);
    const H = d.header;
    let h = head(d, "overview");
    h += "<h2>Coverage of the file</h2>" + covBar(d.slug, d.size, d.coverage) + covKey(d.coverageSummary);
    h += '<div class="grid"><div><h2>Identity and provenance</h2><dl>' +
      [["path", esc(d.path)], ["size", d.size + " B"], ["SHA-256", `<code>${esc(d.sha256)}</code> <button type="button" id="elf-sha">recompute in the browser</button> <span id="elf-shaout" class="muted"></span>`],
        ["Lean bytes", `<code>${esc(d.bytesModule)}</code> (<code>raw</code>: include_bytes; <code>K</code>: kernel bytes)`]]
        .concat(d.provenance.map(([k, v]) => [k.replace(/^url:/, ""), k.startsWith("url:") ? `<a href="${esc(v)}" target="_blank" rel="noopener noreferrer">${esc(v)}</a>` : esc(v)]))
        .map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v}</dd>`).join("") + "</dl></div>";
    h += `<div><h2>ELF header</h2><p>${th(H.theorem)}</p><dl>` + [["class", H.class + ", " + H.data], ["type", H.type], ["machine", `${H.machine} (${H.machineCode})`],
      ["entry", H.entry ? `${hx(H.entry)} ${dlink(d.slug, hx(H.entry), "disassembly")}` : "0"], ["program headers", `${H.phnum} × ${H.phentsize} B at ${blink(d.slug, H.phoff, H.phnum * H.phentsize)}`],
      ["section headers", `${H.shnum} × ${H.shentsize} B at ${blink(d.slug, H.shoff, H.shnum * H.shentsize)}`], ["section names", `section ${H.shstrndx}`],
      ["OS/ABI, ABI version", `${H.osabi}, ${H.abiversion}`], ["flags", hx(H.flags)]].map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v}</dd>`).join("") + "</dl></div></div>";
    // segments
    h += `<h2>Program headers (segments, ${d.segments.length})</h2><div class="tablebox"><table><thead><tr><th>#</th><th>type</th><th>flags</th><th>file bytes</th><th>virtual addresses</th><th>memory only</th><th>sections</th><th>theorem</th></tr></thead><tbody>` +
      d.segments.map((s) => `<tr><td class="num">${s.idx}</td><td>${esc(s.type)}</td><td>${esc(s.flags)}</td>` +
        `<td>${s.filesz ? blink(d.slug, s.offset, s.filesz, `${hx(s.offset)}–${hx(s.offset + s.filesz)}`) : '<span class="muted">none</span>'} <span class="muted">(${s.filesz} B)</span></td>` +
        `<td>${hx(s.vaddr)}–${hx(s.vaddr + s.memsz)} <span class="muted">(${s.memsz} B, align ${s.align})</span></td>` +
        `<td>${s.memsz > s.filesz ? `<span title="memsz > filesz: zero-filled by the loader, not in the file">${s.memsz - s.filesz} B (zero-filled)</span>` : ""}</td>` +
        `<td>${s.sections.map((i) => esc(d.sections[i].name || "#" + i)).join(" ")}</td><td>${th(s.theorem)}</td></tr>`).join("") + "</tbody></table></div>";
    // sections
    h += `<h2>Sections (${d.sections.length})</h2>` + (d.sections.length ? "" : '<p class="note">No section header table: the program headers and the loader view are still read.</p>') +
      '<div class="tablebox"><table><thead><tr><th>#</th><th>name</th><th>type</th><th>flags</th><th>file bytes</th><th>address</th><th>segment</th><th>body</th><th>header</th><th>name</th><th>body theorem</th></tr></thead><tbody>' +
      d.sections.map((s) => `<tr id="elf-sec-${s.idx}"><td class="num">${s.idx}</td><td><code>${esc(s.name)}</code></td><td>${esc(s.type)}</td><td>${esc(s.flags)}</td>` +
        `<td>${s.fileBytes ? blink(d.slug, s.offset, s.fileBytes, `${hx(s.offset)}+${s.fileBytes}`) : `<span class="muted" title="${s.type === "NOBITS" ? "NOBITS: occupies memory, not the file" : "empty"}">none${s.type === "NOBITS" ? ` (${s.size} B in memory)` : ""}</span>`}</td>` +
        `<td>${s.addr ? hx(s.addr) : '<span class="muted">not loaded</span>'}</td><td>${s.segments.join(" ")}</td>` +
        `<td>${esc(s.body)}${s.decoded ? ' <span class="elf-ok" title="a typed table: the body theorem states its entries">decoded</span>' : ""}${bodySummary(s)}${s.exec ? " " + dlink(d.slug, s.name, "disassembly") : ""}</td>` +
        `<td>${th(s.headerTheorem)}</td><td>${th(s.nameTheorem)}</td><td>${th(s.bodyTheorem)}</td></tr>`).join("") + "</tbody></table></div>";
    // loader
    const Ld = d.loader;
    h += `<h2>Loader view</h2><p>${th(Ld.theorem)}</p><dl>` + [["interpreter (PT_INTERP)", Ld.interp], ["needed (DT_NEEDED)", Ld.needed.join(", ")],
      ["soname", Ld.soname], ["runpath", Ld.runpath]].map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v == null || v === "" ? '<span class="muted">none</span>' : esc(v)}</dd>`).join("") + "</dl>" +
      (Ld.dynamic.length ? `<details><summary>${Ld.dynamic.length} dynamic entries</summary><div class="tablebox"><table><thead><tr><th>tag</th><th>value</th></tr></thead><tbody>` +
        Ld.dynamic.map(([t, n, v]) => `<tr><td>${esc(n)} <span class="muted">${hx(t)}</span></td><td>${hx(v)}</td></tr>`).join("") + "</tbody></table></div></details>" : "");
    // symbols
    h += `<h2>Symbols (${d.symbols.length})</h2>` + (d.symbols.length ? '<div class="controls"><input type="text" id="elf-symq" placeholder="filter symbols" size="30"> <span id="elf-symn" class="muted"></span></div><div id="elf-syms"></div>' : '<p class="muted">none</p>') +
      `<p class="muted">From the checked bodies of the symbol tables (section body theorems).</p>`;
    // limits
    h += "<h2>Coverage limits and unsupported parts</h2><ul>" + d.unsupported.map((u) => `<li>${esc(u)}</li>`).join("") + "</ul>";
    const init = () => {
      wireSha(d);
      const box = $("#elf-syms");
      if (!box) return;
      const show = () => {
        const q = $("#elf-symq").value.toLowerCase();
        const rows = d.symbols.filter((s) => !q || s.name.toLowerCase().includes(q));
        $("#elf-symn").textContent = `${rows.length} of ${d.symbols.length}` + (rows.length > 400 ? " (first 400 shown)" : "");
        box.innerHTML = '<div class="tablebox"><table><thead><tr><th>table</th><th>#</th><th>name</th><th>value</th><th>size</th><th>type</th><th>bind</th><th>section</th></tr></thead><tbody>' +
          rows.slice(0, 400).map((s) => `<tr><td>${esc(s.table)}</td><td class="num">${s.idx}</td><td><code>${esc(s.name)}</code></td>` +
            `<td>${s.value ? (s.type === "FUNC" && s.shndx ? dlink(d.slug, hx(s.value), hx(s.value)) : hx(s.value)) : "0"}</td><td class="num">${s.size}</td><td>${esc(s.type)}</td><td>${esc(s.bind)}</td><td>${s.shndx || '<span class="muted">UND</span>'}</td></tr>`).join("") + "</tbody></table></div>";
      };
      $("#elf-symq").addEventListener("input", show);
      show();
    };
    return { html: h, init };
  }
  function bodySummary(s) {
    const x = s.detail || {};
    if (x.count != null) return ` <span class="muted">${x.count} entries</span>`;
    if (x.nbuckets != null) return ` <span class="muted">${x.nbuckets} buckets</span>`;
    return "";
  }
  function wireSha(d) {
    const b = $("#elf-sha");
    if (!b) return;
    b.addEventListener("click", async () => {
      $("#elf-shaout").textContent = "…";
      try {
        const bytes = await elfFetch(`blob/${enc(d.slug)}.bin`, "bytes");
        const h = [...new Uint8Array(await crypto.subtle.digest("SHA-256", bytes))].map((x) => x.toString(16).padStart(2, "0")).join("");
        $("#elf-shaout").innerHTML = h === d.sha256 ? `<span class="elf-ok">matches</span> (${bytes.length} B)` : `<span class="elf-bad">differs: ${esc(h)}</span>`;
      } catch (e) { $("#elf-shaout").textContent = String(e.message || e); }
    });
  }
  function theoremList(d) {
    const kinds = ["part", "zeros", "layout", "parses"];
    let h = `<p>Statements: <code>PartIs F ws p v</code> (the reader <code>p</code> of the ELF specification, run on the bytes of <code>F</code> inside the windows <code>ws</code> only, returns <code>v</code>), ` +
      "<code>ZerosAt F o n</code>, <code>LayoutIs F L</code> and <code>Parses F A</code> (the whole parse, assembled from the parts). Status and axioms are read by elf-pages from the built module (<code>collectAxioms</code>).</p>";
    h += '<div class="tablebox"><table><thead><tr><th>theorem</th><th>kind</th><th>about</th><th>windows (offset+length)</th><th>axioms</th></tr></thead><tbody>' +
      d.theorems.slice().sort((a, b) => kinds.indexOf(a.kind) - kinds.indexOf(b.kind)).map((t) => `<tr><td>${thmCell(t)}</td><td>${esc(t.kind)}</td><td>${esc(t.label)}</td>` +
        `<td>${t.windows.slice(0, 6).map(([o, n]) => blink(d.slug, o, n, `${hx(o)}+${n}`)).join(" ")}${t.windows.length > 6 ? ` <span class="muted">+${t.windows.length - 6} more</span>` : ""}</td>` +
        `<td class="muted">${esc(t.axioms.join(", ") || "none")}</td></tr>`).join("") + "</tbody></table></div>";
    return h;
  }

  // ---------- bytes ----------
  const PAGE = 4096;
  // The parts of the file at offset `o`: sections, segments, theorems whose windows hold it, its class.
  function at(d, o) {
    const secs = d.sections.filter((s) => s.fileBytes && s.offset <= o && o < s.offset + s.fileBytes);
    const segs = d.segments.filter((s) => s.filesz && s.offset <= o && o < s.offset + s.filesz);
    const thms = d.theorems.filter((t) => t.windows.some(([w, n]) => w <= o && o < w + n));
    const run = d.coverage.find(([w, n]) => w <= o && o < w + n);
    const load = segs.find((s) => s.type === "LOAD");
    return { secs, segs, thms, cls: run ? run[2] : "unknown", vaddr: load ? o - load.offset + load.vaddr : null };
  }
  async function elfBytes(arg) {
    const [slug, offS, lenS] = arg.split("/");
    let d, bytes;
    try { [d, bytes] = await Promise.all([elfJson(`f/${enc(slug)}.json`), elfFetch(`blob/${enc(slug)}.bin`, "bytes")]); } catch (e) { return elfMissing(e); }
    let sel = Math.min(Math.max(0, num(offS) ?? 0), d.size - 1);
    let selLen = Math.max(1, Math.min(num(lenS) ?? 1, d.size - sel));
    const page0 = Math.floor(sel / PAGE) * PAGE;
    const cls = new Array(d.size);
    for (const [o, n, c] of d.coverage) for (let i = o; i < o + n; i++) cls[i] = c;
    let h = head(d, "bytes");
    h += covBar(d.slug, d.size, d.coverage) + covKey(d.coverageSummary);
    h += `<div class="controls"><a href="#/elf-bytes/${enc(slug)}/${hx(Math.max(0, page0 - PAGE))}">◀ previous 4 KiB</a>` +
      `<span>bytes ${hx(page0)}–${hx(Math.min(d.size, page0 + PAGE))} of ${hx(d.size)}</span>` +
      `<a href="#/elf-bytes/${enc(slug)}/${hx(Math.min(d.size - 1, page0 + PAGE))}">next 4 KiB ▶</a>` +
      '<label>offset <input type="text" id="elf-goo" size="10" placeholder="0x…"></label><label>virtual address <input type="text" id="elf-gov" size="12" placeholder="0x…"></label>' +
      '<button type="button" id="elf-go">go</button> <span id="elf-goerr" class="err"></span></div>';
    let rows = "";
    for (let r = page0; r < Math.min(d.size, page0 + PAGE); r += 16) {
      const a = at(d, r);
      let bs = "", asc = "";
      for (let i = r; i < Math.min(d.size, r + 16); i++) {
        const b = bytes[i];
        bs += `<span class="b elf-c-${cls[i] || "unknown"}${i >= sel && i < sel + selLen ? " sel" : ""}" data-o="${i}">${b.toString(16).padStart(2, "0")}</span>`;
        asc += b >= 32 && b < 127 ? String.fromCharCode(b) : ".";
      }
      rows += `<tr><td class="o">${hx8(r)}</td><td class="v">${a.vaddr == null ? "" : hx8(a.vaddr)}</td><td>${bs}</td><td class="a">${esc(asc)}</td>` +
        `<td class="muted">${esc(a.secs.map((s) => s.name).join(" "))}</td></tr>`;
    }
    h += '<div class="elf-hexwrap"><div class="tablebox"><table class="elf-hex"><thead><tr><th>offset</th><th>vaddr</th><th>bytes (coloured by coverage)</th><th>ASCII</th><th>section</th></tr></thead><tbody>' +
      rows + '</tbody></table></div><div id="elf-side"></div></div>';
    const side = () => {
      const a = at(d, sel), b = bytes.subarray(sel, sel + selLen);
      const exec = a.secs.find((s) => s.exec);
      $("#elf-side").innerHTML = `<h3>Selection ${hx(sel)}${selLen > 1 ? `+${selLen}` : ""}</h3>` +
        `<p><span class="elf-c-${a.cls}" title="${esc(CLASS_TEXT[a.cls])}">&nbsp;${esc(a.cls)}&nbsp;</span> <span class="muted">${esc(CLASS_TEXT[a.cls])}</span></p>` +
        `<dl><dt>file offset</dt><dd>${hx(sel)} (${sel})</dd><dt>virtual address</dt><dd>${a.vaddr == null ? '<span class="muted">not mapped by a PT_LOAD</span>' : hx(a.vaddr)}</dd>` +
        `<dt>bytes</dt><dd><code>${[...b.subarray(0, 64)].map((x) => x.toString(16).padStart(2, "0")).join(" ")}${selLen > 64 ? " …" : ""}</code></dd>` +
        `<dt>sections</dt><dd>${a.secs.map((s) => `${esc(s.name)} <span class="muted">#${s.idx}, ${hx(sel - s.offset)} in</span>`).join("<br>") || '<span class="muted">none</span>'}</dd>` +
        `<dt>segments</dt><dd>${a.segs.map((s) => `${s.idx} ${esc(s.type)} ${esc(s.flags)}`).join("<br>") || '<span class="muted">none</span>'}</dd></dl>` +
        (exec && a.vaddr != null ? `<p>${dlink(d.slug, hx(a.vaddr), "disassembly at " + hx(a.vaddr))} <span class="muted">(unverified)</span></p>` : "") +
        `<h3>Theorems whose windows hold ${hx(sel)} (${a.thms.length})</h3>` +
        (a.thms.length ? "<ul>" + a.thms.map((t) => `<li>${thmCell(t)}<br><span class="muted">${esc(t.label)}; windows ${t.windows.slice(0, 4).map(([o, n]) => blink(d.slug, o, n, `${hx(o)}+${n}`)).join(" ")}${t.windows.length > 4 ? " …" : ""}</span></li>`).join("") + "</ul>"
          : '<p class="muted">No checked part reads this byte.</p>');
    };
    const paint = () => {
      for (const e of document.querySelectorAll("table.elf-hex span.b")) { const o = +e.dataset.o; e.classList.toggle("sel", o >= sel && o < sel + selLen); }
      side();
      history.replaceState(null, "", `#/elf-bytes/${enc(slug)}/${hx(sel)}${selLen > 1 ? "/" + selLen : ""}`);
    };
    const init = () => {
      side();
      const s = document.querySelector("table.elf-hex span.b.sel");
      if (s) s.scrollIntoView({ block: "center" });
      $("table.elf-hex").addEventListener("click", (ev) => {
        const e = ev.target.closest("span.b");
        if (!e) return;
        const o = +e.dataset.o;
        if (ev.shiftKey && o >= sel) selLen = o - sel + 1; else { sel = o; selLen = 1; }
        paint();
      });
      $("#elf-go").addEventListener("click", () => {
        const o = num($("#elf-goo").value), v = num($("#elf-gov").value);
        let target = o;
        if (v != null) {
          const s = d.segments.find((s) => s.type === "LOAD" && s.vaddr <= v && v < s.vaddr + s.memsz);
          if (!s) { $("#elf-goerr").textContent = `${hx(v)} is in no PT_LOAD`; return; }
          if (v >= s.vaddr + s.filesz) { $("#elf-goerr").textContent = `${hx(v)} is in memory only (zero-filled, beyond the segment's file bytes)`; return; }
          target = v - s.vaddr + s.offset;
        }
        if (target == null || target < 0 || target >= d.size) { $("#elf-goerr").textContent = "offset outside the file"; return; }
        location.hash = `#/elf-bytes/${enc(slug)}/${hx(target)}`;
      });
    };
    return { html: h, init };
  }

  // ---------- disassembly (external, unverified) ----------
  const DPAGE = 400;
  async function elfDisasm(arg) {
    const [slug, target] = arg.split("/");
    let d, x;
    try { d = await elfJson(`f/${enc(slug)}.json`); } catch (e) { return elfMissing(e); }
    let h = head(d, "disassembly") + `<div class="elf-warn sticky" role="note">${esc(DIS_WARNING)}</div>`;
    if (!d.disassembly.file) return h + `<p class="muted">${esc(d.disassembly.note || "no disassembly")}</p>`;
    try { x = await elfJson(d.disassembly.file); } catch (e) { return h + elfMissing(e); }
    // The listing is in chunks of rows ([file, first address, last address, rows]); a page is
    // DPAGE rows of one chunk, and a row's global index is the chunk's start plus its own.
    const starts = []; let acc = 0;
    for (const c of x.chunks) { starts.push(acc); acc += c[3]; }
    const total = acc;
    const t = target || "";
    let ci = 0, hitG = -1;
    if (/^(0x)?[0-9a-f]+$/i.test(t)) {
      const v = num(t);
      ci = Math.max(0, x.chunks.findIndex((c) => c[2] >= v));
      if (x.chunks.every((c) => c[2] < v)) ci = x.chunks.length - 1;
    } else if (t.startsWith("@")) {
      const g = Number(t.slice(1)) | 0;
      ci = Math.max(0, starts.findLastIndex((st) => st <= g)); hitG = g;
    }
    let rows;
    try { rows = await elfJson(x.chunks[ci][0]); } catch (e) { return h + elfMissing(e); }
    if (/^(0x)?[0-9a-f]+$/i.test(t)) {
      const v = num(t);
      let i = rows.findIndex(([a, , b]) => a <= v && v < a + b.length / 2);
      if (i < 0) i = rows.findIndex(([a]) => a >= v);
      if (i >= 0) hitG = starts[ci] + i;
    } else if (t && !t.startsWith("@")) {
      // a section name: the first chunk that holds it
      for (let k = 0; k < x.chunks.length; k++) {
        const r = k === ci ? rows : await elfJson(x.chunks[k][0]);
        const i = r.findIndex((row) => row[4] === t);
        if (i >= 0) { ci = k; rows = r; hitG = starts[k] + i; break; }
      }
    }
    const local = hitG >= 0 ? hitG - starts[ci] : 0;
    const p0 = Math.floor(local / DPAGE) * DPAGE, start = starts[ci] + p0, hit = hitG;
    h += `<p class="muted">${esc(x.tool)}: <code>${esc(x.command)}</code> (listing <code>${esc(x.listing || "")}</code>); ${total} instructions in ${x.sections.length} sections: ` +
      x.sections.map((s) => dlink(slug, s, s)).join(" ") + "</p>";
    h += `<div class="controls">${start > 0 ? dlink(slug, "@" + Math.max(0, start - DPAGE), "◀ previous") : ""}<span>rows ${start + 1}–${Math.min(total, start + DPAGE)} of ${total}</span>` +
      `${start + DPAGE < total ? dlink(slug, "@" + (start + DPAGE), "next ▶") : ""}<label>address <input type="text" id="elf-dgo" size="12" placeholder="0x…"></label><button type="button" id="elf-dgob">go</button></div>`;
    let body = "", sec = null;
    for (let i = start; i < Math.min(total, start + DPAGE) && i - starts[ci] < rows.length; i++) {
      const [a, off, bytes, text, s, label] = rows[i - starts[ci]];
      if (s !== sec || label) body += `<tr class="lbl"><td colspan="4">${s !== sec ? esc(s) + " " : ""}${label ? "&lt;" + esc(label) + "&gt;" : ""}</td></tr>`;
      sec = s;
      body += `<tr${i === hit ? ' class="hit" id="elf-hit"' : ""}><td>${off == null ? hx(a) : blink(slug, off, bytes.length / 2, hx(a))}</td>` +
        `<td class="muted">${off == null ? "" : hx(off)}</td><td><code>${esc(bytes.match(/../g).join(" "))}</code></td><td><code>${esc(text)}</code></td></tr>`;
    }
    h += '<div class="tablebox"><table class="elf-dis"><thead><tr><th>address (→ bytes)</th><th>offset</th><th>raw bytes</th><th>objdump text</th></tr></thead><tbody>' + body + "</tbody></table></div>";
    const init = () => {
      const e = $("#elf-hit");
      if (e) e.scrollIntoView({ block: "center" });
      $("#elf-dgob").addEventListener("click", () => { const v = num($("#elf-dgo").value); if (v != null) location.hash = `#/elf-disasm/${enc(slug)}/${hx(v)}`; });
    };
    return { html: h, init };
  }


  // ---------- functions ----------
  // One row per STT_FUNC / STT_GNU_IFUNC entry of a symbol table (elf-pages `functions`). The row
  // is what the symbol table says (its theorem: Pinned.*.Functions.sym_K_I, the entry as
  // Parse.symbol reads it from its 24 bytes and its name); the extent, file offset, segment,
  // section, aliases and overlaps follow from the checked layout. A contract is linked only when a
  // theorem's statement names the function's address (Pinned.*.Contracts).
  const FN_NOTE = "A row is a symbol-table entry of type FUNC or IFUNC, checked on the file's bytes. It is not a recovered function: " +
    "its extent is the symbol's st_value and st_size (unknown when st_size is 0), nothing checks that the bytes there are code or one function, " +
    "an IFUNC entry is a resolver (the implementation is chosen at load time), and an undefined entry is an import. " +
    "No row asserts the System V ABI: only a linked contract theorem says anything about calls.";
  const FPAGE = 300;
  async function elfFuncs(arg) {
    const [slug] = arg.split("/");
    let d;
    try { d = await elfJson(`f/${enc(slug)}.json`); } catch (e) { return elfMissing(e); }
    const T = thmByDecl(d);
    const fs = d.functions || [];
    const counts = { defined: fs.filter((f) => f.defined).length, imports: fs.filter((f) => !f.defined).length,
      unknown: fs.filter((f) => f.defined && f.size === 0).length, ifunc: fs.filter((f) => f.ifunc).length,
      contracts: fs.filter((f) => f.contracts.length).length };
    const tables = [...new Set(fs.map((f) => f.table))];
    let h = head(d, "functions") + `<p class="note">${esc(FN_NOTE)}</p>`;
    h += `<p>${fs.length} function symbols (${tables.map(esc).join(", ") || "no symbol table"}): ${counts.defined} defined, ${counts.imports} imports, ` +
      `${counts.unknown} with unknown extent (size 0), ${counts.ifunc} IFUNC; <b>${counts.contracts}</b> with a contract theorem, the others have <b>no contract statement</b> in this repository.</p>`;
    h += '<div class="controls"><input type="text" id="elf-fq" placeholder="filter by name or version" size="30">' +
      '<label><input type="checkbox" id="elf-fdef" checked> defined only</label><label><input type="checkbox" id="elf-fcon"> with contract</label>' +
      '<span id="elf-fn" class="muted"></span> <span id="elf-fpg"></span></div><div id="elf-ft"></div>';
    const init = () => {
      let page = 0;
      const cell = (f) => {
        const t = T.get(f.theorem);
        return t ? thmCell(t) : '<span class="st st-bad">no theorem</span>';
      };
      const contract = (f) => f.contracts.length ? f.contracts.map((c) => { const t = T.get(c); return t ? `${thmCell(t)}<details><summary>statement</summary><pre class="code">${esc(t.statement || "")}</pre></details>` : esc(c); }).join("<br>")
        : '<span class="muted">no contract statement</span>';
      const show = () => {
        const q = $("#elf-fq").value.toLowerCase(), def = $("#elf-fdef").checked, con = $("#elf-fcon").checked;
        const rows = fs.filter((f) => (!def || f.defined) && (!con || f.contracts.length) && (!q || (f.name + (f.version || "")).toLowerCase().includes(q)));
        const pages = Math.max(1, Math.ceil(rows.length / FPAGE));
        page = Math.min(page, pages - 1);
        $("#elf-fn").textContent = `${rows.length} of ${fs.length}`;
        $("#elf-fpg").innerHTML = pages > 1 ? `<button type="button" id="elf-fprev"${page ? "" : " disabled"}>◀</button> page ${page + 1} of ${pages} <button type="button" id="elf-fnext"${page + 1 < pages ? "" : " disabled"}>▶</button>` : "";
        $("#elf-ft").innerHTML = '<div class="tablebox"><table class="elf-fns"><thead><tr><th>symbol</th><th>version</th><th>type, bind</th><th>address</th><th>size / extent</th><th>file offset</th><th>segment</th><th>section</th><th>aliases, overlaps</th><th>symbol theorem</th><th>contract</th></tr></thead><tbody>' +
          rows.slice(page * FPAGE, (page + 1) * FPAGE).map((f) => `<tr data-fn="${esc(f.name)}"><td><code>${esc(f.name)}</code><br><span class="muted">${esc(f.table)} #${f.idx}</span></td>` +
            `<td>${esc(f.version || "")}</td><td>${esc(f.type)}${f.ifunc ? ' <span class="st" title="a resolver: the implementation is chosen at load time">resolver</span>' : ""}<br><span class="muted">${esc(f.bind)}</span></td>` +
            `<td>${f.defined && f.value ? (f.offset != null ? dlink(slug, hx(f.value), hx(f.value)) : hx(f.value)) : '<span class="muted">—</span>'}</td>` +
            `<td>${f.size || ""} <span class="${f.extent.startsWith("known") ? "muted" : "st"}">${esc(f.extent)}</span></td>` +
            `<td>${f.offset != null ? blink(slug, f.offset, f.size || 1, hx(f.offset)) : '<span class="muted">—</span>'}</td>` +
            `<td>${f.segment != null ? `${f.segment} <span class="muted">${esc(f.segmentFlags || "")}</span>` : ""}</td><td>${esc(f.section || "")}</td>` +
            `<td>${f.aliases.length ? "alias of " + f.aliases.map(esc).join(", ") : ""}${f.overlaps.length ? `<br><span class="st" title="ranges intersect but differ">overlaps ${f.overlaps.map(esc).join(", ")}</span>` : ""}</td>` +
            `<td>${cell(f)}</td><td>${contract(f)}</td></tr>`).join("") + "</tbody></table></div>";
        $("#elf-fprev")?.addEventListener("click", () => { page--; show(); });
        $("#elf-fnext")?.addEventListener("click", () => { page++; show(); });
      };
      for (const id of ["#elf-fq", "#elf-fdef", "#elf-fcon"]) $(id).addEventListener("input", () => { page = 0; show(); });
      show();
    };
    return { html: h, init };
  }

  // ---------- region rows and their full outgoing adjacency ----------
  const regionProof = (c) => {
    const src = typeof repoFile === "function" ? repoFile(c.file) : null;
    return `<span class="prov prov-lean">byte/CFG kernel certificate</span> <code>${esc(c.decl)}</code>` +
      (src ? ` <a href="${esc(src.blob)}${c.line ? "#L" + c.line : ""}" target="_blank" rel="noopener noreferrer">source</a>` : "") +
      `<details><summary>statement and axioms</summary><pre>${esc(c.statement)}</pre><p>${esc(c.axioms.join(", ") || "no axioms")}</p></details>`;
  };
  const regionSource = (r) => {
    const src = typeof repoFile === "function" ? repoFile(r.provenance.file) : null;
    return `<details><summary>row provenance</summary><code>${esc(r.provenance.declaration)}</code>` +
      (src ? ` <a href="${esc(src.blob)}" target="_blank" rel="noopener noreferrer">source</a>` : `<p>${esc(r.provenance.file)}</p>`) + '</details>';
  };
  const regionStatus = (r, sha) => ElfRegions.certification(r, sha).kind === "stated"
    ? '<span class="prov prov-gen">stated · certificate unknown</span>'
    : '<span class="prov prov-lean">certified bytes + direct CFG</span>';
  const labels = (xs) => xs.map(hx).join(", ") || "∅";
  const edgeLabels = (xs) => xs.map((x) => x.split(":").map((n) => hx(+n)).join(" → ")).join(", ") || "∅";
  async function elfRegions(arg, graphTab = false) {
    const [slug, requested] = arg.split("/");
    let d, data;
    try { [d, data] = await Promise.all([elfJson(`f/${enc(slug)}.json`), elfJson(`regions/${enc(slug)}.json`)]); }
    catch (e) { return elfMissing(e); }
    if (data.sha256 !== d.sha256 || data.schema !== "silmaril.elf-regions.v1") return '<p class="err">Region data image/schema mismatch.</p>';
    let h = head(d, graphTab ? "graph" : "regions") + `<p class="note">${esc(data.scope)}</p>` +
      '<p>Certificates bind ELF bytes and exact direct-transfer syntax. Execution soundness has separate loading, admitted-invariant, and interference premises. ' +
      'Normal edges do not prove progress, termination or absence of traps/faults. Missing certificates remain unknown.</p>';
    if (!data.rows.length) return h + '<p>No region/CFG rows are exported for this file.</p>';
    const rows = data.rows;
    const option = (r, selected) => `<option value="${esc(r.id)}"${r.id === selected ? " selected" : ""}>${esc(r.title)}</option>`;
    if (graphTab) {
      const selected = rows.find((r) => r.id === decodeURIComponent(requested || "")) || rows[0];
      h += `<label>Graph constant <select id="elf-graph-row">${rows.map((r) => option(r, selected.id)).join("")}</select></label><div id="elf-graph"></div>`;
      return { html: h, init: () => {
        const show = () => {
          const r = rows.find((r) => r.id === $("#elf-graph-row").value), g = ElfRegions.graph(r);
          const nodes = new Map(g.nodes.map((n, i) => [n.id, { ...n,
            x: 340 + 210 * Math.cos(i * 2 * Math.PI / g.nodes.length - Math.PI / 2),
            y: 190 + 125 * Math.sin(i * 2 * Math.PI / g.nodes.length - Math.PI / 2) }]));
          const paths = g.edges.map((e, i) => {
            const a = nodes.get(e.source), b = nodes.get(e.target), dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy) || 1;
            const parallel = g.edges.slice(0, i).filter((x) => x.source === e.source && x.target === e.target).length;
            const path = a.id === b.id ? `M ${a.x - 12} ${a.y - 15} C ${a.x - 65} ${a.y - 90 - parallel * 16}, ${a.x + 65} ${a.y - 90 - parallel * 16}, ${a.x + 15} ${a.y - 15}`
              : `M ${a.x + dx * 39 / len} ${a.y + dy * 20 / len} Q ${(a.x + b.x) / 2 - dy * parallel * .12} ${(a.y + b.y) / 2 + dx * parallel * .12} ${b.x - dx * 42 / len} ${b.y - dy * 23 / len}`;
            return `<path data-edge="${e.source}:${e.target}" d="${path}" fill="none" stroke="#526576" stroke-width="2" marker-end="url(#elf-cfg-arrow)"><title>${hx(e.source)} → ${hx(e.target)}</title></path>`;
          }).join("");
          const vertices = [...nodes.values()].map((n) => `<g data-node="${n.id}"><rect x="${n.x - 39}" y="${n.y - 20}" width="78" height="40" rx="${n.internal ? 18 : 2}" fill="${n.entry ? "#d5e9ff" : n.internal ? "#e3f3e6" : "#fff0ce"}" stroke="#526576"/><text x="${n.x}" y="${n.y + 4}" text-anchor="middle" font-size="13">${hx(n.id)}</text><title>${n.entry ? "entry; " : ""}${n.internal ? "internal instruction start" : "outside support"}${n.exit ? "; declared exit" : ""}</title></g>`).join("");
          $("#elf-graph").innerHTML = `<h3>${esc(r.title)}</h3><p>${regionStatus(r, data.sha256)}</p>` +
            `<svg role="img" aria-label="Directed instruction CFG" viewBox="0 -60 680 440" style="max-width:800px;width:100%;border:1px solid var(--line)"><defs><marker id="elf-cfg-arrow" markerWidth="8" markerHeight="8" refX="7" refY="3" orient="auto"><path d="M0,0 L0,6 L8,3 z" fill="#526576"/></marker></defs>${paths}${vertices}</svg>` +
            '<p class="muted">Blue: entry. Rounded green: internal instruction starts. Square amber: outside support. Outgoing arrows are successors, including loops and cross edges; no dominance arcs are inferred. Layout is browser-generated.</p>' +
            '<h3>Relationships and properties</h3><table><thead><tr><th>view</th><th>representation / orientation</th><th>properties</th><th>status / loss</th></tr></thead><tbody>' +
            `<tr><td>Directed multi / edge rows</td><td>source → successor, edge-row identities</td><td>${g.properties.vertices} vertices; ${g.properties.edgeRows} edges; ${g.properties.loops} loops; ${g.properties.parallelDuplicates} duplicate pairs</td><td>Displayed verbatim; row IDs are serialization positions, not machine events</td></tr>` +
            `<tr><td>Directed relation</td><td>ordered pairs; loops allowed</td><td>${g.properties.relationalEdges} distinct pairs</td><td>Certificate checks this extensional view; parallel identities forgotten</td></tr>` +
            `<tr><td>Undirected simple projection</td><td>symmetrized unordered pairs; no loops</td><td>${g.properties.undirectedSimpleEdges} pairs</td><td>Browser computation; loses direction, loops and multiplicity</td></tr>` +
            '<tr><td>Dominator tree</td><td>Immediate-dominance children differ from outgoing edges</td><td>Not supplied</td><td>Requires rooted reachability and a separate dominance witness</td></tr></tbody></table>' +
            '<h3>Complete adjacency</h3><table><thead><tr><th>source</th><th>target</th><th>boundary role</th></tr></thead><tbody>' +
            g.edges.map((e) => `<tr><td>${hx(e.source)}</td><td>${hx(e.target)}</td><td>${r.vertices.includes(e.target) ? "internal" : "outward"}${r.exits.includes(e.target) ? "; declared exit" : ""}</td></tr>`).join("") + '</tbody></table>' +
            `<p><a href="#/elf-regions/${enc(slug)}">Compare region rows and proof provenance</a></p>`;
        };
        $("#elf-graph-row").addEventListener("change", show); show();
      }};
    }
    h += '<div class="tablebox"><table id="elf-regions"><thead><tr><th>row / provenance</th><th>byte extent (half-open)</th><th>boundary / support</th><th>evidence</th></tr></thead><tbody>' +
      rows.map((r) => `<tr data-region="${esc(r.id)}"><td><b>${esc(r.title)}</b><br>${regionStatus(r, data.sha256)}${regionSource(r)}<br><a href="#/elf-graph/${enc(slug)}/${enc(r.id)}">graph</a></td>` +
        `<td>ELF VA [${hx(r.va)}, ${hx(r.va + r.size)})<br>${r.offset == null ? "no file mapping" : blink(slug, r.offset, r.size, `file [${hx(r.offset)}, ${hx(r.offset + r.size)})`)}<br><code>${r.bytes.map((b) => b.toString(16).padStart(2, "0")).join(" ")}</code></td>` +
        `<td>entry ${hx(r.entry)}<br>exits ${labels(r.exits)}<br>instruction starts ${labels(r.vertices)}</td><td>` +
        ElfRegions.certification(r, data.sha256).evidence.map(regionProof).join("") +
        `<p>Native consistency checker: ${r.nativeIntrinsicAccepted ? "accepts" : "rejects"} (not a kernel certificate)</p><details><summary>execution scope</summary>${esc(r.execution)}</details></td></tr>`).join("") + '</tbody></table></div>';
    const defaultB = rows.find((r) => r.id.endsWith(".statedCompare")) || rows[1] || rows[0];
    h += `<h3>Compare decompositions of this image</h3><div class="controls"><label>A <select id="elf-region-a">${rows.map((r) => option(r, rows[0].id)).join("")}</select></label>` +
      `<label>B <select id="elf-region-b">${rows.map((r) => option(r, defaultB.id)).join("")}</select></label></div><div id="elf-region-comparison"></div>`;
    return { html: h, init: () => {
      const show = () => {
        const a = rows.find((r) => r.id === $("#elf-region-a").value), b = rows.find((r) => r.id === $("#elf-region-b").value), c = ElfRegions.compare(a, b);
        const disagreement = c.onlyA.length + c.onlyB.length;
        $("#elf-region-comparison").innerHTML = `<p>${c.overlapBytes} overlapping bytes; ${c.sharedSources.length} shared instruction starts. ` +
          (c.sharedSources.length ? (disagreement ? '<b>Adjacency disagrees at shared sources.</b>' : '<b>Adjacency agrees at shared sources.</b>') : 'No common source to compare.') + '</p>' +
          `<table><tbody><tr><th>Edges only in A at shared sources</th><td>${edgeLabels(c.onlyA)}</td></tr><tr><th>Edges only in B at shared sources</th><td>${edgeLabels(c.onlyB)}</td></tr>` +
          `<tr><th>Entry</th><td>${c.entryAgrees ? "agrees" : "differs"}</td></tr><tr><th>Declared exits</th><td>${c.sameSupport ? `only A: ${labels(c.exitsOnlyA)}; only B: ${labels(c.exitsOnlyB)}` : "Different support; exit sets describe different boundaries"}</td></tr>` +
          `<tr><th>Sources covered only by A / B</th><td>${labels(c.uncoveredSourcesA)} / ${labels(c.uncoveredSourcesB)}</td></tr></tbody></table>` +
          '<p class="muted">Data agreement is not certificate transport. A difference is a disagreement between statements, not proof that an unproved statement is false. Disjoint support is coverage difference. All computations here are browser observations.</p>';
      };
      for (const id of ["#elf-region-a", "#elf-region-b"]) $(id).addEventListener("change", show); show();
    }};
  }

  registerView({ id: "elf", title: "ELF", nav: 85, render: elfIndex });
  registerView({ id: "elf-regions", title: "ELF regions", tab: "elf", render: (arg) => elfRegions(arg) });
  registerView({ id: "elf-graph", title: "ELF graph", tab: "elf", render: (arg) => elfRegions(arg, true) });
  registerView({ id: "elf-funcs", title: "ELF functions", tab: "elf", render: (arg) => elfFuncs(arg) });
  registerView({ id: "elf-file", title: "ELF file", tab: "elf", render: (arg) => elfFile(arg) });
  registerView({ id: "elf-bytes", title: "ELF bytes", tab: "elf", render: (arg) => elfBytes(arg) });
  registerView({ id: "elf-disasm", title: "ELF disassembly (unverified)", tab: "elf", render: (arg) => elfDisasm(arg) });
})();
