// ---------- WAST: the commands of the pinned spec test suite slice, per command ----------
// Reads `wast/report.json` and, if present, `wast/oracle.json` next to the page, as written by
// tools/wasm-wast/gen.py (`emit`, `oracle`) and copied by its `site DIR` command
// (docs/projects/wasm-wast.md). The rows' Lean status comes from the database: each proved
// command is a problem `silmaril.wasm_wast.<file>.l<line>` with an `@[answers … thm]` theorem.
// The pure part (`WastModel`) has no DOM and is loaded by the Node test
// tests/explore/wast_view.test.mjs.
const WastModel = (() => {
  const STATUS_ORDER = ["proved", "mismatch", "undetermined", "unsupported", "context", "action"];
  const STATUS_TEXT = {
    proved: "kernel-checked theorem",
    mismatch: "the interpreter disagrees with the expectation",
    undetermined: "not decided (see the reason)",
    unsupported: "outside the fragment (see the reason)",
    action: "an action of the script (no claim)",
    context: "a register or bare action of a linked script: part of the context of later rows (no claim)",
  };
  const STRENGTH = {
    "silmaril.shapes.wasm.wast.returns_only": "returns these values at every host-free normal form; no host-free run diverges (theorem ReturnsOnly.always)",
    "silmaril.shapes.wasm.wast.traps_only": "traps at every host-free normal form; no host-free run diverges (theorem TrapsOnly.always)",
    "silmaril.shapes.wasm.wast.returns_allowed_all": "under Profile.spec (the specification's NaN result sets), every host-free normal form " +
      "returns values in the allowed set (nan:canonical, nan:arithmetic, or exact bits), and some run reaches one",
    "silmaril.shapes.wasm.wast.returns_allowed_exists": "under Profile.spec, some host-free run returns values in the allowed set " +
      "(existence only: says nothing about the other runs)",
    "silmaril.shapes.wasm.wast.traps_all": "under Profile.spec, every host-free normal form is a trap, and some run reaches one",
    "silmaril.shapes.wasm.wast.terminates_all": "under Profile.spec, no host-free run is infinite, and every finite run extends to a normal form",
    "silmaril.shapes.wasm.wast.validator_rejects": "silmaril-lean's decoder reads the bytes and silmaril-lean's validator rejects the module; " +
      "with validate?_complete, no module the bytes encode is valid in silmaril-lean's ModuleOk (ValidatorRejects.not_valid). " +
      "Not a claim that the module is invalid in the specification",
    "silmaril.shapes.wasm.wast.decoder_rejects": "silmaril-lean's decoder rejects the bytes; the decoder is sound, not complete, " +
      "so this is not a claim that the bytes are malformed",
    "silmaril.shapes.wasm.wast.link.returns_only": "after the linked script prefix (every earlier module, register and action of the file, " +
      "from the closed spectest module), returns these values at every host-free normal form; no host-free run diverges (ReturnsOnly.always)",
    "silmaril.shapes.wasm.wast.link.traps_only": "after the linked script prefix, traps at every host-free normal form; " +
      "no host-free run diverges (TrapsOnly.always)",
    "silmaril.shapes.wasm.wast.link.unlinkable": "after the linked script prefix, the module is valid and its imports do not resolve by name " +
      "to exports of registered modules, or resolve to addresses without the import types (ExternAddrOk, silmaril-lean's transcription " +
      "of Externaddr_ok); so no Instantiate derivation exists for them (Unlinkable.not_instantiate)",
    "silmaril.shapes.wasm.wast.link.uninstantiable": "after the linked script prefix, the module links and instantiateOnce? allocates it, " +
      "and its start function traps at every host-free normal form (segment traps have no shape)",
  };
  // How strong a proved row's claim is (the report's `strength`).
  const CLAIM = {
    only: "semantic: Core reduction",
    all: "semantic: Core reduction under Profile.spec, every normal form",
    exists: "semantic: Core reduction under Profile.spec, some run only",
    tool: "tool-level rejection",
    link: "semantic: linking (name resolution and the ExternAddrOk transcription)",
  };
  // The kinds of claim of a row (the report's `claims[].kind`).
  const KIND = {
    only: "every normal form (profile neverFail; termination by Reaches.always)",
    link: "every context the prefix reaches (one, at profile neverFail)",
    all: "every normal form",
    exists: "some run (existence)",
    terminates: "every run terminates",
  };
  // The oracle result of each command, by id.
  function oracleIndex(oracle) {
    const m = new Map();
    for (const r of (oracle && oracle.results) || []) m.set(r.id, r);
    return m;
  }
  // Counts by status and by reason, and the oracle's agreement.
  function summarize(report, oracle) {
    const byStatus = {}, byReason = {}, byFile = {};
    for (const c of report.commands) {
      byStatus[c.status] = (byStatus[c.status] || 0) + 1;
      const f = (byFile[c.file] = byFile[c.file] || { total: 0 });
      f.total++; f[c.status] = (f[c.status] || 0) + 1;
      if (c.status === "unsupported" || c.status === "undetermined" || c.status === "mismatch") {
        const k = `${c.status}: ${c.reason || "?"}`;
        byReason[k] = (byReason[k] || 0) + 1;
      }
    }
    const ox = oracleIndex(oracle);
    let oracleRun = 0, agreeProved = 0, proved = 0, disagree = 0;
    const byClaim = {};
    for (const c of report.commands) {
      if (c.status === "proved") {
        proved++;
        const k = CLAIM[c.strength] || c.strength || "?";
        byClaim[k] = (byClaim[k] || 0) + 1;
      }
      const o = ox.get(c.id);
      if (!o) continue;
      oracleRun++;
      if (o.oracle === "pass" && c.status === "proved") agreeProved++;
      if (o.oracle !== "pass") disagree++;
    }
    const reasons = Object.entries(byReason).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
    return { total: report.commands.length, byStatus, byFile, reasons, proved, byClaim, oracleRun, agreeProved, disagree,
      oracleLoaded: !!oracle };
  }
  // The script context of a linked row, as one line.
  function contextText(x) {
    if (!x) return "";
    const list = (l) => (l && l.length ? l.join(", ") : "none");
    return `registered: ${list(x.registered)}; named: ${list((x.named || []).map((n) => "$" + n))}; ` +
      `current: ${x.current || "none"}` + (x.current ? ` (imports: ${list(x.current_imports)})` : "") +
      (x.module_imports ? `; this module imports: ${list(x.module_imports)}` : "") + (x.host ? `; host: ${x.host}` : "");
  }
  // The table rows, filtered by status and file ("" for every one).
  function rows(report, oracle, { status = "", file = "" } = {}) {
    const ox = oracleIndex(oracle);
    return report.commands.filter((c) => (!status || c.status === status) && (!file || c.file === file)).map((c) => {
      const o = ox.get(c.id);
      return {
        id: c.id, file: c.file, line: c.line, type: c.type, status: c.status,
        input: (c.on ? c.on + "." : "") + (c.invoke != null ? `${c.invoke}(${(c.args || []).join(", ")})`
          : c.get != null ? `get ${c.get}`
          : c.register ? `register "${c.register.as}" ${c.register.module}`
          : c.wasm_sha256 ? `module (${c.module_type || "binary"}), binary SHA-256 ${c.wasm_sha256.slice(0, 12)}…` : ""),
        expected: (c.expected || []).join(", "),
        observed: c.observed || "",
        strength: c.shape ? STRENGTH[c.shape] || c.shape : "",
        // "semantic: Core reduction" (assert_return, assert_trap) or "tool-level rejection"
        // (assert_invalid, assert_malformed: claims about silmaril-lean's decoder and validator).
        claim: c.status === "proved" ? CLAIM[c.strength] || c.strength || "" : "",
        problem: c.problem || null, theorem: c.theorem || null, reason: c.reason || "",
        // Each claim of a proved row: its kind (`only`, `all`, `exists`, `terminates`), shape and
        // problem. A row under Profile.spec has two: its expectation at every normal form, and
        // termination of every run.
        claims: (c.claims || []).map((x) => ({ kind: x.kind, kindText: KIND[x.kind] || x.kind, shape: x.shape, problem: x.problem })),
        // The profile of the claims and the allowed set (the expectation's patterns).
        profile: c.profile || "", allowed: (c.allowed || []).join(", "),
        // The kernel checker of a proved row: `scriptK` (ByteArray stores) or `scriptKM` (KMem
        // stores, for modules with data segments); the claim is the same.
        checker: c.checker || "",
        // A row of a linked script: the context its claim is relative to (registered names, named
        // modules, the current module and its imports, the module's own imports for a module
        // assertion) and the host model (the closed spectest module).
        linked: c.script === "linked",
        context: contextText(c.context),
        host: c.host || "",
        oracle: o ? o.oracle : null,
      };
    });
  }
  return Object.freeze({ STATUS_ORDER, STATUS_TEXT, STRENGTH, CLAIM, KIND, summarize, rows, oracleIndex, contextText });
})();
if (typeof module !== "undefined" && module.exports) module.exports = WastModel;

if (typeof registerView === "function") {
  const wastCache = new Map();
  const wastJson = async (rel, optional) => {
    if (!wastCache.has(rel)) wastCache.set(rel, fetch("wast/" + rel).then((r) => {
      if (!r.ok) { if (optional && r.status === 404) return null; throw new Error(`wast/${rel}: HTTP ${r.status}`); }
      return r.json();
    }));
    try { return await wastCache.get(rel); } catch (e) { wastCache.delete(rel); if (optional) return null; throw e; }
  };
  const wastMissing = (e) => `<p class="err">The WAST report is not available here (${esc(e.message || e)}). ` +
    "It is written by <code>python3 -I tools/wasm-wast/gen.py emit</code> and copied next to the page by " +
    "<code>gen.py site DIR</code> (docs/projects/wasm-wast.md).</p>";
  const tbl = (rows, cols) => '<div class="tablebox"><table><thead><tr>' + cols.map(([c]) => `<th>${esc(c)}</th>`).join("") +
    "</tr></thead><tbody>" + rows.map((r) => "<tr>" + cols.map(([, f]) => `<td>${f(r)}</td>`).join("") + "</tr>").join("") +
    "</tbody></table></div>";
  async function wastPage(arg, ctx) {
    let report, oracle;
    try { [report, oracle] = await Promise.all([wastJson("report.json"), wastJson("oracle.json", true)]); }
    catch (e) { return wastMissing(e); }
    const s = WastModel.summarize(report, oracle);
    // The Lean side: which rows the loaded database has, with their answers.
    const db = new Map();
    if (tables.has("answers")) for (const r of await ctx.tq("problems", "SELECT p.name AS name, a.status AS status, a.decl AS decl, a.tier AS tier " +
      "FROM problems p LEFT JOIN answers a ON a.problem = p.name WHERE p.name LIKE 'silmaril.wasm_wast.%'")) db.set(r.name, r);
    const [fs, ff] = (arg || "").split("|");
    let h = "<h2>WAST: the spec test suite, command by command</h2>";
    h += `<p>WebAssembly/spec <code>${esc((report.spec.rev || "").slice(0, 12))}</code> (archive SHA-256 <code>${esc(report.spec.archive_sha256 || "")}</code>), ` +
      `converted by ${esc(report.converter.tool)} ${esc(report.converter.version)}. Profile: ${esc(report.profile)}.</p>`;
    h += "<p>Assumptions of the theorems (each says which rows it concerns):</p><ul>" + report.assumptions.map((a) => `<li>${esc(a)}</li>`).join("") + "</ul>";
    h += `<p><b>${s.total}</b> commands: ` + WastModel.STATUS_ORDER.filter((k) => s.byStatus[k]).map((k) =>
      `<a href="#/wast/${encodeURIComponent(k)}" title="${esc(WastModel.STATUS_TEXT[k])}">${esc(k)} ${s.byStatus[k]}</a>`).join(" · ") +
      ` · <a href="#/wast">all</a>. Proved, by claim strength: ` +
      Object.entries(s.byClaim).map(([k, v]) => `${esc(k)} ${v}`).join(" · ") + `. In this database: ${[...db.values()].filter((r) => r.status === "THM").length} rows answered THM ` +
      `(of ${s.proved} proved in the report).</p>`;
    h += s.oracleLoaded
      ? `<p>Oracle: ${esc(oracle.oracle.tool)} ${esc(oracle.oracle.version)} (SHA-256 <code>${esc(oracle.oracle.sha256)}</code>), ` +
        `re-run in CI (the WAST oracle job) when its inputs change and nightly: ${s.oracleRun} commands run, ${s.agreeProved} of ${s.proved} kernel-proved commands agree, ${s.disagree} disagree.</p>`
      : '<p class="muted">No oracle results (<code>wast/oracle.json</code>) next to the page.</p>';
    h += "<h3>Reasons</h3>" + tbl(s.reasons, [["reason", (r) => esc(r[0])], ["commands", (r) => String(r[1])]]);
    h += "<h3>Files</h3>" + tbl(Object.entries(s.byFile), [["file", ([f]) => `<a href="#/wast/|${encodeURIComponent(f)}">${esc(f)}.wast</a>`],
      ...WastModel.STATUS_ORDER.map((k) => [k, ([, c]) => String(c[k] || 0)]), ["total", ([, c]) => String(c.total)]]);
    const rows = WastModel.rows(report, oracle, { status: fs || "", file: ff || "" });
    h += `<h3>Commands${fs ? " (" + esc(fs) + ")" : ""}${ff ? " in " + esc(ff) + ".wast" : ""}: ${rows.length}</h3>`;
    h += tbl(rows.slice(0, 2000), [
      ["command", (r) => `<code>${esc(r.id)}</code> ${esc(r.type)}`],
      ["input", (r) => `<code>${esc(r.input)}</code>`],
      ["expected", (r) => `<code>${esc(r.expected)}</code>`],
      ["observed", (r) => `<code>${esc(r.observed)}</code>`],
      ["claim", (r) => !r.problem ? "" : r.claims.length
        ? `<b>${esc(r.claim)}</b>${r.profile ? ` <span class="muted">(${esc(r.profile)})</span>` : ""}` +
          (r.allowed ? `<br>allowed: <code>${esc(r.allowed)}</code>` : "") +
          r.claims.map((x) => `<br>${esc(x.kindText)}: ${link("problem", x.problem, x.problem)}<br>` +
            `<span class="muted">${esc(WastModel.STRENGTH[x.shape] || x.shape)}</span>`).join("")
        : `${link("problem", r.problem, r.problem)}<br><b>${esc(r.claim)}</b>: <span class="muted">${esc(r.strength)}</span>`],
      ["status", (r) => {
        const d = r.problem && db.get(r.problem);
        return `${esc(r.status)}${r.checker ? ` <span class="muted">(${esc(r.checker)})</span>` : ""}${d ? " · " + esc(d.status || "no answer") + (d.tier ? " (" + esc(d.tier) + ")" : "") :
          r.problem ? ' · <span class="muted">not in this database</span>' : ""}`;
      }],
      ["context", (r) => r.context ? `<span class="muted">${esc(r.context)}</span>` : ""],
      ["reason", (r) => esc(r.reason)],
      ["oracle", (r) => esc(r.oracle || "")],
    ]);
    if (rows.length > 2000) h += `<p class="muted">first 2000 of ${rows.length}</p>`;
    return h;
  }
  registerView({ id: "wast", title: "WAST", nav: 82, render: wastPage });
}
