// ---------- WAST: the commands of the pinned spec test suite slice, per command ----------
// Reads `wast/report.json` and, if present, `wast/oracle.json` next to the page, as written by
// tools/wasm-wast/gen.py (`emit`, `oracle`) and copied by its `site DIR` command
// (docs/projects/wasm-wast.md). The rows' Lean status comes from the database: each proved
// command is a problem `silmaril.wasm_wast.<file>.l<line>` with an `@[answers … thm]` theorem.
// The pure part (`WastModel`) has no DOM and is loaded by the Node test
// tests/explore/wast_view.test.mjs.
const WastModel = (() => {
  const STATUS_ORDER = ["proved", "mismatch", "undetermined", "unsupported", "action"];
  const STATUS_TEXT = {
    proved: "kernel-checked theorem",
    mismatch: "the interpreter disagrees with the expectation",
    undetermined: "not decided (see the reason)",
    unsupported: "outside the fragment (see the reason)",
    action: "an action of the script (no claim)",
  };
  const STRENGTH = {
    "silmaril.shapes.wasm.wast.returns_only": "returns these values at every host-free normal form; no host-free run diverges (theorem ReturnsOnly.always)",
    "silmaril.shapes.wasm.wast.traps_only": "traps at every host-free normal form; no host-free run diverges (theorem TrapsOnly.always)",
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
    for (const c of report.commands) {
      if (c.status === "proved") proved++;
      const o = ox.get(c.id);
      if (!o) continue;
      oracleRun++;
      if (o.oracle === "pass" && c.status === "proved") agreeProved++;
      if (o.oracle !== "pass") disagree++;
    }
    const reasons = Object.entries(byReason).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
    return { total: report.commands.length, byStatus, byFile, reasons, proved, oracleRun, agreeProved, disagree,
      oracleLoaded: !!oracle };
  }
  // The table rows, filtered by status and file ("" for every one).
  function rows(report, oracle, { status = "", file = "" } = {}) {
    const ox = oracleIndex(oracle);
    return report.commands.filter((c) => (!status || c.status === status) && (!file || c.file === file)).map((c) => {
      const o = ox.get(c.id);
      return {
        id: c.id, file: c.file, line: c.line, type: c.type, status: c.status,
        input: c.invoke == null ? "" : `${c.invoke}(${(c.args || []).join(", ")})`,
        expected: (c.expected || []).join(", "),
        observed: c.observed || "",
        strength: c.shape ? STRENGTH[c.shape] || c.shape : "",
        problem: c.problem || null, theorem: c.theorem || null, reason: c.reason || "",
        oracle: o ? o.oracle : null,
      };
    });
  }
  return Object.freeze({ STATUS_ORDER, STATUS_TEXT, STRENGTH, summarize, rows, oracleIndex });
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
    h += "<p>Assumptions of every theorem:</p><ul>" + report.assumptions.map((a) => `<li>${esc(a)}</li>`).join("") + "</ul>";
    h += `<p><b>${s.total}</b> commands: ` + WastModel.STATUS_ORDER.filter((k) => s.byStatus[k]).map((k) =>
      `<a href="#/wast/${encodeURIComponent(k)}" title="${esc(WastModel.STATUS_TEXT[k])}">${esc(k)} ${s.byStatus[k]}</a>`).join(" · ") +
      ` · <a href="#/wast">all</a>. In this database: ${[...db.values()].filter((r) => r.status === "THM").length} rows answered THM ` +
      `(of ${s.proved} proved in the report).</p>`;
    h += s.oracleLoaded
      ? `<p>Oracle: ${esc(oracle.oracle.tool)} ${esc(oracle.oracle.version)} (SHA-256 <code>${esc(oracle.oracle.sha256)}</code>), ` +
        `run outside CI: ${s.oracleRun} commands run, ${s.agreeProved} of ${s.proved} kernel-proved commands agree, ${s.disagree} disagree.</p>`
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
      ["claim", (r) => r.problem ? `${link("problem", r.problem, r.problem)}<br><span class="muted">${esc(r.strength)}</span>` : ""],
      ["status", (r) => {
        const d = r.problem && db.get(r.problem);
        return `${esc(r.status)}${d ? " · " + esc(d.status || "no answer") + (d.tier ? " (" + esc(d.tier) + ")" : "") :
          r.problem ? ' · <span class="muted">not in this database</span>' : ""}`;
      }],
      ["reason", (r) => esc(r.reason)],
      ["oracle", (r) => esc(r.oracle || "")],
    ]);
    if (rows.length > 2000) h += `<p class="muted">first 2000 of ${rows.length}</p>`;
    return h;
  }
  registerView({ id: "wast", title: "WAST", nav: 82, render: wastPage });
}
