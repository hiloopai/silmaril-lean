// The holds/fails/unknown coarsening of a status (as `sil project check`): UNS fails only for a
// closed (arity 0) problem; `contingent` fails; otherwise the `szs` table's verdict.
const COARSE = "CASE WHEN st.status = 'UNS' AND p.arity = 0 THEN 'fails' WHEN st.status = 'contingent' THEN 'fails' " +
  "ELSE coalesce(z.verdict, 'unknown') END";

// The attention lists of the landing page (StatusSemantics.attentionOf), in order.
const ATTENTION = [
  { key: "contrary", title: "Contrary to expectation", text: "the established statuses contradict the expected status, or a finding classifies the refutation as a genuine error" },
  { key: "open", title: "Open", text: "nothing is established yet (OPN, UNK)" },
  { key: "weaker", title: "Less information than expected", text: "something is established and consistent with the expectation, but not the expectation itself (e.g. CSA where UNS is expected)" },
  { key: "stronger", title: "More information than expected", text: "the established statuses entail the expected status and say more (e.g. TAU where SAT is expected, or anything where OPN is expected)" },
];
const EXCLUDED = {
  deprecated: { title: "Deprecated", text: "marked wrong by a deprecation record; kept for the record" },
  "expected-open": { title: "Expected to stay open", text: "an expected_open marking gives a metatheoretic reason about Lean's own theory (independence of it, or its own consistency)" },
};
// A link to the namespace browser filtered by `params` (see views/browse.js).
function browseHref(path, params) {
  const qs = new URLSearchParams(params || {}).toString();
  return "#/browse/" + encodeURIComponent(path || "") + (qs ? "?" + qs : "");
}

// The glossary of displayed codes and outcomes (also the `#/statuses` page).
function glossary(counts) {
  const S = StatusSemantics;
  const row = (c) => {
    const d = S.DISPLAY_CODES[c];
    const n = counts && counts.get(c);
    return `<dt><span class="st">${esc(c)}</span></dt><dd>${esc(d.name)}: ${esc(d.text)}` +
      `${n ? ` · <a href="${browseHref("", { status: c })}">${n} problem${n === 1 ? "" : "s"}</a>` : ""}</dd>`;
  };
  return '<div class="grid"><div><h3>Without parameters</h3><dl class="glossary">' + ["THM", "CTH"].map(row).join("") + "</dl>" +
    "<h3>With parameters</h3><dl class=\"glossary\">" + ["TAU", "UNS", "SAT", "CSA", "NOC"].map(row).join("") + "</dl>" +
    "<h3>Either</h3><dl class=\"glossary\">" + ["OPN", "UNK"].map(row).join("") + "</dl></div>" +
    "<div><h3>Compared with the expected status</h3><dl class=\"glossary\">" +
    `<dt>${statusBadge({ summary: "UNS", arity: 1, expect: "THM" })}</dt><dd>${esc(S.OUTCOMES.contrary.label)}: ${esc(S.OUTCOMES.contrary.text)}</dd>` +
    `<dt>${statusBadge({ summary: "CSA", arity: 1, expect: "UNS" })}</dt><dd>${esc(S.OUTCOMES.weaker.label)}: ${esc(S.OUTCOMES.weaker.text)}</dd>` +
    `<dt>${statusBadge({ summary: "THM", arity: 1, expect: "SAT" })}</dt><dd>${esc(S.OUTCOMES.stronger.label)}: ${esc(S.OUTCOMES.stronger.text)}</dd>` +
    `<dt>${statusBadge({ summary: "THM", arity: 1, expect: "THM" })}</dt><dd>${esc(S.OUTCOMES.match.label)} (or nothing expected): no mark</dd>` +
    "</dl><p class=\"muted\">The database stores SZS codes (THM, UNS, SAT, CSA, contingent, OPN; " +
    `<a href="${SZS_SOURCE}" target="_blank" rel="noopener noreferrer">SZS ontology</a>). The displayed code depends on whether the problem has ` +
    "parameters: stored THM is TAU for a problem with parameters; stored UNS or CSA of a problem without parameters is CTH. A badge's title lists the stored codes. " +
    "An expectation is compared by what the statuses entail, assuming an inhabited argument carrier unless THM and UNS together show it empty.</p></div></div>";
}

async function statusesPage() {
  const idx = await problemIndex();
  const counts = new Map();
  for (const e of idx.list) if (e.kind !== "group") counts.set(e.st.code, (counts.get(e.st.code) || 0) + 1);
  return "<h2>What the status codes mean</h2>" + glossary(counts);
}

const OPEN_PAGE_SIZE = 40;

// A compact table of problems: status, name, title.
async function problemRows(list, limit, existingTitles) {
  const shown = list.slice(0, limit);
  if (!shown.length) return '<p class="muted">(none)</p>';
  const titles = existingTitles || await problemTitles(shown.map((e) => e.name));
  return '<div class="tablebox"><table><thead><tr><th class="nw">status</th><th>problem</th><th>title</th></tr></thead><tbody>' +
    shown.map((e) => `<tr><td class="nw">${statusBadge(e.row)}</td><td>${link("problem", e.name)}</td><td>${esc(titles.get(e.name) || "")}</td></tr>`).join("") +
    "</tbody></table></div>" + (list.length > limit ? `<p class="muted">the first ${limit} of ${list.length}</p>` : "");
}

// Compact project facts bar from actual database rows, respecting active vs excluded problem counts.
function projectFactsBar(problemsOnly, excluded, groupsCount, artifactCount, answerCount) {
  const active = problemsOnly.filter((e) => !e.st.deprecated);
  let holds = 0, fails = 0, open = 0;
  for (const e of active) {
    if (e.row.verdict === "holds") holds++;
    else if (e.row.verdict === "fails") fails++;
    else open++;
  }
  const items = [
    ["Active problems", `${active.length}`, `${holds} holds · ${fails} fails · ${open} open`],
    ["Solutions / answers", `${answerCount}`, groupsCount ? `${groupsCount} problem group${groupsCount === 1 ? "" : "s"}` : "recorded theorems"],
    ["Artifacts", `${artifactCount}`, excluded.deprecated.length ? `${excluded.deprecated.length} deprecated excluded` : "registered blobs"],
  ];
  return `<section class="project-facts" aria-label="Project statistics"><dl class="facts-strip">` +
    items.map(([label, val, sub]) => `<div class="fact-item"><dt>${esc(label)}</dt><dd><b>${esc(val)}</b> <span class="muted">${esc(sub)}</span></dd></div>`).join("") +
    `</dl></section>`;
}

// General Silmaril Projects help + optional project-specific help when configured.
async function openHelpDialog() {
  const proj = await tq("projects", "SELECT * FROM projects WHERE origin = 'local' LIMIT 1").catch(() => []);
  const local = proj[0] || null;
  const projName = (local && local.name) || (PROJECT_META && PROJECT_META.name) || "this project";
  const projDesc = (local && local.description) || (PROJECT_META && PROJECT_META.description) || "";
  let projectSpecificHtml = "";
  if (PROJECT_META && PROJECT_META.helpDoc) {
    try {
      const r = await fetch("docs/" + PROJECT_META.helpDoc.split("/").map(encodeURIComponent).join("/"));
      if (r.ok) {
        const md = await r.text();
        projectSpecificHtml = `<section class="help-project-section" data-project-help="doc"><h3>Project help (${esc(projName)})</h3>` +
          `<div class="doc-body">${ProjectDocs.renderMarkdown(md, PROJECT_META.helpDoc, {
            sourceRepo: SOURCE && SOURCE.repo,
            sourceRev: SOURCE && SOURCE.rev,
            repoFile: typeof repoFile === "function" ? repoFile : null,
          })}</div></section>`;
      }
    } catch { /* fall back gracefully */ }
  } else if (PROJECT_META && PROJECT_META.help) {
    projectSpecificHtml = `<section class="help-project-section" data-project-help="inline"><h3>Project help (${esc(projName)})</h3>` +
      `<div class="doc-body">${ProjectDocs.renderMarkdown(PROJECT_META.help, "README.md", {
        sourceRepo: SOURCE && SOURCE.repo,
        sourceRev: SOURCE && SOURCE.rev,
        repoFile: typeof repoFile === "function" ? repoFile : null,
      })}</div></section>`;
  }

  const docsIndex = PROJECT_META && PROJECT_META.docsIndex;
  const docsLink = docsIndex
    ? `<li><a href="${esc(ProjectDocs.docsRouteHref(docsIndex, ""))}" class="help-nav-link">Project documentation</a>: read the rendered project guides and diagrams inline.</li>`
    : "";

  const body = (projDesc ? `<p class="help-proj-desc"><b>${esc(projName)}:</b> ${esc(projDesc)}</p>` : "") +
    projectSpecificHtml +
    `<section class="help-general-section" data-general-help="1"><h3>Exploring a Silmaril project</h3>` +
    `<p>A Silmaril project records content-addressed <b>artifacts</b>, typed <b>values</b> parsed under <b>formats</b>, formal <b>problems</b> and their <b>answers</b> (Lean theorems), organized in a problem DAG.</p>` +
    `<ul>` +
    docsLink +
    `<li><b>Summary &amp; Needs attention:</b> active open problems and any status that differs from its expected outcome. Search across all active open problems by name or title and step through pages.</li>` +
    `<li><b>Status badges:</b> closed problems (no parameters) read <span class="st">THM</span> (proved), <span class="st">CTH</span> (disproved) or <span class="st">OPN</span> (open). Parameterized predicates read <span class="st">TAU</span>, <span class="st">UNS</span>, <span class="st">SAT</span>, <span class="st">CSA</span> or <span class="st">NOC</span>. See <a href="#/statuses" class="help-nav-link">What the codes mean</a>.</li>` +
    `<li><b>Browse &amp; Graph:</b> walk dotted problem namespaces in <a href="#/browse" class="help-nav-link">Browse</a>, or inspect the proof DAG and stacked leaves in <a href="#/graph" class="help-nav-link">Graph</a>.</li>` +
    `<li><b>Database &amp; SQL:</b> the header button shows whether the SQLite database is read lazily via HTTP Range requests or loaded whole, and lets you open another database file or run queries in <a href="#/sql" class="help-nav-link">SQL</a>.</li>` +
    `</ul></section>`;
  const d = dialog({ title: "Silmaril Projects Help", body });
  d.el.classList.add("dlg-wide");
  for (const a of d.el.querySelectorAll("a[href^='#/']")) {
    a.addEventListener("click", () => d.close());
  }
}

// Every query here is an aggregate, has a LIMIT, or is the shared problem index.
async function summary() {
  const proj = await tq("projects", "SELECT * FROM projects ORDER BY origin DESC, name LIMIT 50");
  const local = proj.find((p) => p.origin === "local");
  if (local?.root) await resolve([local], ["root"], HINTS, false);
  const isSilmarilRepo = SOURCE?.repo.toLowerCase() === "https://github.com/hiloopai/silmaril-lean";
  const ghDocs = isSilmarilRepo ? repoFile("docs/projects/README.md") : null;
  const packagedDocs = PROJECT_META && PROJECT_META.docsIndex ? PROJECT_META.docsIndex : null;
  const description = (local && local.description && local.description.trim())
    || (PROJECT_META && PROJECT_META.description && PROJECT_META.description.trim())
    || "";
  const root = local?.root ? `<p class="index-root">Project root ${link("problem", local.root)} ${verdictBadge(local.root)}</p>` : "";
  let docsHtml = "";
  if (packagedDocs) {
    const inlineHref = ProjectDocs.docsRouteHref(packagedDocs, "");
    docsHtml = `<p class="index-docs"><a href="${esc(inlineHref)}">Project documentation</a>` +
      (ghDocs ? ` <span class="muted">· <a href="${esc(ghDocs.blob)}" target="_blank" rel="noopener noreferrer">on GitHub</a></span>` : "") +
      `</p>`;
  } else if (ghDocs) {
    docsHtml = `<p class="index-docs"><a href="${esc(ghDocs.blob)}">Project documentation</a></p>`;
  }
  let h = `<section class="index-intro"><div class="index-intro-head"><h2>${esc(local?.name || (PROJECT_META && PROJECT_META.name) || "Project index")}</h2>` +
    `<button type="button" class="help-btn summary-help-btn" data-open-help="1" aria-haspopup="dialog">Help</button></div>` +
    (description ? `<p class="project-description">${esc(description)}</p>` : "") +
    docsHtml +
    root + "</section>";
  const idx = tables.has("problems") ? await problemIndex() : { list: [] };
  if (idx.tooLarge) h += `<p class="muted">${idx.tooLarge} problems: too many to classify here; use the problem list and SQL.</p>`;
  const problemsOnly = idx.list.filter((e) => e.kind !== "group");
  const groupsCount = idx.list.length - problemsOnly.length;
  const by = Object.fromEntries(ATTENTION.map((a) => [a.key, []]));
  const excluded = { deprecated: [], "expected-open": [] };
  for (const e of problemsOnly) {
    if (e.st.attention.list) by[e.st.attention.list].push(e);
    else if (e.st.attention.excluded) excluded[e.st.attention.excluded].push(e);
  }
  const [artifactRows, answerRows] = await Promise.all([
    tq("artifacts", "SELECT count(*) AS n FROM artifacts"),
    tq("answers", "SELECT count(*) AS n FROM answers"),
  ]);
  const artifactCount = (artifactRows[0] && artifactRows[0].n) || 0;
  const answerCount = (answerRows[0] && answerRows[0].n) || 0;
  if (problemsOnly.length || artifactCount || answerCount) {
    h += projectFactsBar(problemsOnly, excluded, groupsCount, artifactCount, answerCount);
  }
  h += explorerIndex();
  // within a list: closed problems first (they are single questions), then by name
  for (const k of Object.keys(by)) by[k].sort((a, b) => (a.arity === 0 ? 0 : 1) - (b.arity === 0 ? 0 : 1) || a.name.localeCompare(b.name));
  const openTitles = by.open.length ? await problemTitles(by.open.map((e) => e.name)) : new Map();
  if (problemsOnly.length) {
    const activeProblemsCount = problemsOnly.length - excluded.deprecated.length;
    h += `<h2 id="attention">Needs attention</h2><p class="muted">${activeProblemsCount} active problem${activeProblemsCount === 1 ? "" : "s"}. ` +
      `Open problems and problems whose statuses differ from what was expected. <a href="#/statuses">What the codes mean</a>.</p><div class="att">` +
      ATTENTION.map((a) => `<a class="card k-${a.key}" href="${browseHref("", { attention: a.key })}" title="${esc(a.text)}"><b>${by[a.key].length}</b>${esc(a.title)}</a>`).join("") +
      (excluded["expected-open"].length ? `<a class="card k-excluded" href="${browseHref("", { excluded: "expected-open" })}" title="${esc(EXCLUDED["expected-open"].text)}"><b>${excluded["expected-open"].length}</b>${esc(EXCLUDED["expected-open"].title)}</a>` : "") +
      "</div>";
    for (const a of ATTENTION) {
      if (!by[a.key].length) continue;
      const closed = by[a.key].filter((e) => e.arity === 0).length;
      if (a.key === "open") {
        h += `<h3 id="att-open">${esc(a.title)} (${by.open.length}: ${closed} without parameters, ${by.open.length - closed} with)</h3>` +
          `<p class="muted">${esc(a.text)}. <a href="${browseHref("", { attention: "open" })}">browse by namespace</a></p>` +
          `<div class="controls open-search-controls" role="search" aria-label="Search active open problems">` +
          `<label>Search open problems <input type="search" id="open-search" placeholder="filter by problem name or title…" size="36" autocomplete="off"></label>` +
          `<button type="button" id="open-prev" disabled>◀ previous</button>` +
          `<button type="button" id="open-next"${by.open.length <= OPEN_PAGE_SIZE ? " disabled" : ""}>next ▶</button>` +
          `<span id="open-count" class="muted" aria-live="polite">showing ${by.open.length ? 1 : 0}–${Math.min(OPEN_PAGE_SIZE, by.open.length)} of ${by.open.length} open problems</span>` +
          `</div>` +
          `<div id="open-results">${await problemRows(by.open, OPEN_PAGE_SIZE, openTitles)}</div>`;
      } else {
        h += `<h3 id="att-${a.key}">${esc(a.title)} (${by[a.key].length})</h3>` +
          `<p class="muted">${esc(a.text)}. <a href="${browseHref("", { attention: a.key })}">browse by namespace</a></p>` + await problemRows(by[a.key], 100);
      }
    }
    const ex = Object.entries(excluded).filter(([, l]) => l.length);
    if (ex.length) {
      h += `<div class="excluded-routes"><p class="muted">Excluded from active lists: ` +
        ex.map(([k, l]) => `<a class="excluded-link" data-excluded="${esc(k)}" href="${browseHref("", { excluded: k })}"><b>${l.length}</b> ${esc(EXCLUDED[k].title.toLowerCase())}</a> — ${esc(EXCLUDED[k].text)}`).join(" · ") +
        `</p></div>`;
    }
  }
  // the counts read whole tables (edges, statuses): only when asked for
  h += '<details id="sumdetails"><summary><b>Counts, verdicts, groups and metadata</b></summary><div id="sumdetailsbody"><p class="muted">reading…</p></div></details>';
  const init = () => {
    for (const btn of document.querySelectorAll("[data-open-help]")) {
      btn.addEventListener("click", () => openHelpDialog());
    }
    const searchInput = $("#open-search");
    if (searchInput) {
      let off = 0;
      let filtered = by.open;
      const prevBtn = $("#open-prev"), nextBtn = $("#open-next"), countEl = $("#open-count"), resEl = $("#open-results");
      const renderOpenPage = () => {
        const q = searchInput.value.trim().toLowerCase();
        filtered = !q ? by.open : by.open.filter((e) => e.name.toLowerCase().includes(q) || (openTitles.get(e.name) || "").toLowerCase().includes(q));
        if (off >= filtered.length) off = Math.max(0, Math.floor((filtered.length - 1) / OPEN_PAGE_SIZE) * OPEN_PAGE_SIZE);
        const page = filtered.slice(off, off + OPEN_PAGE_SIZE);
        if (!page.length) {
          resEl.innerHTML = '<p class="muted">(no matching open problems)</p>';
          countEl.textContent = `0 of ${by.open.length} open problems match`;
        } else {
          resEl.innerHTML = '<div class="tablebox"><table><thead><tr><th class="nw">status</th><th>problem</th><th>title</th></tr></thead><tbody>' +
            page.map((e) => `<tr><td class="nw">${statusBadge(e.row)}</td><td>${link("problem", e.name)}</td><td>${esc(openTitles.get(e.name) || "")}</td></tr>`).join("") +
            "</tbody></table></div>";
          countEl.textContent = q
            ? `showing ${off + 1}–${off + page.length} of ${filtered.length} matching (${by.open.length} total open)`
            : `showing ${off + 1}–${off + page.length} of ${by.open.length} open problems`;
        }
        prevBtn.disabled = off === 0;
        nextBtn.disabled = off + OPEN_PAGE_SIZE >= filtered.length;
      };
      searchInput.addEventListener("input", () => { off = 0; renderOpenPage(); });
      prevBtn.addEventListener("click", () => { off = Math.max(0, off - OPEN_PAGE_SIZE); renderOpenPage(); });
      nextBtn.addEventListener("click", () => { if (off + OPEN_PAGE_SIZE < filtered.length) { off += OPEN_PAGE_SIZE; renderOpenPage(); } });
    }
    const d = $("#sumdetails");
    if (!d) return;
    d.addEventListener("toggle", async () => {
      if (!d.open || d.dataset.loaded) return;
      d.dataset.loaded = "1";
      try { $("#sumdetailsbody").innerHTML = await summaryDetails(local, proj, problemsOnly); }
      catch (e) { if (!(e instanceof Superseded)) $("#sumdetailsbody").innerHTML = `<p class="err">${esc(e.message || e)}</p>`; }
      updateStats();
    });
  };
  return { html: h, init };
}
async function summaryDetails(local, proj, problemsOnly) {
  let h = "";
  h += local ? await dl(local) : '<p class="muted">no local project row</p>';
  const counts = [
    ...await tq("objects", "SELECT kind, count(*) AS n FROM objects GROUP BY kind"),
    ...await tq("artifacts", "SELECT 'artifact' AS kind, count(*) AS n FROM artifacts"),
    ...await tq("edges", "SELECT 'edge:' || kind AS kind, count(*) AS n FROM edges GROUP BY kind"),
    ...await tq("answers", "SELECT 'answer' AS kind, count(*) AS n FROM answers")];
  h += '<div class="grid"><div><h2>Objects by kind</h2>' + await table(counts) + "</div>";
  const codes = new Map();
  for (const e of problemsOnly) codes.set(e.st.code, (codes.get(e.st.code) || 0) + 1);
  h += "<div><h2>Problems by status</h2>" + await table(StatusSemantics.DISPLAY_ORDER.filter((c) => codes.get(c)).map((c) =>
    ({ status: c, meaning: StatusSemantics.DISPLAY_CODES[c].text, problems: codes.get(c) })), ["status", "meaning", "problems"],
    { render: { status: (r) => `<a href="${browseHref("", { status: r.status })}"><span class="st">${esc(r.status)}</span></a>` } }) + "</div>";
  if (tables.has("statuses")) {
    h += "<div><h2>Stored statuses by SZS code</h2>" + await table(await q(
      `SELECT st.status AS code, z.name, ${COARSE} AS verdict, count(*) AS statuses, count(DISTINCT st.problem) AS problems ` +
      "FROM statuses st LEFT JOIN szs z ON z.code = st.status LEFT JOIN problems p ON p.name = st.problem GROUP BY 1, 3 ORDER BY 3, 1 LIMIT 200")) +
      '<p class="muted">As stored, before the reading by arity. holds = THM; fails = CSA, contingent, UNS of a closed problem; unknown = the rest.</p></div>';
  }
  h += "</div>";
  if (tables.has("objects") && tables.has("edges")) {
    const ng = (await q("SELECT count(*) AS n FROM objects WHERE kind = 'group'"))[0].n;
    if (ng) {
      const gs = await q("SELECT name AS group_name FROM objects WHERE kind = 'group' ORDER BY name LIMIT 100");
      h += `<h2>Groups (${ng})</h2>` + await table(gs, null, { hints: { group_name: "problem" } }) +
        (ng > 100 ? '<p class="muted">the first 100 groups</p>' : "");
    }
  }
  h += "<h2>Meta</h2>" + await table(await tq("meta", "SELECT * FROM meta LIMIT 100"));
  if (proj.length > 1) h += "<h2>Projects</h2>" + await table(proj, ["name", "origin", "version", "root", "url", "rev"]);
  return h;
}

registerView({ id: "summary", title: "Summary", nav: 10, render: summary });
registerView({ id: "statuses", title: "Statuses", tab: "summary", render: statusesPage });
