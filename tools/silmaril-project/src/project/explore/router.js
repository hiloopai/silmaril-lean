// ---------- views and routing ----------
// A view is one route, `#/<id>/<arg>`. Views register themselves (see `registerView`); the
// navigation is built from the registered views that have a `nav` position. A view's
// `render(arg, ctx)` returns its HTML, or `{ html, init, dispose }` when it wires up controls
// after rendering (`init`, awaited) or holds resources to release when the route changes
// (`dispose`), or a promise of either.
//
// `ctx` belongs to one rendering of one route over one database:
//   ctx.arg            the decoded rest of the route (`""` for none)
//   ctx.alive()        whether this rendering is still current (same route, same database)
//   ctx.q(sql, params) rows as objects; ctx.tq(table, sql, params) [] when `table` is missing;
//   ctx.first(n, sql, params) the first n rows and whether there are more;
//   ctx.exec(sql)      sql.js's [{columns, values}]
//   ctx.onDispose(fn)  run fn when the route changes or another database is opened
// Every query of a superseded rendering rejects with `Superseded` (ignored by the router), so a
// slow query of an old route or an old database never writes into the current page.
class Superseded extends Error { constructor() { super("superseded"); this.name = "Superseded"; } }
let routeTok = 0, disposers = [];
// A promise that rejects with `Superseded` once the route or the database has changed.
function guarded(tok, db, p) {
  const live = () => tok === routeTok && db === be;
  return Promise.resolve(p).then((v) => { if (!live()) throw new Superseded(); return v; },
    (e) => { throw live() ? e : new Superseded(); });
}
function q(sql, params) { return guarded(routeTok, be, be.query(sql, params || [])); }
function tq(t, sql, params) { return tables.has(t) ? q(sql, params) : Promise.resolve([]); }
function dbExec(sql) { return guarded(routeTok, be, be.exec(sql)); }
function routeCtx(tok, db, arg) {
  return Object.freeze({ arg, alive: () => tok === routeTok && db === be,
    q: (sql, params) => guarded(tok, db, db.query(sql, params || [])),
    tq: (t, sql, params) => tables.has(t) ? guarded(tok, db, db.query(sql, params || [])) : Promise.resolve([]),
    first: async (n, sql, params) => { const rows = await guarded(tok, db, db.query(sql + " LIMIT " + (n + 1), params || [])); return { rows: rows.slice(0, n), more: rows.length > n }; },
    exec: (sql) => guarded(tok, db, db.exec(sql)),
    onDispose: (fn) => { if (tok === routeTok) disposers.push(fn); } });
}
function disposeRoute() {
  const ds = disposers; disposers = [];
  for (const d of ds) try { d(); } catch (e) { /* a view's cleanup must not stop the next one */ }
}
async function route() {
  if (!be) return;
  disposeRoute();
  const tok = ++routeTok;
  const parts = location.hash.replace(/^#\/?/, "").split("/");
  const corpusOnly = corpusOnlyNavigation();
  const requested = VIEWS.get(parts[0]);
  const view = corpusOnly ? (requested && (requested.id.startsWith("corpus") || requested.id === "sql") ? requested : VIEWS.get("corpus"))
    : requested || VIEWS.get("summary");
  for (const a of document.querySelectorAll("#nav a")) a.classList.toggle("on", a.getAttribute("href") === "#/" + view.tab);
  window.explore.busy = true;
  window.explore.view = view.id;
  markNavigationLocation(view);
  try {
    let arg;
    try { arg = decodeURIComponent(parts.slice(1).join("/")); }
    catch { throw new Error("Malformed route encoding"); }
    let r = await view.render(arg, routeCtx(tok, be, arg));
    if (tok !== routeTok) return;
    if (typeof r === "string") r = { html: r };
    $("#main").innerHTML = r.html;
    if (r.dispose) disposers.push(r.dispose);
    if (view.id !== "graph") window.scrollTo(0, 0);
    if (r.init) await r.init();
  } catch (e) {
    if (tok !== routeTok || e instanceof Superseded) return;
    if (e instanceof SourceChanged) { $("#main").innerHTML = changedNotice(e); wireChangedNotice($("#main")); }
    else $("#main").innerHTML = `<p class="err">${esc(e.stack || e.message || e)}</p>`;
  } finally {
    if (tok === routeTok) { await updateStats(); window.explore.hash = location.hash; window.explore.busy = false; }
  }
}
window.addEventListener("hashchange", route);
// Event handlers of a superseded route may still be awaiting a query: their rejection is expected.
window.addEventListener("unhandledrejection", (e) => { if (e.reason instanceof Superseded) e.preventDefault(); });


// ---------- sections: content other tasks add to existing pages ----------
// A section adds a block to the pages of one or more subjects, without editing their views:
//   registerSection({ id, title, on: ["artifact", "wasm-component", "wasm-module"], order,
//                     render(subject, ctx) -> HTML | "" | Promise })
// `subject` describes what the page shows (see `SECTION_SUBJECTS`); "" (or nothing) leaves the
// page as it is. A section that throws shows its error in its own block; the page still renders.
// Sections render in `order`, then by id, after the page's identity block (name, source, files).
const SECTION_SUBJECTS = {
  artifact: "{ kind: 'artifact', cid, sid, name, type, sha256, size }",
  "wasm-component": "{ kind: 'wasm-component', slug, title, cid, cidVia, sha256, name, path } (the registered blob; cid null for an embedded one; " +
    "cidVia 'sha256' when a Lean-built module's SHA-256 is exactly that of one registered artifact)",
  "wasm-module": "{ kind: 'wasm-module', slug, title, cid, cidVia, sha256, name, path } (as for components)",
};
const SECTIONS = [];
function registerSection(sec) {
  if (!sec || !/^[a-z][a-z0-9-]*$/.test(sec.id || "") || typeof sec.render !== "function") throw new Error("registerSection: needs an id and render");
  const on = [].concat(sec.on || []);
  if (!on.length || on.some((k) => !SECTION_SUBJECTS[k])) throw new Error(`registerSection: on must be among ${Object.keys(SECTION_SUBJECTS).join(", ")}`);
  if (SECTIONS.some((s) => s.id === sec.id)) throw new Error(`registerSection: ${sec.id} is registered twice`);
  SECTIONS.push(Object.freeze({ id: sec.id, title: sec.title || sec.id, on, order: sec.order || 0, render: sec.render }));
  SECTIONS.sort((a, b) => a.order - b.order || a.id.localeCompare(b.id));
}
async function sections(kind, subject, ctx) {
  let h = "";
  for (const sec of SECTIONS.filter((s) => s.on.includes(kind))) {
    let body;
    try { body = await sec.render(Object.freeze(Object.assign({ kind }, subject)), ctx); }
    catch (e) {
      if (e instanceof Superseded || e instanceof SourceChanged) throw e;
      body = `<p class="err">${esc(e.message || e)}</p>`;
    }
    if (body) h += `<section class="ext" data-section="${esc(sec.id)}"><h2>${esc(sec.title)}</h2>${body}</section>`;
  }
  return h;
}

// ---------- the API for views ----------
// `Explorer` is what a view file (explore/views/*.js, bundled after this file by explore.rs) may
// use: views register with `Explorer.registerView` (the contract is above), and `Explorer.ui`
// holds the shared components (ui.js, table.js). Everything else in this script is internal.
window.Explorer = Object.freeze({
  registerView,
  registerViewer,
  registerSection,
  ui: Object.freeze({ esc, href, link, badge, statusBadge, statusInfo, statusCode, statusText, expectationSummary, semantics: StatusSemantics, axiomChip, table, tableOf, dl, dialog, viewer, highlightWat, hexDump }),
  tables: () => new Set(tables),
  schema: SCHEMA,
});
