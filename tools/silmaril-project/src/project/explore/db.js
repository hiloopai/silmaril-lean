// ---------- loading ----------
function isSqlite(buf) { return buf.length >= 16 && new TextDecoder().decode(buf.slice(0, 15)) === "SQLite format 3"; }
// Worker and WASM assets are verified before they are run from same-origin blobs.
async function sriAsset(url, integrity) {
  const r = await fetch(url, { integrity, mode: "cors" });
  if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
  return r;
}
let sqlJs = null;
function loadSqlJs() {
  return sqlJs || (sqlJs = (async () => {
    const r = await sriAsset(SQLJS + "sql-wasm.wasm", SQLJS_WASM_SRI);
    return initSqlJs({ wasmBinary: await r.arrayBuffer() });
  })());
}
// A backend: query(sql, params) -> rows as objects; exec(sql) -> [{columns, values}]; stats().
async function wholeBackend(bytes, mode) {
  const SQL = await loadSqlJs();
  const d = new SQL.Database(bytes);
  return {
    mode, size: bytes.length,
    async query(sql, params) {
      const st = d.prepare(sql);
      try { st.bind(params); const out = []; while (st.step()) out.push(st.getAsObject()); return out; }
      finally { st.free(); }
    },
    async exec(sql) { return d.exec(sql); },
    async stats() { return { totalBytes: bytes.length, totalFetchedBytes: bytes.length, totalRequests: mode === "local file" ? 0 : 1 }; },
    close() { d.close(); },
  };
}
async function sha256Hex(bytes) {
  if (!crypto.subtle) return null;
  const d = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return [...d].map((b) => b.toString(16).padStart(2, "0")).join("");
}
// What we can say about the bytes against the page's DB_META (same URL only).
function metaNote(u, size, sha) {
  if (!DB_META || DB_META.url !== u) return "";
  if (size !== undefined && size !== DB_META.size) return "; the page was generated for another version of the database";
  if (sha) return sha === DB_META.sha256 ? "; SHA-256 verified" : "; SHA-256 differs from the page's";
  return "";
}
// The fallback takes a complete snapshot in one response, with a default size cap.
const WHOLE_LIMIT = Math.min(256 * 1024 * 1024, Number(PARAMS.get("whole-limit")) || Infinity);
class TooLarge extends Error {
  constructor(url, total, why) {
    super(`${url} is ${total ? kB(total) : "of unknown size"}; ${why}, so it would be read whole into memory`);
    this.name = "TooLarge"; Object.assign(this, { url, total });
  }
}
// The body of `r`, failing beyond `limit` bytes (whatever the headers said).
async function readCapped(r, limit, url, why) {
  const parts = []; let n = 0;
  const rd = r.body.getReader();
  for (;;) {
    const { done, value } = await rd.read();
    if (done) break;
    n += value.length;
    if (n > limit) { rd.cancel().catch(() => {}); throw new TooLarge(url, null, why); }
    parts.push(value);
  }
  const out = new Uint8Array(n); let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}
async function openUrl(u, opts) {
  const url = new URL(u, location.href).href;
  const whole = PARAMS.get("load") === "full" || !!opts?.whole;
  let r;
  try { r = await fetchDbHeader(url); }
  catch (e) { throw new Error("could not fetch (" + e.message + ")"); }
  let why = "";
  if (r.status === 206) {
    const meta = dbHeaderMetadata(r);
    if (!whole && meta.size && meta.etag && meta.identity) {
      const head = await readCapped(r, 100, url, "the database header range was not 100 bytes").catch((e) => {
        if (e instanceof TooLarge) throw new Error("the database header range was not 100 bytes");
        throw e;
      });
      if (head.length !== 100 || !isSqlite(head)) throw new Error("not a SQLite database");
      const storedPageSize = (head[16] << 8) | head[17];
      const pageSize = storedPageSize === 1 ? 65536 : storedPageSize;
      if (pageSize < 512 || pageSize > 65536 || (pageSize & (pageSize - 1)) || meta.size % pageSize) {
        throw new Error("invalid SQLite page size or file length");
      }
      const cached = await registerPageCache();
      try {
        const b = await lazyBackend(url, pageSize, meta);
        b.mode += (cached ? "; ranges cached across reloads" : "") + metaNote(u, meta.size);
        return b;
      } catch (e) {
        if (e instanceof SourceChanged) throw e;
        why = `lazy loading failed: ${e.message || e}`;
      }
    } else {
      r.body?.cancel().catch(() => {});
      if (!meta.identity) why = "the server encoded its Range response";
      else if (!meta.size) why = "the server sent no valid Content-Range total";
      else if (!meta.etag) why = "the server sent no strong ETag, which lazy reads need to stay on one version";
    }
    if (!whole && meta.size > WHOLE_LIMIT) throw new TooLarge(url, meta.size, why);
    r = await fetch(url, { cache: "no-store" });
  } else {
    why = "the server ignored the Range request";
  }
  if (r.status !== 200) throw new Error("HTTP " + r.status + " when opening " + u);
  const declared = Number(r.headers.get("content-length"));
  if (!whole && declared > WHOLE_LIMIT) {
    r.body?.cancel().catch(() => {});
    throw new TooLarge(url, r.headers.get("content-encoding") ? null : declared, why);
  }
  const bytes = whole ? new Uint8Array(await r.arrayBuffer()) : await readCapped(r, WHOLE_LIMIT, u, why);
  if (!isSqlite(bytes)) throw new Error("not a SQLite database");
  const sha = await sha256Hex(bytes);
  return wholeBackend(bytes, "whole file" + (whole ? "" : ` (${why})`) + metaNote(u, bytes.length, sha));
}
function pickHelp(why) {
  const def = DB_URLS[0] || "project.sqlite";
  return `<div class="pick"><h2>Choose the database</h2>${why}
    <p><label>Open a project.sqlite <input type="file" class="dbfile" accept=".sqlite,.sqlite3,.db"></label>, or drop it on this page.
    <code>sil project sqlite</code> writes it to <code>${esc(def)}</code> (relative to this page).
    The file is read in the browser; nothing is uploaded.</p>
    <p>To have the page open it by itself, serve the project directory over HTTP, preferably with a
    server that supports Range requests so that only the pages a view needs are fetched, e.g.
    <code>npx http-server -p 8080 .lake/silmaril</code> in the project directory (by default the
    page and the database are both there), then open <code>http://localhost:8080/explore.html</code>.
    Another file: add <code>?db=&lt;url&gt;</code>.</p></div>`;
}
// ---------- the source: which database is open ----------
// One database is open at a time. Opening another (a URL, a chosen or dropped file) takes a new
// `openTok`: an attempt that finishes after a later one started is closed and dropped, so a slow
// download can never replace the file the reader chose since.
let openTok = 0;
const source = { label: null, mode: null, schema: null, problem: null };
const originalTitle = $("#title").textContent;
const supportedSchema = schema => schema === SCHEMA || schema === "corpus.catalog.v1";
function shortMode(mode) {
  return !mode ? "" : /^lazy/.test(mode) ? "lazy" : /^local/.test(mode) ? "local file" : "whole file";
}
function renderSource() {
  const el = $("#source");
  const name = source.label ? source.label.replace(/[?#].*$/, "").split("/").pop() || source.label : "no database";
  const warn = source.problem || (source.schema && !supportedSchema(source.schema));
  el.innerHTML = `<span class="src-name">${esc(name)}</span>` + (source.mode ? ` <span class="muted">${esc(shortMode(source.mode))}</span>` : "") +
    (warn ? ' <b class="src-warn" aria-hidden="true">!</b>' : "");
  el.setAttribute("aria-label", `Database: ${source.label || "none"}${source.mode ? ", " + source.mode : ""}${warn ? ", needs attention" : ""}. Show details or open another.`);
  el.title = "the database this page reads: details, or open another";
}
async function sourceDialog() {
  const s = be ? await be.stats().catch(() => null) : null;
  const row = (k, v) => v ? `<dt>${esc(k)}</dt><dd>${v}</dd>` : "";
  const body = (source.problem ? `<p class="err" role="alert">${esc(source.problem)}</p>` : "") +
    "<dl>" + row("source", source.label ? `<code>${esc(source.label)}</code>` : "none") +
    row("read", source.mode && esc(source.mode)) +
    row("schema", source.schema && `<code>${esc(source.schema)}</code>` + (supportedSchema(source.schema) ? "" : ` <span class="err">this page expects ${esc(SCHEMA)} or corpus.catalog.v1</span>`)) +
    row("transferred", s && (be.mode === "local file" ? `${esc(kB(s.totalBytes))} in memory` :
      `${esc(kB(s.totalFetchedBytes))} of ${esc(kB(s.totalBytes))}${s.totalRequests ? ` in ${s.totalRequests} requests` : ""}`)) + "</dl>" +
    (be && be.changed && be.changed() ? '<p><button type="button" id="reopen">Open the new version</button></p>' : "") +
    '<h3>Open another database</h3><p><label>file <input type="file" class="dbfile" accept=".sqlite,.sqlite3,.db"></label> ' +
    '<span class="muted">read in the browser; nothing is uploaded</span></p>' +
    '<form class="dburl"><label>URL <input type="text" name="u" size="40" placeholder="project.sqlite or https://…"></label> <button type="submit">Open</button></form>' +
    (DB_URLS.length ? `<p class="muted">this page's default: <code>${esc(DB_URLS[0])}</code></p>` : "");
  const d = dialog({ title: "Database", body });
  wireFilePickers(d.el, d.close);
  const re = d.el.querySelector("#reopen");
  if (re) re.addEventListener("click", () => { d.close(); const u = source.label; openSource(u, () => openUrl(u)); });
  d.el.querySelector("form.dburl").addEventListener("submit", (e) => {
    e.preventDefault();
    const u = e.target.u.value.trim();
    if (u) { d.close(); openSource(u, () => openUrl(u)); }
  });
}
function wireFilePickers(root, done) {
  for (const i of root.querySelectorAll("input.dbfile")) i.addEventListener("change", (e) => {
    const f = e.target.files[0];
    if (f) { if (done) done(); openFile(f); }
  });
}
// Open what `make()` returns under `label`; false when a later attempt superseded this one.
async function openSource(label, make) {
  const tok = ++openTok;
  disposeRoute();
  routeTok++;   // the current view stops here: its late queries are superseded
  $("#main").innerHTML = `<div id="msg">Opening ${esc(label)}…</div>`;
  try {
    const b = await make();
    if (tok !== openTok) { if (b.close) b.close(); return false; }
    await useDb(b, label);
    return true;
  } catch (e) {
    if (tok !== openTok || e instanceof Superseded) return false;
    window.explore.failed = unreadable(e);
    $("#main").innerHTML = `<div id="msg">${pickHelp(`<p class="err">could not open ${esc(label)}: ${esc(unreadable(e))}</p>` + tooLargeOffer(e))}</div>`;
    wireFilePickers($("#main"));
    wireTooLarge($("#main"));
    return false;
  }
}
// The open database changed on the server: say so in the source button and dialog (for the
// database that is open now only; an old backend's late report is ignored).
function noteChanged(e) {
  if (!be || !be.changed || be.changed() !== e) return;
  source.problem = e.message;
  renderSource();
  window.explore.changed = { was: e.was, now: e.now || null, why: e.why || null };
}
// What a view shows instead when its database changed: the way to the new version.
function changedNotice(e) {
  return `<div class="note" role="alert"><p><b>The database changed.</b> ${esc(e.message)}</p>` +
    '<p><button type="button" id="reopen">Open the new version</button> <button type="button" id="pickother">Choose another database…</button></p></div>';
}
function wireChangedNotice(root) {
  const r = root.querySelector("#reopen"), o = root.querySelector("#pickother");
  if (r) r.addEventListener("click", () => { const u = source.label; openSource(u, () => openUrl(u)); });
  if (o) o.addEventListener("click", () => sourceDialog());
}
async function boot() {
  renderNav();
  renderSource();
  const urls = [...new Set([PARAMS.get("db"), ...DB_URLS].filter(Boolean))];
  if (location.protocol === "file:") {
    $("#main").innerHTML = `<div id="msg">${pickHelp(`<p>This page was opened from a file (<code>file://</code>),
      where browsers block it from reading other files, including ${urls.map((u) => `<code>${esc(u)}</code>`).join(", ")}.</p>`)}</div>`;
    wireFilePickers($("#main"));
    return;
  }
  const tok = ++openTok, tried = [];
  for (const u of urls) {
    $("#msg") && ($("#msg").textContent = `Opening ${u}…`);
    let b;
    try { b = await openUrl(u); }
    catch (e) { tried.push(`<li><code>${esc(u)}</code>: ${esc(e.message || e)}${tooLargeOffer(e)}</li>`); continue; }
    if (tok !== openTok) { if (b.close) b.close(); return; }   // the reader chose a file meanwhile
    try { return await useDb(b, u); } catch (e) {
      if (e instanceof Superseded) return;
      // the file opened but cannot be read (e.g. its schema pages are damaged): try the next
      tried.push(`<li><code>${esc(u)}</code>: ${esc(unreadable(e))}</li>`);
    }
  }
  if (tok !== openTok) return;
  window.explore.failed = tried.length ? tried.join(" ") : null;
  $("#main").innerHTML = `<div id="msg">${pickHelp(`<p>No database could be opened from:</p><ul>${tried.join("")}</ul>`)}</div>`;
  wireFilePickers($("#main"));
  wireTooLarge($("#main"));
}
// A database too large to read whole by default: the reader may still ask for it.
// A database that opened but whose first queries fail: SQLite's own words, and what they mean.
function unreadable(e) {
  const m = String(e && e.message || e);
  return /malformed|not a database|corrupt/i.test(m) ? `${m}. The file as served is damaged, or not a database this page can read ` +
    "(check it with `sqlite3 <file> 'PRAGMA integrity_check'`); it was not opened." : m;
}
function tooLargeOffer(e) {
  return e instanceof TooLarge ? ` <button type="button" class="loadwhole" data-url="${esc(e.url)}">Read it whole anyway${e.total ? ` (${esc(kB(e.total))})` : ""}</button>` : "";
}
function wireTooLarge(root) {
  for (const b of root.querySelectorAll("button.loadwhole")) b.addEventListener("click", () => {
    const u = b.dataset.url;
    openSource(u, () => openUrl(u, { whole: true }));
  });
}
async function useDb(b, label) {
  if (be && be.close) try { be.close(); } catch (e) { /* ignore */ }
  be = b;
  if (b.profile) window.explore.vfsProfile = b.profile;
  else delete window.explore.vfsProfile;
  disposeRoute();
  routeTok++;   // whatever the old database's route still awaits is superseded
  known = Object.fromEntries(KINDS.map((k) => [k, new Map()]));
  verdictOf = new Map(); summaryOf = new Map(); statusOf = new Map();
  let ts, ix, metaRows = [];
  try {
    ts = await q("SELECT name FROM sqlite_master WHERE type IN ('table', 'view')");
    ix = await q("SELECT name FROM sqlite_master WHERE type = 'index'");
    if (ts.some((r) => r.name === "meta")) metaRows = await q("SELECT value FROM meta WHERE key = 'schema'");
    else if (ts.some((r) => r.name === "corpus_meta")) metaRows = await q("SELECT value FROM corpus_meta WHERE key = 'schema'");
  } catch (e) {
    // not readable: no database stays open (the caller says why)
    if (!(e instanceof Superseded) && be === b) {
      be = null; window.explore.ready = false;
      delete window.explore.vfsProfile;
      try { if (b.close) b.close(); } catch (x) { /* ignore */ }
      Object.assign(source, { label: null, mode: null, schema: null, problem: null }); renderSource();
    }
    throw e;
  }
  tables = new Set(ts.map((r) => r.name));
  $("#title").textContent = tables.has("corpus_artifacts") && !tables.has("projects") ? "Silmaril corpus explorer" : originalTitle;
  renderNav();
  indexes = new Set(ix.map((r) => r.name));
  const schema = (metaRows[0] || {}).value || "?";
  Object.assign(source, { label, mode: b.mode, schema, problem: null });
  renderSource();
  Object.assign(window.explore, { ready: true, mode: b.mode, source: label, opened: (window.explore.opened || 0) + 1, changed: null, failed: null });
  await route();
}
async function updateStats() {
  if (!be) return;
  const s = await be.stats();
  if (s) {
    $("#stats").textContent = be.mode === "local file" ? `${kB(s.totalBytes)} in memory`
      : `read ${kB(s.totalFetchedBytes)} of ${kB(s.totalBytes)}`;
    window.explore.stats = s;
  }
}
function openFile(f) {
  return openSource(f.name, async () => {
    const bytes = new Uint8Array(await f.arrayBuffer());
    if (!isSqlite(bytes)) throw new Error("not a SQLite database (run `sil project sqlite` and choose its .sqlite file)");
    return wholeBackend(bytes, "local file");
  });
}
$("#source").addEventListener("click", () => { sourceDialog(); });
document.addEventListener("dragover", (e) => { e.preventDefault(); $("#drop").style.display = "flex"; });
document.addEventListener("dragleave", (e) => { if (!e.relatedTarget) $("#drop").style.display = "none"; });
document.addEventListener("drop", (e) => {
  e.preventDefault(); $("#drop").style.display = "none";
  if (e.dataTransfer.files[0]) openFile(e.dataTransfer.files[0]);
});

