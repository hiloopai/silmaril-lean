// The page holds no data. It opens a SQLite file, in this order: `?db=<url>`, the URLs written by
// `sil project explore` (relative to the page), a file picker or drop. Over http(s) it reads the
// file lazily with sql.js-httpvfs (HTTP Range requests for page-aligned blocks) when the server
// answers a Range request with 206, and otherwise downloads the whole file into sql.js.
// `?load=full` forces the whole download.
const SQLJS = "https://cdnjs.cloudflare.com/ajax/libs/sql.js/1.12.0/";
const SQLJS_WASM_SRI = "sha384-R/MwdqDq6/VfWyY+p8u2RAFr+3gVOgzxeJqDeDxCnpQaVqOc9tEFLu4wdQfoDpb5";
const HTTPVFS = "https://cdn.jsdelivr.net/npm/sql.js-httpvfs@0.8.12/dist/";
const HTTPVFS_WORKER_SRI = "sha384-BrR3wW39f7nMD+hl+U8cK/5koOrbeue14Qauqf765b5XI6FVLJ4X9MXtcJQwNLAf";
const HTTPVFS_WASM_SRI = "sha384-CwaF51S8nw9DzEnqyuX2TtKOMgGc+3pdu8lNwsR0A95D6qEFmY6iEyTn4d4PiHGK";
const SCHEMA = "silmaril.project-db.v0.1";
const PARAMS = new URLSearchParams(location.search);
const DB_URLS = JSON.parse(document.getElementById("db-urls").textContent);
// The size and SHA-256 of the default database when the page was generated (or null).
const DB_META = JSON.parse(document.getElementById("db-meta").textContent || "null");
let be = null, cy = null;   // the open database (a backend, see below) and the project graph
let tables = new Set();     // tables and views of the open database
let indexes = new Set();    // its indexes (`schema::INDEXES` in the checker)
// Caches filled by bounded lookups: name -> whether it names an object of that kind; verdicts.
const KINDS = ["problem", "value", "format", "artifact", "machine"];
let known = {}, verdictOf = new Map(), summaryOf = new Map();
// For tests and the curious: the state of the page.
window.explore = { ready: false, busy: false, mode: null, source: null };

const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const kB = (n) => n < 1e6 ? (n / 1e3).toFixed(1) + " kB" : (n / 1e6).toFixed(2) + " MB";
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const ph = (n) => Array(n).fill("?").join(",");
// `sql` with `$` replaced by placeholders, over `names` in chunks (one query per 300 names).
async function inChunks(sql, names, twice) {
  const out = [];
  for (let i = 0; i < names.length; i += 300) {
    const part = names.slice(i, i + 300);
    out.push(...await q(sql.replaceAll("$", ph(part.length)), twice ? part.concat(part) : part));
  }
  return out;
}
// The first `n` rows of `sql` (which must not have a LIMIT), and whether there are more.
async function first(n, sql, params) {
  const rows = await q(sql + " LIMIT " + (n + 1), params);
  return { rows: rows.slice(0, n), more: rows.length > n };
}

// ---------- cross-links ----------
