# Exploring a project database

`sil project explore` writes one static page, `.lake/silmaril/explore.html`, that opens a silmaril
project's database in the browser. It complements [silmaril-projects.md](silmaril-projects.md), which
describes the database itself (`sil project sqlite`).

```
sil project sqlite [--httpvfs [--page-size 4096]]   # writes .lake/silmaril/project.sql and .lake/silmaril/project.sqlite (with its indexes)
sil project explore [--dir .] [--db .lake/silmaril/project.sqlite] [--out .lake/silmaril/explore.html]
                    [--source-url https://github.com/<owner>/<repo> --source-rev <commit>]
```

The page holds no data. Project databases can grow large, so the page never embeds the database
or its SQL text; it opens a separate `.sqlite` file. The page is about 160 kB.

## How the page finds the database

It tries these sources in order:

1. `?db=<url>`, a query parameter (relative to the page, or absolute);
2. `--db`, written into the page at generation time, relative to the page (by default the
   page and the database are both in `.lake/silmaril/`, so this is `project.sqlite`);
3. `project.sqlite` next to the page;
4. a file chosen with **open a project.sqlite**, or dropped onto the page.

Over `file://`, browsers block a page from reading other files, so only the fourth source works.
The page says so and shows where `sil project sqlite` wrote the database. A chosen file is read
into memory in the browser; nothing is uploaded.

The header shows how many bytes have been read so far and a compact source button (the file name,
`lazy`, `whole file` or `local file`, and `!` when something needs attention). The button opens a
dialog with the source, how it is read, the schema version and the transfer counts, and with a file
picker and a URL field to open another database.

## Graph, evidence and sources

**The graph** does not draw every problem by default. Below each parent, leaves (problems with no
children of their own) are stacked by status code: `16 × OPN` is one node. Clicking a stack lists
its problems in the side panel, and **Expand** draws them one by one (for that parent). **every
problem** draws all of them. Problems that need attention (an unexplained failure, an unmet
expectation), the focus and the root are never stacked. The count line says how many problems
the neighbourhood has, how many are drawn and how many are in stacks. Nodes are neutral, and are
marked red for an unexplained failure, dashed for an unmet expectation and grey for deprecated.

**Evidence.** A problem's page says what its summary status rests on. These are the statuses with
that code and how each was obtained: an answer or a solving theorem (with its axioms and tier), a
refutation, an instance, a decomposition. An open problem says that nothing is recorded.

**Sources.** With `--source-url` (a GitHub repository) and `--source-rev` (a commit, 7 to 40 hex
digits), `sil project explore` writes into the page the file of each module the database names
that exists under the project's source directories. Problems and answers then link to their
modules at that commit. **view** fetches the file from `raw.githubusercontent.com` (at most 1 MiB)
and shows the lines where a text search finds the declaration, escaped. The dialog says that the
line was found by a text search. That the declaration was kernel-checked is what the database's
tier says, not the source view. `make pages PAGES_SOURCE_REV=<commit>` passes the repository and
that commit (the Pages workflow passes the pushed commit). The commit is never guessed from a
checkout, whose HEAD may be one GitHub does not have.
Without these options the page has no source links.

**Bytes.** An artifact of the local package has a **view** button. It reads at most 64 KiB of the
file from the repository at that commit, shows it as text (when it is UTF-8) or hex, and, when it
read the whole file, says whether its SHA-256 matches the registry's. A Wasm module or component
page shows its WAT highlighted, and its bytes. Viewers are registered (`Explorer.registerViewer`),
so a view for another format is one more entry.

`tests/explore/provenance.mjs` checks these in Chromium on a `make pages` output: stacks and their
counts, expanding, "every problem", that no problem needing attention is stacked, evidence links
pinned to the commit, the source view, the byte viewer with its SHA-256 check, and the WAT
highlighting.

## The published explorer

`.github/workflows/pages.yml` publishes silmaril's own project at
<https://hiloopai.github.io/silmaril-lean/>. It runs on every push to `main` (and by hand), and
builds on hiloop's prove service (`make pages`). It is not a `workflow_run` of CI, because the prove
service refuses OIDC tokens of `workflow_run` events. The worker restores main's build from the
shared Lake pool and runs `sil project dump`, `check`,
`sqlite --httpvfs` and `explore --db _site/project.sqlite --out _site/index.html`, and deploys
`_site` to GitHub Pages (repository setting: Pages source "GitHub Actions"). The site holds only
what the public repository already contains. GitHub Pages answers Range requests with the
identity bytes, so the page reads the database lazily (see below for why it ignores `HEAD`), and
the deploy job checks a Range request on the deployed file.

To view a local build instead:

```
make project-tool && build/bin/silmaril-project dump && build/bin/silmaril-project check
build/bin/silmaril-project sqlite --httpvfs && build/bin/silmaril-project explore
npx http-server -p 8080 .lake/silmaril   # then open http://localhost:8080/explore.html
```

## Serving it over HTTP

Serve the project directory and open the page, for example:

```
npx http-server -p 8080 .lake/silmaril   # in the project directory
# then open http://localhost:8080/explore.html
```

`http-server` supports Range requests but sends a weak ETag, and `python3 -m http.server` does
not support Range requests, so with either the page reads the whole database (see below).
GitHub Pages, and `tests/explore/pages_server.py`, allow lazy reads.

### Lazy loading (HTTP Range)

The page first requests the 100-byte SQLite header with `Range: bytes=0-99` (never from the cache).

- **206 Partial Content, identity bytes, `Content-Range: bytes 0-99/<length>` and a strong
  `ETag`.** SQLite runs in a worker using [sql.js-httpvfs](https://github.com/phiresky/sql.js-httpvfs).
  Each block miss requests an aligned **1 MiB** range, shortened at EOF. Some fetched pages
  may go unused. The loader reduces the block size for databases that would otherwise fit in
  one block, down to a minimum of one SQLite page.
- **Other responses.** When lazy loading is unavailable, plain sql.js opens the database
  from a single full response. The fallback caps downloads at 256 MiB unless the reader
  chooses **Read it whole anyway** or uses `?load=full`. When the page was generated next to the
  database, it checks the SHA-256 of the downloaded bytes and reports the result.

**The GET probe supplies length and identity.** The pinned VFS adapter uses the validated
`Content-Range` length directly and skips the worker's synchronous HEAD. GitHub Pages can
serve compressed representation metadata on HEAD, while the probe describes the raw file.
An in-database UUID is available only after a read and cannot attest to the remaining ranges.
A source commit identifies bytes only when all build inputs are pinned and the artifact URL
serves immutable bytes. On the mutable Pages URL the strong ETag is checked on every read.

**Versions and caching.** Tagged range requests carry the strong ETag and length.
`explore-sw.js` caches exact ranges in Cache Storage by source URL, version and range. It
keeps the original strong validator when it reconstructs a cached 206. When it caches a new
version of a source, it drops previous versions. The initial 100-byte probe always goes to
the server. `?cache=off` skips registration, so use a fresh browser context or block service
workers to compare without an existing controller. The VFS caches blocks in memory during
the visit. For cross-origin databases, the server must expose `Content-Range`, `ETag`, and
`Content-Encoding` via CORS.

**Experiment knobs.** Use `?vfs-chunk=page` for one physical page per demand read, or pass
a page-aligned byte count up to 4 MiB, for example `?vfs-chunk=65536` on the Pages database.
Invalid choices use the default. The worker caps the upstream read-ahead algorithm at one
block and fetches only on demand. Changing this setting leaves the physical SQLite page
size intact.

To inspect reads, open with `?vfs-profile=1`, then use the browser console:

```js
const trace = await window.explore.vfsProfile();
console.table(trace.events.filter(event => event.type === "fetch"));
```

Each call drains the worker's trace of up to 8192 events. `dropped` reports additional
events since the previous drain. A `read` event is a SQLite request for bytes. A `fetch`
event records the requested block, returned range, status, acceptance, byte count and
duration. Byte offsets are zero-based with exclusive ends. Page numbers are one-based
and inclusive. Times are milliseconds relative to the worker's `timeOrigin`.
`cache-storage` marks an explorer service worker hit. `http` is the HTTP path, which can
include browser and CDN caches. The trace starts with the worker and excludes the initial
probe. Profiling is local and off by default.

`tests/explore/range_cache.mjs` exercises default partial reads without HEAD, chunk overrides,
EOF, profiling, warm cache, and replacements in Chromium against `pages_server.py`.

### One snapshot per open database

Every range read is checked in the worker, before SQLite sees its bytes: it must be a `206` of
exactly the requested bytes, of a file with the length and the strong ETag that the database was
opened at. Lazy reads need a strong ETag: a `Last-Modified` date has a one-second resolution, and a
weak ETag does not promise the same bytes, so a file replaced by another of the same size within a
second would pass for the same version. Without a strong ETag the page reads the whole file instead
(above). The first read that fails the check fails its query
(it is not retried), the source button is marked `!`, and the view says that the database changed
and offers to open the new version or another file. A query on a database that has not changed but
is damaged reports SQLite's own error (for example "database disk image is malformed"), saying that
the version is unchanged so the file itself is damaged. Before this check, a database rebuilt while
a page had it open lazily gave "database disk image is malformed" on later graph or problem
views: the page read pages of the new file under the old version's URL.

`sil project sqlite` builds the database in a temporary file next to it and renames it into place,
so a server never serves a half-written database. The service worker caches a page only for the
version its URL names, and keeps its validators so cached pages are checked like fresh ones.
`tests/explore/snapshot.mjs` replaces the served file while a page reads it. It covers a longer
file during graph navigation, a file of the same length, a replacement during a query, recovery
through a chosen file, and a damaged but unchanged file. It also checks servers with a weak ETag,
with only `Last-Modified` and with no validator (`pages_server.py --validators`). For each, the page
reads the whole file, and a same-size replacement with the same mtime leaves the opened snapshot
intact. Run against the earlier lazy reading, that case showed the new file's titles for all 12
problems not yet read. It also checks the size limit and the explicit **Read it whole anyway**.

`tools/silmaril-project/tests/explore/shell.mjs` checks the shared shell in Chromium: the
navigation built from the registered views, the source button and its dialog (keyboard, Escape,
focus), neutral status badges in one status column, rapid graph navigation (the last route wins)
and repeated switches between a local file and the lazy URL while views load: `node shell.mjs
_site [screenshots-dir]`.

`tools/silmaril-project/tests/explore/wasm_cfg.mjs` checks the Wasm function pages in Chromium
on a small and a large block CFG: the legend's edge counts against the page data, may-edges kept
but drawn only on selection, hover or request without moving any node, the inspector's exact
edges, keyboard navigation, direct links to a node, the stated dominator basis and its agreement
with the kernel-checked table, and that module call graphs and machine pages still draw. Run it on
a `make pages` output: `node wasm_cfg.mjs _site [screenshots-dir]`. `wasm_cfg_variants.mjs` checks graph variants and named dominator
bases (issue #231) on synthetic fixtures built from that output: the data's default variant, links,
relations shown as unchecked metadata, outcomes as marks rather than edges, instruction-level graphs
boxed by block with links between the two granularities, and that a kernel table is shown as evidence only for exactly
the same nodes, entry and edges.

Requirements on the server for lazy loading:

- It must answer `Range: bytes=a-b` with `206`, the identity bytes and
  `Content-Range: bytes a-b/<length>`.
- For a database on another origin, CORS must allow the page's origin and expose
  `Content-Range`, `Content-Encoding` and `ETag`.

### Indexes and `sil project sqlite --httpvfs`

Lazy loading pays off only when queries can use indexes. Primary keys and `UNIQUE` constraints do
not cover, for example, `edges(parent)`, so without more indexes following an edge reads all of
`edges`. The canonical schema therefore creates the indexes of `schema::INDEXES` in the SQL text
itself, so every project database has them, whether it is read lazily, downloaded whole, or
queried with `sqlite3`:

- edges by parent, child and kind; `summary(verdict, summary)`; `problems(detached, name)`;
  `objects(kind)` (a narrow index for counts by kind);
- reverse lookups by problem, value, CID and format (`answers(problem)`,
  `problem_inputs(value)`, `value_sources(cid)`, `formats(base)` and so on).

`write_db` checks that the built file has exactly these indexes. They make the file about 30%
larger (9.97 MB instead of 7.52 MB on the large project measured below).

`--httpvfs` tunes the file using `PRAGMA page_size` (`--page-size`, 4096 by default),
`journal_mode = DELETE`, and `VACUUM`. This controls the database layout. The browser
chooses its transport block size when it opens the file.

sql.js-httpvfs supports fixed-size server files through `serverMode: "chunked"`.
The explorer describes a single server file and requests byte ranges within it.
Hosts without Range use the bounded whole-file fallback.

### Bounded queries

Every query the page issues is bounded, so a lazy read touches only part of the file:

- **Summary:** aggregates over indexes (counts by kind, verdicts, SZS codes), the first 100 groups
  by name, the first 100 problems that do not hold, and `meta`.
- **Lists:** 100 rows a page. The filter is a case-insensitive substring match, and the query
  stops once a page of matches is found.
- **Details:** each list is cut at 300 rows.
- **Graph:** one query per level for the edges out of that level, cut at 4 × *max nodes* edges.
  Node data comes from `IN (…)` lookups over the drawn nodes. A group's tally looks up at most
  500 children that are not drawn; the rest are labelled *unchecked*.
- **Cross-links:** cells are looked up by name with `IN (…)` (per column kind, or every string
  cell on the SQL page), never by loading every name.
- **SQL:** free-form, so it is unbounded. A query without `LIMIT` or an index can read the whole
  file.

### Measurements (a large project)

The database of a large project (3,550 problems, 6,322 edges) was built by `sil project sqlite` and
served from `127.0.0.1` by a small Range-capable server. The *no indexes* row is the same file
with every index dropped and `VACUUM`ed, for comparison. Headless Chrome loaded the summary and
then visited the root graph, the problem list, one problem page and a second graph. These are the
database bytes read with the earlier page-sized VFS and its sequential read-ahead. The
table excludes HTML and CDN assets.

| database | mode | after the summary | after all five views |
|---|---|---|---|
| canonical, 4096 B pages (9.97 MB) | whole file | 9.97 MB | 9.97 MB |
| canonical, 4096 B pages | lazy | 0.75 MB (111 requests) | 2.36 MB (258 requests) |
| `--httpvfs --page-size 1024` (10.6 MB) | lazy | 0.54 MB (185 requests) | 2.01 MB (401 requests) |
| no indexes, 4096 B pages (7.52 MB) | lazy | 3.28 MB (97 requests) | 4.65 MB (360 requests) |

Time to the first summary was 0.6–1.2 s in every mode on loopback, so time does not tell the
modes apart there. Over a real network, fewer bytes should load faster, while many small
requests add latency.

## What it shows

- **Summary:** the local project row, object counts by kind, and derived verdicts
  (holds/fails/unknown by summary code). It also shows statuses by SZS code with their
  coarsening, the root, the groups, the first problems that do not hold, and `meta`.
- **Progress** (`#/progress`, `views/progress.js`): every family of the project (the children of
  its root group), with each problem reachable through `children` edges counted once per family in
  exactly one of holds, fails and open, and apart from those: deprecated, expected open, findings,
  **axiomatic** (an answer uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound`), **not
  kernel** (settled at another tier) and detached. A project classifies its problems into
  **dimensions** with groups named `<prefix>.dimension.<d>`, `d` one of `inventory` (what the
  artifacts are), `decomposition` (where the functions are) and `semantic` (what the code does);
  the page cross-tabulates families and dimensions, lists problems in no dimension group as
  unclassified, and reads nothing from names or titles. Unit tests: `tests/explore/progress.test.mjs`.
- **Graph:** the problem DAG from `edges`, with the root on top (dagre layout).
  - Problems are coloured green, red or grey by their derived verdict. Groups are boxes labelled
    with their counts of children that hold, fail or are unknown.
  - Refutation routes are dashed, instance edges are dotted, and proved edges (`via`) are thick.
  - The graph starts at the root and shows whole levels below the focus, up to *depth*, while
    the total stays within *max nodes* (300 by default). A node with children that are not
    drawn shows `(+N hidden)`; `(+ more, not read)` marks a node whose edges were not read
    because of the edge cap.
  - The focus box suggests up to 30 problem names that contain the typed text.
  - Click a node to see its details in the side panel. Double-click a node to refocus on it.
- **Problems, Artifacts, Values, Formats:** paged, filterable tables. Each problem, value, format
  and artifact (CID or sid) has a detail page:
  - a problem's judgement, arguments, inputs, answers with their axioms, statuses, edges in and
    out (children with their verdicts), and the value sources it is the obligation of;
  - a value's sources (CID, format, obligation and its verdict) and the problems over it;
  - a format's laws, families, derived formats and values;
  - an artifact's paths, tool facts, and the values and problems that read it.
- **SQL:** a free-form query box with example queries. Results link every cell that names a
  known problem, value, format or artifact.

## Pinned scripts

The page loads these exact versions, each checked against an SRI hash. The worker and the WASM
files are fetched with `fetch(…, {integrity})`. The VFS worker is adapted after integrity
verification and runs with its WASM from `blob:` URLs. Review the exact-match adapter
against the upstream source when changing the VFS version.

| library | version | from | files |
|---|---|---|---|
| sql.js-httpvfs | 0.8.12 | jsdelivr | `index.js`, `sqlite.worker.js`, `sql-wasm.wasm` |
| sql.js | 1.12.0 | cdnjs | `sql-wasm.js`, `sql-wasm.wasm` |
| cytoscape | 3.30.2 | cdnjs | |
| dagre | 0.8.5 | cdnjs | |
| cytoscape-dagre | 2.5.0 | jsdelivr | |

cdnjs does not carry sql.js-httpvfs. Its jsdelivr files are byte-identical to the npm tarball.

The template is `tools/silmaril-project/src/project/explore.html` (the shell and its styles).
`explore.rs` fills in the title and the database URLs, and bundles the script from the files of
`explore/` in the order of its `SCRIPTS` list into one `<script>`:

| file | what it holds |
|---|---|
| `core.js` | constants, page state, small helpers |
| `ui.js` | shared components: links, status badges, the dialog, the byte viewer and WAT highlighting |
| `table.js` | tables and definition lists that link the names they show |
| `vfs-transport.js` | HTTP probe, snapshot guard and service worker registration |
| `vfs.js` | demand block policy, pinned worker adapter and opt-in trace |
| `db.js` | opening a database (lazy, whole, local file) and the source button and dialog |
| `router.js` | the view registry, routing and the per-route context |
| `graphs.js` | dominators and dominator trees shared by graph views |
| `views/*.js` | the views, each registering itself |
| `main.js` | the `Explorer` API object, and the start |

### Views

A view is a route `#/<id>/<arg>`. A file in `explore/views/` registers its views, and one line in
`SCRIPTS` (`script!("views/<file>.js")`, before `main.js`) adds the file to the page:

```js
Explorer.registerView({
  id: "languages",          // the route: #/languages/<arg>; [a-z][a-z0-9-]*, unique
  title: "Languages",       // shown in the navigation
  nav: 75,                  // position in the navigation; omit for detail views
  tab: "languages",         // the navigation entry to highlight (default: id)
  async render(arg, ctx) {  // HTML, or { html, init, dispose }
    const rows = await ctx.q("SELECT name FROM problems ORDER BY name LIMIT 20");
    return { html: await Explorer.ui.table(rows), init() { /* wire controls */ } };
  },
});
```

`ctx` belongs to one rendering of one route over one database: `ctx.q`, `ctx.tq` (empty when a
table is missing), `ctx.first` and `ctx.exec` query it, `ctx.alive()` says whether it is still
current, and `ctx.onDispose(fn)` releases resources when the route changes. Once the reader has
moved on or opened another database, every query of the old rendering rejects (and the router
ignores it), so a slow query can never write into the current page.

`Explorer.ui` holds the shared components: `esc`, `href`, `link`, `table(rows, cols, opts)`
(opts: `hints`, `render` for computed columns, `badges`, `nowrap`, `label`, `limit`), `tableOf`,
`dl`, `statusBadge(nameOrStatus)` and `statusInfo`, `dialog({ title, body, actions })` (a modal
`<dialog>`), `viewer(bytes, { name, total, lang, limit })` (bounded text/hex/WAT views;
`Explorer.registerViewer` adds views), `highlightWat` and `hexDump`. Everything they show is
escaped.

Status badges show a problem's summary as a three-character code (THM, OPN, SAT, UNS, CSA, UNK, and
NOC for the stored code `contingent`) in a neutral style. A closed proposition (arity 0) also
shows its truth value: `THM·true`, `UNS·false`. SAT counts as true and CSA as false there; there is
no CTH or TAU relabelling. A problem may have an expected status (`problems.expect`). The badge
compares it as `sil project check` does (W1): the expectation is met when it is the summary, or
one of the problem's established statuses (the `statuses` table, which holds the arity-0 closure
THM ⇒ SAT, UNS ⇒ CSA), or the summary is `contingent` and SAT or CSA is expected.
`Explorer.ui.statusInfo(s).outcome` is one of:

| outcome | when | badge |
|---|---|---|
| `none` | no expected status | neutral, whatever the verdict: a refutation is not a failure by itself |
| `pending` | an expected status, and the summary is not known (OPN, UNK) | neutral; the title names the expectation |
| `match` | the expectation is met | a quiet green ✓ |
| `mismatch` | a known summary that does not meet the expectation | an error: `!` |
| `error` | a finding classifies the problem as a genuine `error` | an error: `!` |

Statuses that hold together vacuously (THM and UNS over an empty carrier) are not an error by
themselves. `Explorer.ui.expectationSummary(list)` counts a group's outcomes. Its `allMet` is
true only when every problem has an expectation and meets it; a missing or unknown one is not a
pass. It counts expectations and is not a claim about the problems' conjunction. Deprecated
problems are struck through. The badge's title spells out the code with its SZS name, the stored
code when it differs, the closed truth value, the established statuses, the verdict, the
expectation and the markings. `contingent` (SAT and CSA both hold) is shown as
NOC, SZS's NoConsequence: "some interpretations are models of Ax, some models of Ax are models of
C, and some models of Ax are models of ~C" (current: [SZS Success ontology](https://szs.tptp.org/success);
historical: [Sutcliffe, The SZS Ontologies for Automated Reasoning Software (2008)](http://tptp.org/cgi-bin/SeeTPTP?Category=BibTeX&File=Sut08-KEAPPA)).
The display is one-to-one. The database keeps `contingent`, and its meaning is the SZS catalogue's
to define. THM is kept as stored and not shown as TAU. With no axioms THM and TAU coincide, but
the project's name for a proved problem is THM, "all models of Ax are models of C". The display
depends only on the stored code; the verdict shown is the database's (UNS fails a closed
proposition only). Over an empty domain no witness exists, so SAT, and therefore `contingent`,
cannot be established there; such problems show their stored code unchanged. A
deprecated problem's page links its replacements, and a replacement's page links what it
replaces.

### Sections

Other tasks add blocks to existing pages without editing their views:

```js
Explorer.registerSection({
  id: "acceptors",                       // unique, [a-z][a-z0-9-]*
  title: "Acceptor interpretations",
  on: ["wasm-component", "wasm-module", "artifact"],
  order: 10,
  async render(subject, ctx) {           // HTML, or "" to add nothing
    // subject: { kind, cid, sha256, name, ... } of the page's registered blob
    const rows = await ctx.tq("some_table", "SELECT ... WHERE cid = ?", [subject.cid]);
    return rows.length ? await Explorer.ui.table(rows) : "";
  },
});
```

Subjects: `artifact` is `{ kind, cid, sid, name, type, sha256, size }`. `wasm-component` and
`wasm-module` are `{ kind, slug, title, cid, cidVia, sha256, name, path }`, the registered blob
(`cid` is null for an embedded module). A module that wasm-pages built from a Lean value has no
CID, only the SHA-256 of its encoded bytes. When exactly one registered artifact has that SHA-256,
its CID becomes the subject's, with `cidVia: "sha256"`. Registrations keyed by CID, such as a
language under an interpretation (`op := artifact`), then show on the module's page. Sections render after the page's identity block. One that throws
shows its error in its own block, and the page still renders. If the route or the database changes
while a section renders, that is not caught: it goes to the router like any query of the view. Link
a language with `Explorer.ui.href("languages", key)`.

## Limitations

- The page needs network access to the CDNs. It does not work offline unless the browser has
  already cached the scripts.
- sql.js-httpvfs opens one database per worker. When a file is opened afterwards, the old
  worker stays until the page is closed.
- A lazily read database stays on the version it was opened at. When the file on the server is
  replaced (rebuilt, redeployed), the next read of a page not yet in memory fails its query and the
  page says that the database changed, with a button to open the new version; it never mixes the
  two. Two versions are told apart by the strong ETag and the length of range responses. A server
  without a strong ETag gets whole-file reads, up to 256 MB unless the reader asks for more. The
  check trusts the server's strong ETag to name the bytes, as HTTP requires.
- On a large project, dagre stays responsive only for a few hundred nodes, so the graph shows
  only a neighbourhood. A wide level, such as 3,400 problems at one depth, is cut off.
- A child that belongs to several groups is drawn once, with an edge from each group. Groups
  are drawn as box nodes, not as enclosing compound boxes.
- The page targets schema `silmaril.project-db.v0.1` and warns about any other schema. Queries
  against missing tables may fail.
