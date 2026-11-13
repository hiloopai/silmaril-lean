# Exploring a project database

`sil project explore` writes one static page, `.lake/silmaril/explore.html`, that opens a silmaril
project's database in the browser. It complements [silmaril-projects.md](silmaril-projects.md), which
describes the database itself (`sil project sqlite`).

```
sil project sqlite [--httpvfs [--page-size 4096]]   # writes .lake/silmaril/project.sql and .lake/silmaril/project.sqlite (with its indexes)
sil project explore [--dir .] [--db .lake/silmaril/project.sqlite] [--out .lake/silmaril/explore.html]
```

The page holds no data. Project databases can grow large, so the page never embeds the database
or its SQL text; it opens a separate `.sqlite` file. The page is about 46 kB.

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

The header shows the source, how it is read (lazily, whole file, or local file), the schema
version and how many bytes have been read so far.

## The published explorer

`.github/workflows/pages.yml` publishes silmaril's own project at
<https://hiloopai.github.io/silmaril-lean/>. It runs after CI succeeds on a push to `main` (and by
hand), restores main's build from the shared Lake pool, runs `sil project dump`, `check`,
`sqlite --httpvfs` and `explore --db _site/project.sqlite --out _site/index.html`, and deploys
`_site` to GitHub Pages (repository setting: Pages source "GitHub Actions"). The site holds only
what the public repository already contains. GitHub Pages answers Range requests, so the page
reads the database lazily.

To view a local build instead:

```
make project-tool && build/bin/silmaril-project dump && build/bin/silmaril-project check
build/bin/silmaril-project sqlite --httpvfs && build/bin/silmaril-project explore
npx http-server -p 8080 .lake/silmaril   # then open http://localhost:8080/explore.html
```

## Serving it over HTTP

Serve the project directory and open the page, for example:

```
npx http-server -p 8080 .lake/silmaril   # in the project directory; supports Range requests
# then open http://localhost:8080/explore.html
```

`python3 -m http.server` works but does not support Range requests, so the page downloads the
whole database (see below).

### Lazy loading (HTTP Range)

The page first requests the 100-byte SQLite header with `Range: bytes=0-99`.

- **206 Partial Content:** the page opens the database with
  [sql.js-httpvfs](https://github.com/phiresky/sql.js-httpvfs). SQLite runs in a web worker
  and reads one page at a time with HTTP Range requests, so the browser downloads only the pages
  that the queries touch. The chunk size is the database's page size (read from the header).
- **200 OK:** the server ignored `Range`. That response is the whole file, which the page opens
  in plain sql.js. `?load=full` forces this path even when Range works.

Requirements on the server for lazy loading:

- It must answer `Range: bytes=a-b` with `206` and a `Content-Range` header, and `HEAD` with a
  `Content-Length`. `Accept-Ranges: bytes` should be set.
- It must not compress the database (`Content-Encoding: gzip` breaks byte ranges; the page then
  falls back to the whole file).
- For a database on another origin, CORS must allow the page's origin and expose
  `Accept-Ranges`, `Content-Length`, `Content-Range` and `Content-Encoding`.

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

`--httpvfs` only tunes the file: `PRAGMA page_size` (`--page-size`, 4096 by default) and
`journal_mode = DELETE`, then `VACUUM`. The SQL text, the logical dump and the indexes do not
change. sql.js-httpvfs recommends `PRAGMA page_size = 1024`. Smaller pages read fewer bytes but
need more requests; see the measurements below.

sql.js-httpvfs can also split a database into fixed-size chunk files (`serverMode: "chunked"`),
for hosts that limit file sizes or do not support Range. `sil project` does not write chunks: a server
with Range support is enough for local and internal use, and without Range the page falls back to
a whole download.

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
bytes of the database read (the page itself and the CDN scripts are not counted):

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
files are fetched with `fetch(…, {integrity})` and run from `blob:` URLs, because a web worker
must have the page's origin.

| library | version | from | files |
|---|---|---|---|
| sql.js-httpvfs | 0.8.12 | jsdelivr | `index.js`, `sqlite.worker.js`, `sql-wasm.wasm` |
| sql.js | 1.12.0 | cdnjs | `sql-wasm.js`, `sql-wasm.wasm` |
| cytoscape | 3.30.2 | cdnjs | |
| dagre | 0.8.5 | cdnjs | |
| cytoscape-dagre | 2.5.0 | jsdelivr | |

cdnjs does not carry sql.js-httpvfs. Its jsdelivr files are byte-identical to the npm tarball.

The template is `tools/silmaril-project/src/project/explore.html`. `explore.rs` fills in the title and the
database URLs.

## Limitations

- The page needs network access to the CDNs. It does not work offline unless the browser has
  already cached the scripts.
- sql.js-httpvfs opens one database per worker. When a file is opened afterwards, the old
  worker stays until the page is closed.
- Lazy reads are cached in memory for the life of the page, and nothing persists across reloads.
  A database rebuilt while the page is open can give inconsistent reads; reload the page.
- On a large project, dagre stays responsive only for a few hundred nodes, so the graph shows
  only a neighbourhood. A wide level, such as 3,400 problems at one depth, is cut off.
- A child that belongs to several groups is drawn once, with an edge from each group. Groups
  are drawn as box nodes, not as enclosing compound boxes.
- The page targets schema `silmaril.project-db.v0.2`. It reads v0.1 databases (without the
  **Trust** tab's tables) and warns about any other schema. Queries against missing tables may
  fail.
- The **Trust** tab is described in [trust-db.md](trust-db.md).
