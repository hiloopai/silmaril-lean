# SQLite source and dependency atlas

The atlas inventories the SQLite 3.54.1 library amalgamation using Rust and
libclang. Python stages the upstream archives, runs the Clang and GCC profile
checks, joins the AST with the source tree and renders the report.

[Measured summary](summary.md) · [Aggregate JSON](measurements.json) · [SQLite release notes](https://sqlite.org/releaselog/3_54_1.html)

## Regenerate

Use native x86-64 Linux with Python 3.10 or newer, Rust and Cargo, Clang 19 and
the matching libclang development package, GCC, glibc headers and `nm`.
The reference run used Debian 13 with Clang and libclang 19.1.7 (Debian
3+b1), GCC 14.2.0-19, glibc 2.41-12+deb13u5, Python 3.13.5 and Rust
1.100.1. For a Debian 13 environment, install the native dependencies with
`apt-get install clang-19 libclang-19-dev gcc libc6-dev binutils python3 ca-certificates`.

From the repository root:

```sh
export LIBCLANG_PATH=/usr/lib/llvm-19/lib
cargo test --locked --manifest-path reports/sqlite/atlas/Cargo.toml
python3 reports/sqlite/atlas/generate.py --out /tmp/sqlite-atlas
python3 reports/sqlite/atlas/check.py /tmp/sqlite-atlas
diff -u reports/sqlite/atlas/summary.md /tmp/sqlite-atlas/summary.md
diff -u reports/sqlite/atlas/measurements.json /tmp/sqlite-atlas/measurements.json
```

Cargo uses the checked-in lockfile. `--cache DIR` retains the three downloads
under their upstream archive names and validates their digests on every run.
`--clang` and `--gcc` select driver executables. Exact output comparison
uses the same compiler and libc header versions. The generator records the
compiler flags and the SHA-256 of each driver’s `-E` output and sorted
`-dM -E` macro lines. The AST comes from libclang parsing the original
amalgamation with the recorded Clang flags and resource directory. GCC also
compiles the same source at `-O2`, links the smoke driver and checks the
profile at runtime. Compiler-conditioned branches can differ in this setup.

### Files

| File | Contents |
| --- | --- |
| `atlas.json` | Function rows, call sites, origins, headers, record layouts, profile and assertion probes |
| `public-tests.json` | Public `.test` and `.subtest` paths and first-pass matches |
| `measurements.json` | Aggregate counts, source archive digests and compiler profile evidence |
| `summary.md` | Rendered measurements, sample review and region priorities |

## Scope and interpretation

- A function ID is `sqlite-<release>/amalgamation/sqlite3.c@<line>:<column>:<identifier>`.
  Position is the physical Clang expansion position. The byte offset joins
  AST locations, and a separate spelling position is nullable for generated
  tokens. Equal names at different sites get distinct IDs. Different
  translation units would require distinct IDs. This profile has one SQLite
  translation unit and excludes the shell and separate extension builds.
- The section table retains the marker stack, stage file and matching canonical
  source path candidates. A unique basename is origin evidence at the file
  level. Generated code carries its generator inputs where identified.
  Stage files are from SQLite's pre-amalgamation bundle. The atlas uses the
  release amalgamation's physical coordinates for definitions and calls.
  Architecture confidence is high for a curated source-section mapping and
  low for a fallback. Classifications use the predominant section role.
- Direct edges require a named function at the callee operand and matching
  definition coordinates. Parentheses, implicit wrappers, and unary address
  and dereference operators preserve a named designator. Casts, conditional
  expressions and returned function pointers remain conservative unknowns.
  Out-of-unit inline bodies, declared-only symbols, compiler intrinsics and
  indirect sites have separate call classes. Indirect rows retain a referenced
  field or variable and the expression kind when available. Macro expansion may
  place several call cursors at the same physical point. AST call counts
  include syntactically present calls even when unevaluated, dead or later
  inlined. Function mentions include ordinary direct calls and other uses.
- Each row records selected C cursor counts, parameter shapes and immediate
  pointee constness, nonlocal object mentions, declaration evidence and
  referenced record layouts. Header dependencies are evidence from
  prototypes, types, declarations, or macro definitions. The translation
  unit's inclusion directives are available separately. Layouts are Clang
  sizes and alignments in bytes with field offsets and bit-field widths in
  bits, as available. Record references alone can arise from opaque handles
  or a callee's signature.
- Effect tags use syntactic indicators and the named boundaries in
  `classify.py`. A byte pointer signals possible buffer access. An object
  tag signals record usage. `pure_candidate` is a local scalar-leaf
  heuristic. Tags are review candidates and carry no guarantee about memory
  ownership, reachability, aliasing or side effects. The propagated sets
  union effect evidence across paths of one or more resolved SQLite edges.
  Cycles participate and unknown boundaries propagate. The purity candidate
  label stays local.
- Assertion counts are libclang macro expansion cursors for `assert`,
  `testcase`, `ALWAYS` and `NEVER`. They include no-op release expansions.
  The separate debug inventory adds `-DSQLITE_DEBUG=1` and matches by
  coordinate and name. These are source probes and have no execution or
  coverage interpretation. The public test inventory is a filename-based
  starting point. Running the upstream Tcl suite would require a separate
  SQLite testfixture build and harness. [SQLite testing overview](https://sqlite.org/testing.html)
