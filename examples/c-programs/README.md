# C programs through the translation-validation pipeline

Stage 2 of [C translation validation](../../docs/projects/c-tv.md). Each directory holds one
program and every representation the pipeline produced for it, with its provenance. They are
written by `scripts/c-tv/corpus.py`.

`make c-tv-check` (part of `make check`) is a **reproducibility check**: a fresh run of
`ctv-pipeline` on the stored typed Ail and observations must give the stored reports and Core
documents. Its "reproduced 24 of 24" means the stored reports are reproducible, not that 24
programs are validated. It needs neither gcc nor clang.

| File | Stage | Producer | Evidence kind (`TV.Provenance`) |
| --- | --- | --- | --- |
| `source.c` | source | input (`src/<name>.c`) | — |
| `preprocessed.i` | preprocessed | `gcc -E -P -std=c11` | `external` |
| `clang-ast.json.gz` | Clang AST | `clang -x c -std=c11 -target x86_64-linux-gnu -Xclang -ast-dump=json -fsyntax-only` on `preprocessed.i` | `external` (untrusted frontend output) |
| `cerberus.tail.sexp` | typed Ail | `cerb-lean parse --level tail` (the Lean port of Cerberus's frontend) | `compiled` |
| `clang.tail.sexp` | typed Ail | `cfront ail` (fail-closed Clang JSON importer) | `compiled` |
| `<route>.core.sexp.gz` | Core | `ctv-pipeline`: `Elaboration.Functions.elaborate`, `TargetCoherence.linuxLP64`, Cerberus's runtime maps | `compiled` |
| `native-O0.out`, `native-O2.out` | observation | gcc builds of `source.c`, run once | sanity runs, not validation |
| `report.json` | — | `ctv-pipeline run`: explorations, `TV.validate` both ways, `Spec.check` on the observations | `compiled` |
| `provenance.json` | — | every artifact (SHA-256 of the exact bytes; of the uncompressed bytes for `.gz`), its producer and inputs, the edges with their evidence, failures, constructs a route dropped, warnings | — |

A stage that fails leaves its artifact absent and is listed under `failures`. Constructs a route
accepts while dropping them are listed under `losses`, each marked **blocking** or not:

* **Blocking**: the route's typed Ail, and its Core and verdicts, no longer correspond to the
  source. The Cerberus route drops `__asm__` labels and registers (as upstream's `c_parser.mly`
  does), so in `asm-label` that route's Core does not represent the source's assembler name; any
  attribute a route accepts without showing that it keeps it (calling convention, layout, linkage,
  section) is blocking too. A blocked route's edges in `provenance.json` carry
  `sourceCorrespondence: blocked`, and the explorer shows it in red.
* **Not blocking**: `cfront` drops `used`, `unused`, `deprecated`, `noinline` and `always_inline`
  (they request diagnostics or inlining only) and rejects the attributes it does not handle,
  `asm` labels among them; `aligned` and `mode` it handles.

`cfront` writes `cfront-clang 23.1.0 …` into its documents whatever clang produced the AST (a
separate fix, #919, removes that self-report). The pipeline never trusts it: it records the clang
that actually ran (here Debian clang 19.1.7) in `tools.clang` and warns on a mismatch.

## What the verdicts mean

Three different things must not be confused. A **route agreement** here is computed by compiled
Lean code (`ctv-pipeline`): it is neither a kernel proof (the kernel-checked rows are separate
and registered) nor evidence that either frontend implements C. Every verdict here is computed by compiled Lean code. It is backed by `TV.validate_sound`,
`TV.validate_refuted` and `Spec.check_sound` / `Spec.check_complete` only up to the Lean compiler
and runtime that ran it. These are not kernel-checked instances: the Cores carry Cerberus's
complete runtime library. `cerberus → clang: validated` means that the clang route's Core
refines the Cerberus route's Core: every observation of the one is an observation of the other,
the clang route's Core reaches no gap or stuck state, and it terminates. "Both ways" is
equivalence. This is a translation validation of the two frontends against each other through
the same elaborator. It is not a proof that either frontend implements C. `gcc -O0 exit 37:
admitted` means that the exit status and stdout of one run of the gcc binary are an observation
the Core allows (`Spec.check`). That is one execution of one build, not a compiler correctness
result.

`provenance.json` names the profile `linuxX86_64` (`Silmaril.Project.Shapes.CTV`): a label for
the target the pipeline is configured for, not a check. The check is per route and per type, on
the Core reachable by name: `report.json`'s `applicability` lists the types the route's Core
names (its own code, the runtime functions and implementation constants it reaches) and the
blockers. It fails on every program here, because Cerberus's runtime conversion functions they
reach name the floating types even on integer-only paths; the check is conservative, necessary
and not sufficient, and no row here describes x86-64 Linux C.

A verdict that rests on source undefined behaviour is labelled "only through source UB" and has
its own status (`agreement-ub-only`); it is never counted with defined-source agreements.

Clang's JSON AST names nodes by their in-memory addresses (`"id": "0x…"`), so it differs between
runs: its SHA-256 identifies this run's dump, not a reproducible output.

<!-- corpus tables: generated by scripts/c-tv/corpus.py; edit above this line -->

## The corpus (24 programs)

### One status per program

The statuses are disjoint: every program has exactly one, and the counts sum to 24.

| Status | Meaning | Count | Programs |
| --- | --- | ---: | --- |
| `frontend-rejected` | no route produced typed Ail | 0 |  |
| `elaborator-rejected` | typed Ail from some route, Core from none | 11 | `control-flow`, `division-by-zero`, `float`, `globals`, `locals`, `pointer`, `recursion`, `signed-overflow`, `statement-expression`, `unsequenced-calls`, `unsequenced-ub` |
| `single-route` | Core from exactly one route (the other rejected at its frontend or elaborator) | 3 | `asm-label`, `attribute`, `local-if` |
| `agreement-ub-free` | Core from both routes; each refines the other (TV.validate, compiled) with a UB-free source both ways (validateUBFree) | 9 | `arithmetic`, `calls`, `compare`, `nested-calls`, `return-constant`, `sign-extend`, `signed-narrow`, `unsigned-parameter`, `unsigned-wrap` |
| `agreement-ub-only` | Core from both routes; each refines the other, but some exploration reaches undefined behaviour | 1 | `overflow-return` |
| `other` | Core from both routes, any other verdict (refuted, unknown, unsupported) | 0 |  |
| **total** | | **24** | |

Separately, 1 program(s) have a route whose source correspondence is **blocked** by a construct it dropped (`asm-label`): that route's typed Ail, Core and verdicts are not about this C program (see `losses` in `provenance.json`).

### Stage reached, per route

Each column counts every program once, so each sums to 24.

| Stage reached | Cerberus route | Clang route |
| --- | ---: | ---: |
| rejected by the frontend (no typed Ail) | 2 | 1 |
| typed Ail, rejected by the elaborator | 10 | 12 |
| Core | 11 | 11 |
| Core, source correspondence blocked | 1 | 0 |
| **total** | **24** | **24** |

### Programs

| Program | Status | Cerberus route | Clang route | Route agreement (compiled) | Native runs (sanity) | Dropped by a route |
| --- | --- | --- | --- | --- | --- | --- |
| `arithmetic` | `agreement-ub-free` | Core: defined 37 (per-type check fails) | Core: defined 37 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 37: cerberus admitted, clang admitted; gcc-O2 exit 37: cerberus admitted, clang admitted |  |
| `asm-label` | `single-route` | Core: defined 7 (per-type check fails) — **source correspondence blocked** | rejected by the frontend (no typed Ail) | — | gcc-O0 exit 7: cerberus admitted; gcc-O2 exit 7: cerberus admitted | cerberus drops asm label or register (**blocking**) |
| `attribute` | `single-route` | rejected by the frontend (no typed Ail) | Core: defined 42 (per-type check fails) | — | gcc-O0 exit 42: clang admitted; gcc-O2 exit 42: clang admitted | clang drops attribute noinline (not blocking) |
| `calls` | `agreement-ub-free` | Core: defined 5 (per-type check fails) | Core: defined 5 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 5: cerberus admitted, clang admitted; gcc-O2 exit 5: cerberus admitted, clang admitted |  |
| `compare` | `agreement-ub-free` | Core: defined 2 (per-type check fails) | Core: defined 2 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 2: cerberus admitted, clang admitted; gcc-O2 exit 2: cerberus admitted, clang admitted |  |
| `control-flow` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 6; gcc-O2 exit 6 |  |
| `division-by-zero` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 signal 8; gcc-O2 signal 4 |  |
| `float` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 3; gcc-O2 exit 3 |  |
| `globals` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 5; gcc-O2 exit 5 |  |
| `local-if` | `single-route` | Core: defined 12 (per-type check fails) | typed Ail, rejected by the elaborator | — | gcc-O0 exit 12: cerberus admitted; gcc-O2 exit 12: cerberus admitted |  |
| `locals` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 17; gcc-O2 exit 17 |  |
| `nested-calls` | `agreement-ub-free` | Core: defined 42 (per-type check fails) | Core: defined 42 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 42: cerberus admitted, clang admitted; gcc-O2 exit 42: cerberus admitted, clang admitted |  |
| `overflow-return` | `agreement-ub-only` | Core: ub (per-type check fails) | Core: ub (per-type check fails) | cerberus->clang: validated (only through source UB); clang->cerberus: validated (only through source UB) | gcc-O0 exit 0: cerberus admitted, clang admitted; gcc-O2 exit 0: cerberus admitted, clang admitted |  |
| `pointer` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 3; gcc-O2 exit 3 |  |
| `recursion` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 20; gcc-O2 exit 20 |  |
| `return-constant` | `agreement-ub-free` | Core: defined 42 (per-type check fails) | Core: defined 42 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 42: cerberus admitted, clang admitted; gcc-O2 exit 42: cerberus admitted, clang admitted |  |
| `sign-extend` | `agreement-ub-free` | Core: defined -1 (per-type check fails) | Core: defined -1 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 255: cerberus admitted, clang admitted; gcc-O2 exit 255: cerberus admitted, clang admitted |  |
| `signed-narrow` | `agreement-ub-free` | Core: defined -56 (per-type check fails) | Core: defined -56 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 200: cerberus admitted, clang admitted; gcc-O2 exit 200: cerberus admitted, clang admitted |  |
| `signed-overflow` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 0; gcc-O2 exit 0 |  |
| `statement-expression` | `elaborator-rejected` | rejected by the frontend (no typed Ail) | typed Ail, rejected by the elaborator | — | gcc-O0 exit 6; gcc-O2 exit 6 |  |
| `unsequenced-calls` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 12; gcc-O2 exit 12 |  |
| `unsequenced-ub` | `elaborator-rejected` | typed Ail, rejected by the elaborator | typed Ail, rejected by the elaborator | — | gcc-O0 exit 3; gcc-O2 exit 3 |  |
| `unsigned-parameter` | `agreement-ub-free` | Core: defined 1 (per-type check fails) | Core: defined 1 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 1: cerberus admitted, clang admitted; gcc-O2 exit 1: cerberus admitted, clang admitted |  |
| `unsigned-wrap` | `agreement-ub-free` | Core: defined 2 (per-type check fails) | Core: defined 2 (per-type check fails) | cerberus->clang: validated (UB-free source); clang->cerberus: validated (UB-free source) | gcc-O0 exit 2: cerberus admitted, clang admitted; gcc-O2 exit 2: cerberus admitted, clang admitted |  |
