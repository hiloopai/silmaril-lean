# GCC C torture suite: translation-validation manifest and status

Stage 4 of [C translation validation](../../docs/projects/c-tv.md). **The long-term goal**: every
in-scope torture test translation-validated by validators proved sound. **The current state** is
below, against the full denominator. Running examples here is not coverage, and no row is a
kernel theorem.

## The pinned suite

[`manifest.json`](manifest.json) pins GCC **14.3.0** at
[`c9cd41fb`](https://github.com/gcc-mirror/gcc/tree/c9cd41fba9ebd288c4f101e4b99da934bcb96a11/gcc/testsuite/gcc.c-torture).
It has the SHA-256 of all 3,901 files of `gcc/testsuite/gcc.c-torture/{compile,execute}`, and the
3,852 C cases among them are the denominator. The test sources are **not** stored here: they keep
their own copyright and licence (GPL-3.0-or-later, with the GCC Runtime Library Exception where a
file says so) in the pinned checkout. The inventory was generated from that checkout
(originally `benchmarks/gcc-torture/corpus.json` of hiloopai/moria-lean). Every file's SHA-256
was re-checked against a fresh sparse clone on 2026-11-17: 3,901/3,901 match.

```sh
git clone --filter=blob:none --sparse --depth=1 --branch releases/gcc-14.3.0 https://github.com/gcc-mirror/gcc.git /tmp/gcc
git -C /tmp/gcc sparse-checkout set gcc/testsuite/gcc.c-torture
lake build --wfail cerb-lean cfront ctv-pipeline
scripts/c-tv/torture.py --root /tmp/gcc/gcc/testsuite/gcc.c-torture --jobs 8
```

## Statuses (fifth run of 2026-11-17)

[`tv-report.json.gz`](tv-report.json.gz) has one row per case, the tool versions and the manifest's
SHA-256. Tools: gcc 14.2.0 (Debian), clang 19.1.7 (Debian), and `cerb-lean`, `cfront` and
`ctv-pipeline` built from this repository (their SHA-256s are in the report). Elapsed time:
335 s on 8 workers. Every case has exactly one status (`scripts/c-tv/torture.py`
defines them). `cross-validated` is a frontend agreement (Core to Core) with UB-free sources both
ways; one that rests on source undefined behaviour is `cross-validated-ub`, counted separately
(none in this run). An agreement with a route that accepted a construct it drops (an `asm` label, an attribute it does not show it keeps) is `cross-validated-blocked`: that route's Core does not correspond to the source (0 in this run; 239 cases have a blocked route in all). Between runs, a case near the 60-second timeout can move between statuses
(the previous run had 1,131 frontend- and 2,512 elaborator-rejected). In this run three cases moved from elaborator- to frontend-rejected because a route hit the tool output cap (`cfront` writes 960 MB of typed Ail for `compile/stuct.c`) or the 60 s tool timeout; the reason is recorded per route.

| Status | compile/ | execute/ | total |
| --- | ---: | ---: | ---: |
| `harness-needed` | 0 | 158 | 158 |
| `frontend-rejected` | 666 | 467 | 1133 |
| `elaborator-rejected` | 1264 | 1246 | 2510 |
| `no-main` | 46 | 0 | 46 |
| `gap` | 0 | 0 | 0 |
| `unknown` | 0 | 0 | 0 |
| `explored` | 0 | 0 | 0 |
| `cross-validated` | 2 | 2 | 4 |
| `cross-validated-ub` | 0 | 0 | 0 |
| `cross-validated-blocked` | 0 | 0 | 0 |
| `refuted` | 0 | 0 | 0 |
| `timeout` | 1 | 0 | 1 |
| `tool-error` | 0 | 0 | 0 |
| `not-attempted` | 0 | 0 | 0 |
| **denominator** | 1,979 | 1,873 | **3,852** |

Separate facts:

* `ubReached`: 0.
* `profileIncoherent` (`float`, `long double` or `wchar_t` in the typed Ail): 0.
* Core allows the pass observation (exit 0, no output): admitted 2, rejected 0, unknown 0.

The 4 cross-validated cases are trivial on this target:

* `compile/960218-1.c`: Cerberus route ≡ Clang route, endings {"exit": 0, "kind": "defined"}
* `compile/ddd.c`: Cerberus route ≡ Clang route, endings {"exit": 0, "kind": "defined"}
* `execute/ieee/fp-cmp-4e.c`: Cerberus route ≡ Clang route, endings {"exit": 0, "kind": "defined"}; Core allows the pass observation: {'cerberus': 'admitted', 'clang': 'admitted'}
* `execute/ieee/fp-cmp-8e.c`: Cerberus route ≡ Clang route, endings {"exit": 0, "kind": "defined"}; Core allows the pass observation: {'cerberus': 'admitted', 'clang': 'admitted'}

(`ieee/fp-cmp-4e.c` and `fp-cmp-8e.c` compile to `int main () { return 0; }` outside ia64-HP-UX.)
`no-main`: compile/ cases that elaborate but have no `main`. Their whole-program behaviour is
undefined, so the Core startup halts with the `error` "no startup function"; they are not
counted as gaps. All verdicts are compiled evidence (`ctv-pipeline`). `timeout`:
`compile/limits-externalid.c`.

## What blocks coverage, ranked

These counts are each route's first rejection reason, over the frontend- and elaborator-rejected
cases. They are the concrete port obligations of the roadmap:

**cerberus route** (first reason per case, frontend and elaborator):

| cases | reason |
| ---: | --- |
| 976 | expected a type specifier |
| 537 | elaborate: "defined-function variadics, noreturn or noninteger returns are not ported |
| 463 | elaborate: "statement form is not ported by the actual elaborator |
| 318 | use of undeclared identifier … |
| 288 | expected Silmaril.Cerberus.Frontend.Punct.semicolon |
| 171 | elaborate: "unsupported: binary operator outside scalar add/sub/mul/gt/eq |
| 101 | feature not yet supported: bit-fields |
| 94 | K&R declaration lists are rejected |
| 78 | elaborate: "unsupported: initialized local is not a direct arithmetic object |
| 62 | expected Silmaril.Cerberus.Frontend.Punct.rparen |
| 60 | expected a primary expression |
| 58 | elaborate: "unsupported: actual expression form is outside constants, object rvalues, scalar operations and no |

**clang route** (first reason per case, frontend and elaborator):

| cases | reason |
| ---: | --- |
| 839 | elaborate: "unsupported: unknown block location needs omitted upstream cursor information |
| 801 | elaborate: "defined-function variadics, noreturn or noninteger returns are not ported |
| 392 | elaborate: "statement form is not ported by the actual elaborator |
| 270 | elaborate: "unsupported: binary operator outside scalar add/sub/mul/gt/eq |
| 225 | clang: error: type specifier missing, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimpl |
| 92 | statement GCCAsmStmt is not supported yet |
| 58 | unknown typedef name __builtin_va_list |
| 58 | clang: error: '__malloc__' attribute takes no arguments |
| 52 | clang: error: parameter 'a' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int |
| 44 | elaborate: "unsupported: actual expression form is outside constants, object rvalues, scalar operations and no |
| 44 | elaborate: "unsupported: arithmetic operator is outside add/sub/mul |
| 43 | elaborate: "unsupported: global object is not a direct integer or pointer |

Reading the table:

* **Language profile.** The torture tests are written for GNU C with implicit `int`, K&R
  definitions and implicit declarations. The runner preprocesses and parses as `gnu11`. Clang 19
  then rejects implicit `int`, and Cerberus rejects implicit declarations and K&R lists, as C11
  requires. A `gnu89` profile, with its own coherence obligations, is the next language step.
* **Elaborator.** Defined variadic, `noreturn` and non-`int`-returning functions; non-`return`
  statements (loops, `if` with blocks); `/`, `%`, shifts and comparisons other than `>` and `==`;
  initialized non-arithmetic locals; `sizeof` of expressions; globals other than integers and
  pointers. These are the cases of upstream `translation.lem` still to transcribe.
* **Clang route.** It needs the cursor location the elaborator expects for blocks, which the
  Clang AST does not carry ("unknown block location"). It rejects `asm` statements and
  `__builtin_va_list`.
* **Harness.** 158 execute/ cases need DejaGNU behaviour (`.x` scripts, the builtins directory's
  extra sources) that the runner does not interpret.

## Highlights: the four cross-validated cases are not coverage

| Case | Why it is not coverage |
| --- | --- |
| `compile/960218-1.c` | **compile-only**: a compile/ test is about compiling; its evidence must be function-level (`c.compiles_to`, function-level contexts), and none exists for it yet |
| `compile/ddd.c` | **compile-only**, as above |
| `execute/ieee/fp-cmp-4e.c` | **architecture-gated**: `#if defined (__ia64__) && defined (__hpux__)` selects the test; on x86-64 it preprocesses to `int main () { return 0; }` |
| `execute/ieee/fp-cmp-8e.c` | **architecture-gated**, as above |

All four are frontend agreements only (Core to Core, compiled evidence): no per-type check passes
on them and no compiler-origin edge exists. The report flags `compileOnly` on every compile/ case
and `targetConditional` on the 35 cases whose source selects code with `#if` on a target macro;
the explorer's GCC torture page (C programs tab) highlights them. The 46 `no-main` compile/ cases
are the same function-level gap: they elaborate, but have no whole-program behaviour.

## How a run is pinned and checked

* Every case's source is hashed **during the run** and compared with the manifest
  (`sourceVerified`, `sha256` per row); a mismatch makes the case `not-attempted`.
* The report pins the manifest's SHA-256, the tools (gcc and clang versions; SHA-256 of
  `cerb-lean`, `cfront`, `ctv-pipeline`), every option (preprocessing, both routes, the pipeline's
  bounds, profile and elaborator, the native build) and the native caps.
* Every run (native tests and the tools: gcc, clang, `cerb-lean`, `cfront`, `ctv-pipeline`) is
  launched in its own session and process group, with stdin from `/dev/null`, under one wall-clock
  deadline that covers the whole lifecycle (its output, end of file, and the wait for the process);
  stdout and stderr are read with `select` up to caps (native: 1 MiB and 64 KiB; tools: 512 MiB and
  4 MiB). On a deadline or a cap, and after a normal end too, the whole group is killed, so no child
  outlives the run; a descendant that starts its own session escapes, and nothing detects it.
* Native test runs also have resource limits (10 s of CPU, 1 GiB address space, 16 MiB files, no
  core), applied by an exec wrapper rather than `preexec_fn` (the runner launches from worker
  threads). The report records how each run ended: `exit`, `signal`, `cpu-limit` (SIGXCPU, or
  SIGKILL with the CPU time at the limit), `fsize-limit` (SIGXFSZ), `timeout`, `stdout-limit`,
  `stderr-limit` or `build-failed`; the code (exit status, or the signal number, also for a
  limit, as its evidence); the CPU time; whether members of the group were alive after the program
  ended; and the stdout's size and SHA-256. Stdout is never parsed. An address-space limit has no
  signal of its own: a program whose allocation fails is reported by whatever it then does.
* `scripts/c-tv/check-torture.py` checks the manifest and report invariants without a GCC
  checkout: 3,852 unique cases, one row per case in manifest order, statuses summing to the
  denominator, every attempted row verified, pinned tools/options/profile/caps, statuses agreeing
  with their rows' facts (both route pairs and both routes' endings for a cross-validation, UB for
  `cross-validated-ub`), typed flags, only known fields, the summary (statuses and flag counts)
  equal to the rows' counts. It runs in the CI helpers job (`scripts/test_c_tv_torture.py`, with
  tampered reports that must be rejected; `scripts/test_c_tv_native.py` exercises the runner) and
  in `make c-tv-check`. It does not authenticate the report: a forged but structurally valid
  report passes. The evidence for a status is the recorded run, repeatable with the pinned GCC
  checkout, tools and options.

## Gap roadmap

Every case of the denominator, by the first gap it hits, against the milestone that closes it.
The rows are disjoint and sum to the denominator. Even a case past every row needs milestone 7 (a
precise per-type check) and milestone 11 (compiler origin) before it is translation-validated.

| Gap | Roadmap milestone (docs/projects/c-tv.md) | Cases |
| --- | --- | ---: |
| Harness: DejaGNU `.x` options, builtins sources | 4 (runner) | 158 |
| Language profile: implicit `int`, K&R, implicit declarations (both routes) | 4, 6 | 763 |
| Frontend, other (asm statements, `va_list`, GNU extensions, VLAs, bit-fields, output caps, timeouts) | 6 | 370 |
| Elaborator: rest of `translation.lem` (functions, statements, operators, locals, globals) | 5 | 2,510 |
| Whole-program behaviour undefined (compile/ without `main`) | 9 (function-level evidence) | 46 |
| Timeouts | 8 (validators beyond enumeration) | 1 |
| Cross-validated (frontend agreement, trivial) | then 7 (per-type check), 11 (compiler origin) | 4 |
| **total** | | **3,852** |

## What a status does not mean

* `cross-validated` is two frontends agreeing through one elaborator on the Core semantics. It
  is not a proof that the GCC-compiled program is correct, nor that either frontend implements C.
* The native runs are sanity runs of one build, not compiler validation.
* Coverage of a test needs, at least: its whole-program Core (both routes, or one route plus a
  semantic edge from the source); an exhaustive, supported exploration; a profile coherent at its
  types; and an edge to the compiled object (stage 5 and later, through the ABI and ELF work).
