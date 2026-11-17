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

## Statuses (run of 2026-11-17)

[`tv-report.json.gz`](tv-report.json.gz) has one row per case, the tool versions and the manifest's
SHA-256. Tools: gcc 14.2.0 (Debian), clang 19.1.7 (Debian), and `cerb-lean`, `cfront` and
`ctv-pipeline` built from this repository (their SHA-256s are in the report). Elapsed time:
346 s on 8 workers. Every case has exactly one status (`scripts/c-tv/torture.py`
defines them).

| Status | compile/ | execute/ | total |
| --- | ---: | ---: | ---: |
| `harness-needed` | 0 | 158 | 158 |
| `frontend-rejected` | 664 | 467 | 1131 |
| `elaborator-rejected` | 1266 | 1246 | 2512 |
| `no-main` | 46 | 0 | 46 |
| `gap` | 0 | 0 | 0 |
| `unknown` | 0 | 0 | 0 |
| `explored` | 0 | 0 | 0 |
| `cross-validated` | 2 | 2 | 4 |
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

## What a status does not mean

* `cross-validated` is two frontends agreeing through one elaborator on the Core semantics. It
  is not a proof that the GCC-compiled program is correct, nor that either frontend implements C.
* The native runs are sanity runs of one build, not compiler validation.
* Coverage of a test needs, at least: its whole-program Core (both routes, or one route plus a
  semantic edge from the source); an exhaustive, supported exploration; a profile coherent at its
  types; and an edge to the compiled object (stage 5 and later, through the ABI and ELF work).
