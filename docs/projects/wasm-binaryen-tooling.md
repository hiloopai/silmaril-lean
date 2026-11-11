# Binaryen tooling: wasm-opt stages, wasm-asyncify, wasm-check, wasm-egraph

Four tools for optimizing and checking WebAssembly Core modules. Each tool's core is a pure
Lean function with a correctness theorem; the command-line glue around it is not verified.
They extend the verified Binaryen-compatible tools in this repository (`wasm-as`, `wasm-dis`,
`wasm-opt`, `wasm-merge`, …), whose contracts are listed in
`tools/binaryen-lean/release-manifest.json`.

| Tool | What it does | Main guarantee |
| --- | --- | --- |
| `wasm-opt` with the extra stages | five more Binaryen-style rewrites and an opt-in SSA optimizer | exact export equivalence at every numerical profile |
| `wasm-asyncify` | Binaryen-style asyncify: unwinding to a shadow stack in linear memory | the transformed binary has the behaviours of the source program |
| `wasm-check` | refutes or proves equivalence and refinement of two modules, export by export; certifies whole optimizer runs | a `refuted` or `proved` verdict comes with a Lean certificate checked by the kernel |
| `wasm-egraph` | an untrusted e-graph search that prints proofs | its certificates are checked in Lean; nothing in the tool is trusted |

Build the Lean tools with Lake and `wasm-egraph` with Cargo:

```sh
lake build wasm-opt wasm-asyncify wasm-check
cargo build --release --manifest-path tools/wasm-egraph/Cargo.toml
```

## wasm-opt: extra stages

`wasm-opt` with none of the options below behaves exactly as before. These options add five
verified stages, each a restricted subrule of a Binaryen pass:

| Option | Rewrite | Binaryen pass |
| --- | --- | --- |
| `--neutral-ops` | `x op k` with a neutral constant (`x + 0`, `x * 1`, …) becomes `x` when an integer operator consumes it | `OptimizeInstructions` |
| `--eqz-pair` | `eqz (eqz c)` before `br_if`, `select` or `eqz` becomes `c` | `OptimizeInstructions` |
| `--rse-line` | `local.get x; local.set x` becomes `local.get x; drop`; a self-tee becomes a get | `RedundantSetElimination` |
| `--drop-get` | `local.get x; drop` becomes `nop` | `Vacuum` |
| `--tee-form` | `local.set x; local.get x` becomes `local.tee x` | `SimplifyLocals` |

The stage names also work inside `--passes`. `--verified-stages` expands each `-O*` preset to the
preset followed by these stages after every `optimize-instructions` slot. `--stats` reports
sizes and how often each stage changed the module; it uses an unverified replay, for
reporting only. `Wasm/Binaryen/Coverage/Defs.lean` lists every pass of Binaryen's default
`-O2`/`-Os` pipelines with its status: verified here, verified in a restricted form, or
missing.

**Guarantee.** For every selection of stages and every number of rounds, the output module
is valid and, for every export, has exactly the behaviours of the input, at every numerical
profile, under the closed host: `extraSelectedCompatBytes_sound_exact` and
`extraSelectedCompatBytes_valid` (`Wasm/Binaryen/Pipeline/Thms.lean`). Each stage's own
theorem is in its topic (`NeutralOps`, `EqzPair`, `RseLine`, `DropGet`, `TeeForm`). On this
path, the growth-policy options of `wasm-opt` (`--mode`, `--*-grow-*`) are rejected.

### The SSA stage (`--ssa`)

`--ssa` (or `ssa` in `--passes`) is opt-in and never part of a preset. It translates each
function in its fragment to a typed lambda-SSA intermediate representation, optimizes it
there, translates it back, and keeps the result only if a run-time certificate check
succeeds.

- **Fragment.** Modules without imports. Only store-free integer functions are rewritten;
  every other function is left unchanged.
- **Guarantee.** Exact export equivalence at every numerical profile (`ssaRun_exportEquiv`,
  through the caller-side simulation `behaviours_srel`). With `--ssa` alone,
  `ssaOnlyCompatBytes_sound` adds, for each rewritten function, fragment equivalence and equal
  Core 3.0 behaviours of its invocations.
- **Clean-up.** Follow it with clean-up stages (for example `-O2 --tee-form --rse-line
  --drop-get --vacuum`) to remove the locals and blocks that leaving SSA introduces.

The SSA library is under `Wasm/SSA`: the dialect, translation in and out, passes, and the
certificate checker. It is built on the lambda-SSA calculus under `SSA/Isotope/LambdaSSA`:
syntax, typing, operational semantics and determinism.

**Tests.** `node tools/binaryen-lean/wasm-opt-stages/test-peepholes.mjs .lake/build/bin/wasm-opt`
runs the stages under Node's WebAssembly engine and compares every export of the input and
output on 240 checks. `differential.mjs` and `analyze.mjs` compare with an installed upstream
`wasm-opt`.

## wasm-asyncify

```
wasm-asyncify asyncify IN.wasm -o OUT.wasm [--pages N] [--no-elide] [--selective]
wasm-asyncify run-src IN.wasm EXPORT ARGS [--fuel N]
wasm-asyncify run-tgt OUT.wasm EXPORT ARGS [--fuel N]
wasm-asyncify example NAME -o OUT.wasm
wasm-asyncify examples
```

`asyncify` rewrites a Core binary so that a blocking host call can suspend the program and
later resume it. The program saves its state to a shadow stack in linear memory and unwinds;
on resumption it rewinds. The transformation is Binaryen's asyncify design, restricted to an
`i32` fragment.

- **Default.** Statement form, otherwise operands are spilled to locals, and redundant
  re-entry checks are elided.
- **`--no-elide`.** The guarded form, statements only.
- **`--selective`.** Instruments only the calls that may suspend.
- **`run-src` and `run-tgt`.** Run the source and target models with a test host, so that
  the two can be compared on concrete inputs.

**Guarantee.** For every successful run on bytes, the input decodes to a well-formed source
program and the output encodes its asyncified version, with the same exports. For every
host, export and arguments within the depth bound, the source and target have equal
behaviours (results, traps and divergence): `asyncifyBytesW_correct`, `asyncifyBytes_correct`,
`asyncifyBytesE_correct` and `asyncifyBytesSel_spec`, under `Wasm/FX/Asyncify/Tool`. The
behaviours are those of the tool's source and target machines. The link from the target
machine to Core 3.0 execution is proved in the development tree, but conditionally on open
statements, so it is not part of this release.

**Tests.** `node tools/wasm-asyncify/differential.mjs .lake/build/bin/wasm-asyncify` compiles
the examples, runs source and target under Node with a host that suspends, and compares their
results: 34 of 34 runs agree.

## wasm-check

```
wasm-check refines IMPL.wasm SPEC.wasm EXPORT [--rel eq|trap] [--random N] [--lean FILE]
wasm-check equiv A.wasm B.wasm EXPORT [--rel eq|trap] [--random N] [--lean FILE]
wasm-check pass A.wasm B.wasm [--random N] [--lean FILE] [--lean-dir DIR] [--chunk K]
                [--egraph-tv TV.lean] [--egraph-tv-seg FILE] [--wat A.wat B.wat]
wasm-check bench [--random N] [--out DIR]
```

`wasm-check` compares two Core modules export by export, for start-free modules with scalar
function imports and exports. It returns one of four verdicts:

- **`refuted`:** a counterexample found by differential testing on the verified interpreter.
- **`proved`:** equal function summaries, or an e-graph certificate.
- **`identical`.**
- **`unknown`.**

`pass` checks every shared function export, as for an optimizer pass with input `A` and
output `B`, and prints one JSON report per export.

**Guarantee.**

- A `refuted` verdict is a refutation of refinement, or of equivalence
  (`checkRefinesBase_refuted`, `checkEquivBase_refuted`, `checkRefines_refuted`).
- A `proved` verdict proves `ModEquiv` at every profile (`checkRefines_proved`,
  `checkEquiv_proved`, `modEquiv_of_checkAmong`).
- With `--lean FILE`, the verdict is written as a Lean certificate. The certificate embeds
  both modules and proves the statement by kernel evaluation. Checking it with Lean makes the
  verdict independent of the compiled tool.
- With `--wat`, the certificate is about the modules of the WAT texts. That those are the
  modules of the binaries is not checked by the kernel.
- `ModEquiv` observes one invocation of an export: its result or trap. Changes to globals
  and memory are not observed.

**Tests.** `tools/wasm-check/tests/bench.sh` checks the pinned inputs against their SHA-256
sums. It then runs the built-in benchmark cases and the pinned module pairs, and compares
every verdict with `tests/expected.tsv`. With `--certs`, it also replays the certificates of
the refuted pairs in Lean.

The checking library is under `Wasm/Auto`:

| Topic | Contents |
| --- | --- |
| `Front` | the front end (both the core and the extended checker) |
| `Bridge` | function summaries, extended and segment summaries included |
| `Equiv` (extended and control-flow rules included) and related topics | symbolic execution and equivalence of segments |
| `EGraph`, `Rules`, `ESeg` | the rule library and the certificate checker of `wasm-egraph` |
| `VCGen`, `VCGen2`, `VCSmt` | a reflective verification-condition generator with one soundness theorem each |

Its tests and benchmarks are the Lake library `WasmAutoTests` (`tests/wasm/auto`).

## wasm-egraph

`wasm-egraph` (Rust, standard library only) searches for equalities of straight-line integer
Wasm code with an e-graph over the verified rule library (`Wasm/Auto/Rules`). It prints Lean
certificates, which the checker in `Wasm/Auto/EGraph` validates by `decide +kernel`. Nothing
in the tool is trusted. It also performs translation validation of optimizer runs (`tv`,
`tv-seg`). See [its README](../../tools/wasm-egraph/README.md).

**Tests.** `tools/wasm-egraph/tests/run.sh` runs the unit tests and the corpus. It checks the
translation validation of the pinned optimizer runs: 121 of 122 functions in the first set,
and 640 of 640 with effect summaries. The pinned runs are outputs of Binaryen version_123's
`wasm-opt`; see `NOTICES/Binaryen`.

## Command-line specifications

The command lines of `wasm-asyncify` and of the extra `wasm-opt` options are read by
grammars under `Cli`: `Cli/Spec/Asyncify` and `Cli/Spec/WasmOpt`.
`Cli.Clap.Tool.main_refines` states that a program run through such a grammar refines the
grammar's specification: help, usage errors with exit status 2, and dispatch of the parsed
matches.

## Foundations

These tools use the following parts of the library:

- **The program logic** (`Wasm/Logic`): Hoare-style rules, instruction by instruction, for
  the every-run logic used by `wasm-check`.
- **Games** (`Games`, `Wasm/Game`): the module-level semantics of instantiation and export
  calls behind `ModEquiv`.
- **Function-level institutions** (`Wasm/FnInst`, over `Logic/Inst`): the logics of the
  optimizer rules and their translations.
- **The specification library** (`WasmSpec`): the entries used by the `wasm-check`
  benchmarks.

## Trust boundary

- **Proved.** The theorems named above, about the pure function each tool runs.
- **Tested, not proved.** Agreement with upstream Binaryen; the Node differential suites;
  the `--stats` replay.
- **Not verified.** The command-line glue (reading and writing files, argument dispatch,
  report printing) of the four tools; the SMT-LIB printer of `VCSmt`; the Rust e-graph
  search (its results are checked); and the `partial def`s in the closure, listed in the
  release report of the candidate.
- **Trusted.** Lean's kernel, compiler and runtime.

None of these modules uses `sorry`, declares an axiom or trusts compiled code in a proof.
