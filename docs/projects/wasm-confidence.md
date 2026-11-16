# Confidence that silmaril-lean's Wasm semantics match the Wasm specification

A roadmap, and the state of its first slice ([WAST rows](wasm-wast.md), PR #843). Grounded in
`main` at `5170984b` plus #843.

Testing never proves universal soundness: it establishes agreement on the cases tested.
Universal claims come only from the simulation and refinement theorems in the
[bridge matrix](#1-bridge-matrix-implementation-to-specification). A WAST row is a theorem about
silmaril-lean's Core semantics on one command; an oracle result is agreement of an independent
implementation on one script.

## 1. Bridge matrix: implementation to specification

| implementation / translation | universal theorem status | external oracle (pinned) |
|---|---|---|
| SpecTec spec (Wasm 3.0, `608711107b`) → `Execution.Core` relational `Step` | **partial**: both directions on typed, `BoundedSelM`, no-memory-SIMD configurations with a finite `HostOk` host (`wholeStepValidRMNoMSH_backend`); the whole-step goals `Task.wholeStep` / `Bwd.Task.wholeStepUpTo` are open | the spec test suite at `608711107b`: 1140 commands of 6 files run (§2) |
| SpecTec Wasm 1.0 → V1 | **both directions proved** at `fwdB10` (`wholeStep10_both`) | — |
| SpecTec Wasm 2.0 → V2 | forward only, partly (`wholeStepVec`); `Task.wholeStepValid` and the backward goals are open | — |
| `SingleThreaded.stepI` / `runInvoke?` interpreter → `Step` | **sound and complete** (`interpHead_sound`, `HeadExact`, `runInvoke?_sound`, `runInvoke?_complete`) at `profile o` (deterministic, canonical NaNs, grow oracle) | wasmtime 50.0.0 on the WAST slice: 1140/1140 kernel-proved commands agree |
| `runInvokeK` (kernel-evaluable) | `runInvokeK_eq : runInvokeK o = runInvoke? o` | — |
| `scriptKM` (kernel checker on `KMem` stores) → `scriptK` | `scriptK_of_scriptKM`, from `instantiateOnce?_toBytes`, `runI_toBytes` (#796) | — |
| WAST script commands → `Step` (#843) | **per command, proved**: `ScriptHolds.of_kernel` (or `ScriptHolds.of_kernelKM`, for modules with data segments) turns one `decide +kernel` run of `scriptK` (`scriptKM`) into `ReturnsOnly`/`TrapsOnly` for every command of a module; `ScriptHolds.always` adds termination (§3) | wasmtime 50.0.0 (§4) |
| `Profile.deterministic` vs `Profile.spec` | canonical NaNs refine the spec's NaN sets (`floatUnOpP_canonical_spec`, …); determinism (`Internal.deterministic`, `Det.DStep.join'`, `reach_normal_unique`) only at `profile o` | — |
| Binaryen interpreter / `wasm-shell` | **open** (`FwdSim`/`BwdSim` unproved; fragments in `Wasm/Interp`) | wasm-opt release suites (tested) |
| Component IR `Comp.denU`/`denI` ↔ REF (reference machine) | `Simple.sound` (import-free numeric); session adequacy with imports on a fragment (#805, open); start comparison on 3 litmus components (#827, open) | wasmtime 50.0.0, wasm-tools 1.262.0, jco 1.39.0 (not run in CI) |
| REF (Lean transcription of `definitions.py` @ `a25fc0b`) | a transcription, **not** an independent authority | component-model test suite (not vendored) |
| KMem evaluator (#796, open) | `stepI_toBytes`, `runI_toBytes`, `instantiateOnce?_toBytes`, engine simulation, REF transfer: unconditional in #796; used by the WAST checker `scriptKM` | — |

Tool correctness (decoder, validator, encoder, WAST parser) is a separate axis. The decoder is
sound (`decode?_sound`), not complete. Validator and WAST-parser theorems are listed in
[wasm-tools-trust.md](wasm-tools-trust.md). Agreement with upstream tools is tested, not proved.

## 2. The first slice: denominator, pins, skips

**Pins.**

| input | pin | SHA-256 |
|---|---|---|
| spec test suite | WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36` (codeload archive; `tools/wasm-tools/tests/pins.sh`) | archive `22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b` |
| converter | wasm-tools 1.262.0 `json-from-wast` | archive `655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65`, binary `fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211` |
| oracle | wasmtime 50.0.0 (`ebe5e8df1 2026-10-20`; `tools/wasm-jco/tests/pins.sh`) | archive `77c19ee0437991f9ac7837b9c269d9c7076744f85dad263fea5214cc2723c7ff`, binary `f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7` |

**Denominator.** Every command after a `module` command of `test/core/{i32, i64, int_exprs, fac,
traps, address}.wast`: **1258 commands**. `module` commands themselves are not counted.

| file | commands | proved | unsupported | undetermined |
|---|---|---|---|---|
| `i32.wast` | 459 | 374 | 85 | 0 |
| `i64.wast` | 415 | 384 | 31 | 0 |
| `int_exprs.wast` | 89 | 89 | 0 | 0 |
| `fac.wast` | 7 | 6 | 1 | 0 |
| `traps.wast` | 32 | 32 | 0 | 0 |
| `address.wast` | 256 | 255 | 1 | 0 |
| **total** | **1258** | **1140** | **118** | **0** |

By assertion: `assert_return` 1025 proved (`returns_only`); `assert_trap` 115 proved
(`traps_only`); `assert_invalid` 113, `assert_malformed` 4 and
`assert_exhaustion` 1 unsupported. No command was a mismatch, and none ran out of fuel (100 000
steps per call).

**Skip reasons.**

| count | status | reason |
|---|---|---|
| 113 | unsupported | `assert_invalid`: needs validator completeness; no shape |
| 4 | unsupported | `assert_malformed` (text): no shape |
| 1 | unsupported | `assert_exhaustion` (`fac.wast`): resource exhaustion is not modelled |

"Undetermined" never means the implementation failed: it means no theorem was produced.

## 3. What each assertion claims, and how strong it is

Each row is stated over: the module (valid, no imports, no start function, instantiated from the
empty store); the actions of all earlier commands of the same module, threaded through their
final stores (also after a trap); `profile o` with `o = neverFail`; no host functions.

| assertion | shape and strength | status |
|---|---|---|
| `assert_return` (exact values) | `returns_only`: some host-free run returns `vs`, and **every host-free normal form** returns `vs`. Plus, by `ReturnsOnly.always`: no host-free run is infinite, and every finite run extends to a normal form returning `vs`. | 1025 proved |
| `assert_trap` | `traps_only`: same, with "is a trap"; the trap message is not part of the claim. `TrapsOnly.always` excludes divergence. | 115 proved |
| `assert_return` with `nan:canonical` / `nan:arithmetic` | needs an allowed-set shape under `Profile.spec`; uniqueness is not claimable (NaN payloads are nondeterministic in the spec) | no shape; none in this slice |
| `assert_exhaustion` | unsupported: stacks are unbounded in the model | 1 skipped |
| `assert_invalid` | needs validator completeness for `¬ ∃ t, Valid m t`; otherwise only "the validator rejects", labelled as weaker | no shape |
| `assert_malformed` | binary: "the decoder rejects" (weaker than grammar rejection while `decode?` is only sound); text: WAT parser rejection | no shape |
| `assert_unlinkable`, `assert_uninstantiable` | instantiation fails at import matching / traps during start or initialisation | no shape |
| `register`, `get`, named modules | script-state transitions | not in the fragment |

**Wording.** The `…_only` statements quantify over normal forms only: "every normal outcome is
`r`". That no run diverges is a separate theorem, proved for every row:
`Reaches.always : Reaches o m pre act r → Always o m pre act r`, from the one-step diamond
(`Det.DStep.join'`) and the strict decrease of code size on a non-trivial peak
(`Det.DStep.shrink`). It is a property of `profile o`; it is not claimed under `Profile.spec`.

**Script state.** A row is relative to the actual run of the earlier actions, not to their
expected outcomes. Earlier assertions are their own rows; a later row does not assume them, but
its existence part does require every earlier action to end at a result, and at `profile o` the
earlier actions leave exactly one state (`ScriptAt.unique`).

Every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound`.

## 4. External-oracle trust boundary

An oracle result is **test-wise agreement**: wasmtime 50.0.0, given one script, accepted it.
It is not a proof, it is not checked by Lean, and it says nothing about commands that were not
run. What it adds is independence: an implementation not derived from silmaril-lean's semantics
gives the same outcome as the kernel-checked row on 1140 of 1140 commands.

What is trusted when reading `examples/wasm-wast/oracle.json`:

* that the binary with SHA-256 `f95e5b…` is wasmtime 50.0.0 as released (the archive SHA-256 was
  recorded on 2026-11-09 from the GitHub release asset; `fetch-wasmtime` re-checks both);
* that `wasmtime wast` implements the WAST assertions as specified (in particular, an
  `assert_trap` passes on any trap, whatever its message, as in the rows);
* that the script given to wasmtime is the one whose SHA-256 is recorded, and that it encodes
  the row's command: the same module binary, the same earlier actions, the same command. `gen.py
  verify --scripts` regenerates every script and compares its SHA-256; it checks consistency
  of the record, not wasmtime's verdicts;
* the machine that ran it (`host`, `generated_at`): verdicts are only re-obtained by running
  `gen.py oracle` again.

What the oracle does **not** cover: whether Core is the specification (§1), the commands left
out (§2), the spec profile's nondeterminism (wasmtime picks one NaN payload, one grow outcome),
and the binaries themselves (both sides read wasm-tools' output for the text).

## 5. A bounded CI oracle job (proposal)

No CI workflow is changed by #843; this is a proposal for a separate, authorised change.

**Job.** On pull requests touching `tools/wasm-wast/**`, `examples/wasm-wast/**` or the pins
files, and on the nightly schedule:

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec   # spec archive and wasm-tools, SHA-256 checked
python3 -I tools/wasm-wast/gen.py fetch-wasmtime       # wasmtime archive and binary, SHA-256 checked
python3 -I tools/wasm-wast/gen.py convert
python3 -I tools/wasm-wast/gen.py verify --scripts     # the committed record is consistent
python3 -I tools/wasm-wast/gen.py oracle               # re-run wasmtime
python3 -I tools/wasm-wast/gen.py verify --scripts
git diff --exit-code -I '"generated_at"' examples/wasm-wast/oracle.json  # same verdicts
```

It needs no Lean build: the scripts come from the committed `report.json` and the converted
JSON. The kernel rows are checked by the existing Lean build.

**Cost** (measured on one core of the development machine):

| step | size / time |
|---|---|
| downloads | spec archive 15.0 MB, wasm-tools archive (binary 20.4 MB), wasmtime archive 11.7 MB (binary 68.0 MB); `fetch-wasmtime` took 1.4 s here |
| `convert` | 0.15 s (6 files, 295 KB of JSON and binaries) |
| `oracle` | about 10 s: 1140 scripts plus the 6 unmodified upstream files |
| `verify --scripts` | under 1 s |

So the job is bounded at well under a minute plus runner start-up, and about 35 MB of downloads
(cacheable by SHA-256). The risk is network dependence on GitHub release assets; a cache keyed
by the pinned SHA-256 removes it after the first run. A failed verdict should fail the job; a
changed `report.json` without a regenerated `oracle.json` fails `verify`.

## 6. Staged acceptance criteria

| stage | scope | acceptance criterion | state |
|---|---|---|---|
| S0 | the slice of §2 | every command counted with a status and reason; every proved row a kernel theorem with termination; oracle 100 % agreement on executed commands; provenance verifiable | **met** in #843 (885 proved, 885/885 agree); with the `KMem` checker, 1140 proved, 1140/1140 agree |
| S1 | numeric scripts (`i32`, `i64`, `f32`, `f64`, `conversions`, `int_exprs`, …) | ≥ 95 % of `assert_return`/`assert_trap` commands kernel-checked at `profile o`, NaN-pattern results as allowed-set claims under `Profile.spec`; every skip classified; oracle agreement 100 % on executed ones | `i32`, `i64`, `int_exprs`: 100 % of their 847 `assert_return`/`assert_trap` commands proved; floats and conversions not started |
| S2 | memory, tables, control (`address`, `memory*`, `br*`, `call*`, `traps`) | the same; data segments in the kernel (KMem, #796); `assert_unlinkable`/`assert_uninstantiable` shapes | `traps`, `fac` and `address` proved (`address` on `KMem` stores, `ScriptHolds.of_kernelKM`); the other files not started |
| S3 | validation (`assert_invalid`) | validator completeness proved, or claims labelled tool-level; 100 % of commands accounted for | not started (113 counted) |
| S4 | decoding (`assert_malformed` binary) | decoder rejection kernel-checked; completeness or an explicit weaker label | not started |
| S5 | SIMD, relaxed SIMD, GC, exceptions, tail calls, memory64, multi-memory | per-proposal pass/skip counts; nondeterministic results as allowed-set claims | not started |
| C1 | component-model WAST suite (pinned) on REF | per-file PASS/FAIL/UNSUP counts as JSON, shown in the explorer; agreement with wasmtime 50 | not started |
| C2 | components with lists, strings, resources | IR/REF adequacy extended | in progress (#805, #827) |

CI budget per stage: kernel time is per generated module (here 33 s to 62 s each, and 133 s with
9.3 GB peak RSS for `address.wast` on `KMem`), so shard by
file; the oracle job of §5 grows linearly with the number of scripts (about 9 ms each).

## 7. Highest-risk caveats

1. **SpecTec ↔ Core 3.0 whole-step** simulation is open. Rows are proved against
   `Execution.Core`, not against the spec transcription. Closing `Task.wholeStep` is the top
   priority for "equivalent to the specification".
2. **Profiles:** uniqueness and termination are proved only at `profile o`. NaN payloads, relaxed
   SIMD and grow failure are nondeterministic in the spec and need allowed-set claims.
3. **Hosts:** rows are host-free; the spectest host and imports are not in the fragment.
4. **Resource exhaustion** and stack overflow are not modelled.
5. **Validator and decoder completeness** are not proved, which weakens `assert_invalid` and
   `assert_malformed`.
6. **Components:** REF is a transcription, not an independent oracle; IR↔REF adequacy is
   fragmentary; the external oracles are not run in CI.
7. The **Binaryen interpreter** is unverified; `wasm-shell` agreement is tested only.
