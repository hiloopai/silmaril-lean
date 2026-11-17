# Confidence that silmaril-lean's Wasm semantics match the Wasm specification

A roadmap, and the state of its first slice ([WAST rows](wasm-wast.md), PR #843, extended
since by the `KMem` checker, the tool-level rejection shapes, the CI oracle job, the float
files at the specification profile, linked scripts with imports and `register`, and the typed
`spectest` host with host-aware determinism). Grounded in
`main` at `5170984b` plus #843.

Testing never proves universal soundness: it establishes agreement on the cases tested.
Universal claims come only from the simulation and refinement theorems in the
[bridge matrix](#1-bridge-matrix-implementation-to-specification). A WAST row is a theorem about
silmaril-lean's Core semantics on one command; an oracle result is agreement of an independent
implementation on one script.

## 1. Bridge matrix: implementation to specification

| implementation / translation | universal theorem status | external oracle (pinned) |
|---|---|---|
| SpecTec spec (Wasm 3.0, `608711107b`) → `Execution.Core` relational `Step` | **partial**: both directions on typed, `BoundedSelM`, no-memory-SIMD configurations with a finite `HostOk` host (`wholeStepValidRMNoMSH_backend`); the whole-step goals `Task.wholeStep` / `Bwd.Task.wholeStepUpTo` are open | the spec test suite at `608711107b`: 8626 commands of 19 files run (§2) |
| SpecTec Wasm 1.0 → V1 | **both directions proved** at `fwdB10` (`wholeStep10_both`) | — |
| SpecTec Wasm 2.0 → V2 | forward only, partly (`wholeStepVec`); `Task.wholeStepValid` and the backward goals are open | — |
| `SingleThreaded.stepI` / `runInvoke?` interpreter → `Step` | **sound and complete** (`interpHead_sound`, `HeadExact`, `runInvoke?_sound`, `runInvoke?_complete`) at `profile o` (deterministic, canonical NaNs, grow oracle) only; **not** a description of the runs of `Profile.spec` (next rows) | wasmtime 50.0.0 on the WAST slice: 1140/1140 kernel-proved execution commands at `profile o` agree (CI, §5) |
| `runInvokeK` (kernel-evaluable) | `runInvokeK_eq : runInvokeK o = runInvoke? o` | — |
| `scriptKM` (kernel checker on `KMem` stores) → `scriptK` | `scriptK_of_scriptKM`, from `instantiateCfg?_toBytes`, `runI_toBytes` (#796) | — |
| `validate?` (validator) → `ModuleOk` (silmaril-lean's validation relation) | **sound and complete**: `validate?_sound`, `validate?_complete`, `validate?_isSome_iff` (unconditional) | wasmtime 50.0.0 rejects all 113 `assert_invalid` modules of the slice that `validate?` rejects |
| `ModuleOk` → SpecTec Wasm 3.0 validation rules | **open as a whole**: fragments only (`Instr30`: `nop`, `unreachable`, `drop` at bounded types; the empty module is the open `Task.emptyModuleOk`; `drop_nested`: `Instr_ok` is not reflected). So a validator rejection is invalidity relative to `ModuleOk`, not to the spec | the spec test suite's `assert_invalid` commands (113 in the slice) |
| `decode?` (decoder) → `Binary.Core.Encodes` | **sound only** (`decode?_sound`; `Binary.Core.functional`); completeness not proved | wasm-tools 1.262.0 binaries of the slice (all decode) |
| WAST `assert_invalid` → `ValidatorRejects` | **per command, proved, tool-level**: `ValidatorRejects.of_kernel` (one `decide +kernel` of `validatorRejectsB`); `ValidatorRejects.not_valid` adds "no module the bytes encode is `ModuleValid`" via `validate?_complete` | wasmtime 50.0.0 (§4) |
| WAST script commands → `Step` (#843) | **per command, proved**: `ScriptHolds.of_kernel` (or `ScriptHolds.of_kernelKM`, for modules with data segments) turns one `decide +kernel` run of `scriptK` (`scriptKM`) into `ReturnsOnly`/`TrapsOnly` for every command of a module; `ScriptHolds.always` adds termination (§3). **Instantiation is the specification's**: the script state `Instance P m s mi := (∃ xtE, ModuleOk m ⟨[], xtE⟩) ∧ ∃ c₀ c, Instantiate P Det.noHost (Game.importStore []) m [] c₀ ∧ c₀.frame.module = mi ∧ Steps P Det.noHost c₀ c ∧ c.code = [] ∧ c.store = s` (at `profile o`, and `Profile.spec nd r` for the float files): every global allocated as `$instantiate` allocates it, no renaming, no no-globals hypothesis. The checkers instantiate with `instantiateCfg?`: `instance_of_cfg : validate? m = some mt → mt.imports = [] → instantiateCfg? (Game.importStore []) m [] = some (c, mi) → c.code = [] → Instance P m c.store mi ∧ StoreOk c.store` (every `P`), `instance_unique` (at `profile o`), `instance_unique_nil` (no segments, no start: any profile), `instance_spec` (`profile o` to `Profile.spec nd {}`) | wasmtime 50.0.0 (§4) |
| `Profile.deterministic` vs `Profile.spec` | **existence, in general**: every `profile o` step is a `Profile.spec nd {}` step (`Step.deterministic_refines_spec`), so a deterministic run to a result is a spec run (`Reaches.spec`, `Returns.allowedExists`). **Every normal form and termination, for a fragment only**: for straight-line numeric functions (`local.get 0 … local.get (k-1); op`, `op` a scalar numeric instruction), at **every** profile, every host-free normal form of `$invoke` is a result of `NumericStep P` in the same store (`StraightLine.nf`), each such result is reached (`StraightLine.reaches`), and no run is infinite (`StraightLine.not_diverges`, `extends_nf`). Determinism (`Internal.deterministic`, `Det.DStep.join'`, `reach_normal_unique`) and interpreter completeness only at `profile o`; no general theorem describes all `Profile.spec` runs of other code (memory, control, NaNs reaching control) | — |
| WAST linked scripts (imports, `register`, named modules, `get`, module assertions) → `Step (profile o) Spectest.host`, the specification's `Instantiate`, `ExternAddrOk` | **per command, proved, relative to the concrete host `Spectest.host`**: `ScriptHolds.of_kernel : scriptHK o fuel cmds = true → ScriptHolds o cmds` (`….WasmWastHost`) turns one `decide +kernel` run per file into `host.returns_only`/`host.traps_only`/`host.uninstantiable` (every normal form of `Step (profile o) Spectest.host`, after every earlier module, `register` and action of the file) and `host.unlinkable`; `ScriptAt.unique` (one context, host-call log included), `ReturnsOnly.always` (no infinite run under the host, via `Steps.always_of_hostDet`), `Unlinkable.not_instantiate`, `LogIs.of_kernel` (the log); `ReturnsOnly.matching : ReturnsOnly o pre act vs → matchAll ps vs = true → ReturnsMatching o pre act ps` (`host.returns_matching`, the `(ref.func)` pattern). **Instantiation is the specification's**: `InstNF` (a module, or `assert_trap (module …)`) is `Instantiate (profile o) Spectest.host s₀ m xas c₀` run to a normal form under the host, so a segment trap and a start trap are both a trap of `c₀`, the script goes on with its (residual) store, and globals are allocated as `$instantiate` allocates them (no no-globals hypothesis, no address renaming). The checker's `instantiateCfg?` is related to it by `instantiateCfg?_sound : instantiateCfg? s m xas = some (c, mi) → ∃ c₀, Instantiate P host s m xas c₀ ∧ c₀.frame.module = mi ∧ Steps P host c₀ c` (valid module, typed imports), and `Instantiate` has one configuration (`instantiate?_evalConst_complete`); `InstNF.of_trap`: a segment trap of `instantiateT?` with residual store `s'` (`instantiateT?_trap_sound`) is the outcome `trap` in `s'`. Stores typed by `Game.instantiateCfg?_configOk` and `resolve?_ok`; host calls typed by `Ctx.fill_callout_typed`. Name resolution (`resolve?`) is the reference interpreter's script semantics, transcribed | wasmtime 50.0.0: 531/531 agree (one script per file) |
| WAST host references (`(ref.extern n)` arguments and results, `(ref.func)` patterns; reference interpreter `parser.mly` l. 1507–1537, `runner.ml` l. 402–417, 464–477 at `608711107b`) → Core `Ref.extern (Ref.host n)` and `WasmWastRef.Pat` | **a transcription, checked by reading, with a proved typing lemma**: `(ref.extern n)` = `Extern.ExternRef (Script.HostRef n)` upstream = SpecTec `REF.EXTERN (REF.HOST_ADDR n)` = Core `.ref (.extern (.host n))` (`RefOk.extern`, `RefOk.host`; no new runtime syntax). `invokeOkRB_sound : invokeOkRB s a args = true → InvokeOk s a args` (numbers of their parameter type, `(ref.extern n)` for `(ref null? extern)`); `matchAll_sound : matchAll ps vs = true → MatchAll ps vs` (`Pat.exact v`: `w = v`, i.e. `eq_ref` on host/extern/null references; `Pat.funcRef`: `∃ a, w = .ref (.func a)`, upstream `RefTypePat FuncHT`). Not modelled: `(ref.extern)` (upstream: any reference, null included), other type patterns, `either`, `(ref.host n)` and null arguments (none in the slice) | wasmtime 50.0.0 on the `global.wast`/`elem.wast` scripts; `regress/wrong-externref.wast` (`(ref.extern 2)` for `(ref.extern 1)`) and the `global.wast` line 241 mutant rejected |
| `instantiateT?` / `instantiateCfg?` (trap-aware instantiation) → `Instantiate` and `Steps` | **sound and complete**, any profile and host: `instantiateT?_trap_sound : instantiateT? s m xas = .trap s' → ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧ initSegmentsT? evalConst? c.store c.frame m = .trap s' ∧ Instantiate P host s m xas (c.withStart st) ∧ Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩` (valid module, typed imports); `instantiateT?_ok_sound`; `Game.instantiateT?_ne_fail_iff : instantiateT? s m xas ≠ .fail ↔ ∃ c, Instantiate P host s m xas c` (typed store); `instantiateCfg?_eq_none_iff`; `instantiateT?_toBytes`, `instantiateCfg?_toBytes` (`KMem`). Single allocation (`instantiateOnceT?`) with globals only up to the global-address embedding (`Game.instantiateOnceT?_trap_spec`); the scripts do not use it | `regress/wrong-segment-trap-state.wast` (a rolled-back memory) rejected; the mutant of `linking.wast` line 410 rejected |
| `spectest` (reference interpreter host module, `interpreter/host/spectest.ml` at `608711107b`) → `Spectest.host` with `resolve?` and the log `LStep` | **a transcription, checked by reading, with proved properties**: print functions are host functions (fresh per import, `Spectest.lookup?_print`, `….resolve?_print_twice`) answered with the unchanged store and no values (`Spectest.print_nf`); globals fresh per import (`….lookup?_global`, `….resolve?_global_twice`); `table`, `table64`, `memory` shared (`….lookup?_shared`, `….resolve?_memory_twice`); observation: the host-call log, projected by `Spectest.printed` to upstream's output lines. `Spectest.hostDet : HostDet Spectest.host`, `Spectest.hostTyped : HostTyped Spectest.host`. Not claimed: indistinguishability from other `spectest` implementations; output as text; the `env` virtual module. The closed module `Spectest.module` (`….WasmWastLink`) is superseded (no rows) | wasmtime's own `spectest` (agreement on outcomes; it shares globals and functions too, which Wasm code cannot observe); `regress/wrong-spectest-shared.wast` (shared memory) rejected |
| Core `Step` with a host → determinism | **proved for any deterministic host** (`Silmaril.Wasm.Abstract.HostDet.Thms`): `Step.join_of_hostDet (hd : HostDet host) : Step (profile o) host c c₁ → Step (profile o) host c c₂ → Det.Join (Step (profile o) host) c₁ c₂`; `Steps.nf_unique_of_hostDet`; `Steps.always_of_hostDet` (a run to a normal form excludes infinite runs); `LSteps.nf_unique_of_hostDet` (normal form and host-call log unique). No typing hypothesis | — |
| WAST float commands → `Step (Profile.spec nd r)` | **per command, proved**: `ScriptHoldsS.of_kernel` turns one `decide +kernel` run of `scriptSK` (fragment check `StraightLine.fn?`, result class `numericSet?`, containment `NumSet.sub`) into `returns_allowed_all`/`traps_all` (every normal form, with existence) and `terminates_all` for every command of a module, for every `nd` and `r`; `numericSet?_sound` relates the classes to `floatUnOpRel`/`floatBinOpRel`/`convertRel` | wasmtime 50.0.0: 6783/6783 agree (one NaN per run, §4) |
| Binaryen interpreter / `wasm-shell` | **open** (`FwdSim`/`BwdSim` unproved; fragments in `Wasm/Interp`) | wasm-opt release suites (tested) |
| Component IR `Comp.denU`/`denI` ↔ REF (reference machine) | `Simple.sound` (import-free numeric); session adequacy with imports on a fragment (#805, open); start comparison on 3 litmus components (#827, open) | wasmtime 50.0.0, wasm-tools 1.262.0, jco 1.39.0 (not run in CI) |
| REF (Lean transcription of `definitions.py` @ `a25fc0b`) | a transcription, **not** an independent authority | component-model test suite (not vendored) |
| KMem evaluator (#796, open) | `stepI_toBytes`, `runI_toBytes`, `instantiateOnce?_toBytes`, `instantiateCfg?_toBytes`, engine simulation, REF transfer: unconditional in #796; used by the WAST checker `scriptKM` | — |

Tool correctness (decoder, validator, encoder, WAST parser) is a separate axis. The decoder is
sound (`decode?_sound`), not complete. The validator is sound and complete for silmaril-lean's
`ModuleOk` (`validate?_sound`, `validate?_complete`); `ModuleOk` itself is a transcription whose
agreement with the SpecTec validation rules is open (rows above). Other validator and WAST-parser
theorems are listed in [wasm-tools-trust.md](wasm-tools-trust.md). Agreement with upstream tools is tested, not proved.

## 2. The first slice: denominator, pins, skips

**Pins.**

| input | pin | SHA-256 |
|---|---|---|
| spec test suite | WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36` (codeload archive; `tools/wasm-tools/tests/pins.sh`) | archive `22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b` |
| converter | wasm-tools 1.262.0 `json-from-wast` | archive `655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65`, binary `fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211` |
| oracle | wasmtime 50.0.0 (`ebe5e8df1 2026-10-20`; `tools/wasm-jco/tests/pins.sh`) | archive `77c19ee0437991f9ac7837b9c269d9c7076744f85dad263fea5214cc2723c7ff`, binary `f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7` |

**Denominator.** Every command after a `module` command of `test/core/{i32, i64, int_exprs, fac,
traps, address}.wast` (deterministic profile) and `test/core/{f32, f64, f32_bitwise, f64_bitwise,
float_misc, conversions}.wast` (specification profile): 8098 commands; and every command but the
`module` commands of the linked files `test/core/{imports, linking, exports, start, global, data,
elem}.wast` (one script per file): 576 commands. **8674 commands**. `module` commands themselves
are not counted.

| file | commands | proved | unsupported | undetermined |
|---|---|---|---|---|
| `i32.wast` | 459 | 457 | 2 | 0 |
| `i64.wast` | 415 | 413 | 2 | 0 |
| `int_exprs.wast` | 89 | 89 | 0 | 0 |
| `fac.wast` | 7 | 6 | 1 | 0 |
| `traps.wast` | 32 | 32 | 0 | 0 |
| `address.wast` | 256 | 256 | 0 | 0 |
| `f32.wast` | 2513 | 2511 | 2 | 0 |
| `f64.wast` | 2513 | 2511 | 2 | 0 |
| `f32_bitwise.wast` | 363 | 363 | 0 | 0 |
| `f64_bitwise.wast` | 363 | 363 | 0 | 0 |
| `float_misc.wast` | 470 | 470 | 0 | 0 |
| `conversions.wast` | 618 | 618 | 0 | 0 |
| **total, single-module files** | **8098** | **8089** | **9** | **0** |

Linked files (`context`: `register` and bare actions, no claim, part of later rows' prefixes):

| file | commands | proved | context | unsupported | undetermined |
|---|---|---|---|---|---|
| `imports.wast` | 150 | 128 | 6 | 16 | 0 |
| `linking.wast` | 142 | 133 | 9 | 0 | 0 |
| `exports.wast` | 41 | 41 | 0 | 0 | 0 |
| `start.wast` | 15 | 10 | 4 | 1 | 0 |
| `global.wast` | 115 | 111 | 1 | 3 | 0 |
| `data.wast` | 36 | 35 | 1 | 0 | 0 |
| `elem.wast` | 77 | 73 | 4 | 0 | 0 |
| **total, linked** | **576** | **531** | **25** | **20** | **0** |

**All files: 8674 commands, 8620 proved, 25 context, 29 unsupported, 0 undetermined, 0
mismatch.** Before host references (`(ref.extern n)`, `(ref.func)`): 8563 proved, 22 context, 38
unsupported, 51 undetermined. Before the linked scripts went on after a segment trap: 8481
proved, 16 context, 41 unsupported, 136 undetermined.

By assertion: at `profile o`, `assert_return` 1025 proved (`returns_only`) and `assert_trap` 115
proved (`traps_only`); at `Profile.spec`, `assert_return` 6716 proved (`returns_allowed_all`:
4885 exact, 895 `nan:canonical`, 936 `nan:arithmetic` expectations) and `assert_trap` 67 proved
(`traps_all`), each also with a `terminates_all` row; `assert_invalid` 166 proved **tool-level**
(`validator_rejects`); `assert_malformed` 8 (all text) and `assert_exhaustion` 1 unsupported.
Before the float files: 1253 proved, 5 unsupported. No command was a mismatch, and none ran out
of fuel (100 000 steps per call). Not in the slice: `f32_cmp`, `f64_cmp` (in the fragment, left
out for kernel time), `float_exprs`, `float_literals`, `float_memory` (outside the fragment).

**Skip reasons.**

| count | status | reason |
|---|---|---|
| 20 | unsupported | linked files: `assert_malformed` on text |
| 8 | unsupported | `assert_malformed` on text: no binary; the WAT front end has no completeness theorem and its syntax error also covers unsupported text |
| 1 | unsupported | `assert_exhaustion` (`fac.wast`): resource exhaustion is not modelled |

"Undetermined" never means the implementation failed: it means no theorem was produced.

## 3. What each assertion claims, and how strong it is

Each row is stated over: the module (valid, no imports, instantiated by the specification's
`Instantiate` in the empty store, its code run to the empty code: `Instance`); the actions of all earlier commands of the same module, threaded through their
final stores (also after a trap); `profile o` with `o = neverFail` for the integer, control and
memory files, `Profile.spec` (every run of the specification's NaN choices) for the float files;
no host functions.

| assertion | shape and strength | status |
|---|---|---|
| `assert_return` (exact values) | `returns_only`: some host-free run returns `vs`, and **every host-free normal form** returns `vs`. Plus, by `ReturnsOnly.always`: no host-free run is infinite, and every finite run extends to a normal form returning `vs`. | 1025 proved |
| `assert_trap` | `traps_only`: same, with "is a trap"; the trap message is not part of the claim. `TrapsOnly.always` excludes divergence. | 115 proved |
| `assert_return` at `Profile.spec` (float files; `nan:canonical`, `nan:arithmetic` or exact bits) | `returns_allowed_all`: some host-free run returns values in the allowed set, and **every host-free normal form** of every run of `Profile.spec` does (canonical = canonical NaN of either sign; arithmetic = NaN with the quiet bit set, either sign; exact = same bits, `-0 ≠ +0`). Plus `terminates_all`, its own row: no host-free run is infinite. Uniqueness is not claimed (NaN payloads are nondeterministic) | 6716 proved, each with termination |
| `assert_trap` at `Profile.spec` | `traps_all` and `terminates_all` | 67 proved |
| `assert_exhaustion` | unsupported: stacks are unbounded in the model | 1 skipped |
| `assert_invalid` | `validator_rejects`, **tool-level**: silmaril-lean's `decode?` reads the bytes and its `validate?` rejects the module. With `validate?_complete`: no module the bytes encode in `Binary.Core.Encodes` is `ModuleValid` (`ValidatorRejects.not_valid`), relative to silmaril-lean's transcriptions `Encodes` and `ModuleOk`; not invalidity in the spec (the `ModuleOk` ↔ SpecTec bridge is open, §1). `validate?_sound` gives nothing about a rejection | 113 proved (tool-level) |
| `assert_malformed` | binary: `decoder_rejects`, **tool-level** ("the decoder rejects"; `decode?` is only sound, so not grammar rejection); text: unsupported, since the WAT front end's `.syntax` error also covers unsupported text and it has no completeness theorem | binary: shape, none in this slice; text: 4 unsupported |
| `assert_return`, `assert_trap` in a linked file | `host.returns_only`, `host.traps_only` (`(ref.extern n)` and `(ref.null)` are exact values; with a `(ref.func)` result, `host.returns_matching`: every normal form returns a function reference): the same, under `Step (profile o) Spectest.host` (print calls are host calls), after **every** earlier module, `register` and action of the file from the context `Init` (the shared `spectest` table and memory; `"spectest"` bound to the host environment); imports resolved through the registry (fresh `spectest` print functions and globals per import) and typed by `ExternAddrOk`, stores and the host-call log threaded across modules (also through imported memories, tables and globals); modules instantiated by the specification's `Instantiate` | 235 proved (199 `host.returns_only`, 2 `host.returns_matching`, 34 `host.traps_only`) |
| `assert_unlinkable` | `host.unlinkable`, strength `link`: the module is valid and its imports do not resolve through the registry, or resolve to addresses without the import types (`ExternAddrOk`, a transcription of `Externaddr_ok`); `Unlinkable.not_instantiate`: no `Instantiate` derivation exists for them | 136 proved |
| `assert_uninstantiable` (`assert_trap (module …)`) | `host.uninstantiable`: the module links and the specification's `Instantiate` configuration traps at every normal form, in a segment initialisation (`table.init`/`memory.init` out of bounds) or in the start function; the script goes on with the residual store (the allocation and earlier writes persist, also in imported tables and memories), and the failed instance is never current, named or registered | 34 proved (32 segment traps, 2 start traps) |
| `register`, bare actions, `get`, named modules | script-state transitions of the linked shapes (`CmdRun`); `get` reads a global export | 25 `context` rows; 11 `get` rows proved |
| the printed output of a script (no WAST assertion) | `host.log_is`: the script runs and every context it reaches has the host-call log `l` (`LogIs.of_kernel`) | 1 proved (`silmaril.wasm_wast.spectest_host.log`) |

**Wording.** The `…_only` statements quantify over normal forms only: "every normal outcome is
`r`". That no run diverges is a separate theorem, proved for every row:
`Reaches.always : Reaches o m pre act r → Always o m pre act r`, from the one-step diamond
(`Det.DStep.join'`) and the strict decrease of code size on a non-trivial peak
(`Det.DStep.shrink`). It is a property of `profile o`. Under `Profile.spec` termination is the
separate shape `terminates_all`, proved for the float rows from the straight-line fragment
theorem (`StraightLine.not_diverges`), not from determinism.

**Script state.** A row is relative to the actual run of the earlier actions, not to their
expected outcomes. Earlier assertions are their own rows; a later row does not assume them, but
its existence part does require every earlier action to end at a result, and at `profile o` the
earlier actions leave exactly one state (`ScriptAt.unique`). At `Profile.spec` the earlier
actions of the float files leave exactly the instantiated state, whatever their runs
(`scriptAtS_iff`): every function keeps the store (`StraightLine.nf`).

Every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound`.

## 4. External-oracle trust boundary

An oracle result is **test-wise agreement**: wasmtime 50.0.0, given one script, accepted it.
It is not a proof, it is not checked by Lean, and it says nothing about commands that were not
run. What it adds is independence: an implementation not derived from silmaril-lean's semantics
gives the same outcome as the kernel-checked row on 8620 of 8620 commands (for the 288
`assert_invalid` and 4 binary `assert_malformed` rows: wasmtime also rejects the same bytes; for
6 of them with a differently worded message). For a linked-file row, wasmtime runs the whole file's script, with
its **own** `spectest`: agreement on the outcome, not evidence about `Spectest.host` beyond it
(wasmtime shares one instance of every `spectest` entity; the reference interpreter and
`Spectest.host` allocate globals and print functions per import, a difference Wasm code cannot
observe). For a `Profile.spec` row, wasmtime
runs once and returns one NaN: its pass says that this member is in the allowed set, not that
every member of the specification's result set is; the latter is the kernel row's claim. Running it in CI (§5) does not make
it a proof.

What is trusted when reading `examples/wasm-wast/oracle.json`:

* that the binary with SHA-256 `f95e5b…` is wasmtime 50.0.0 as released (the archive SHA-256 was
  recorded on 2026-11-09 from the GitHub release asset; `fetch-wasmtime` re-checks both);
* that `wasmtime wast` implements the WAST assertions as specified (in particular, an
  `assert_trap` passes on any trap, whatever its message, as in the rows, and `nan:canonical`,
  `nan:arithmetic` and exact float constants keep their meaning: canonical NaN of either sign,
  quiet NaN of either sign, same bits); `gen.py regress` checks only that it rejects a few
  deliberately wrong expectations of each kind, among them `nan:canonical` on an arithmetic
  non-canonical result and `+0` for `-0` (§5);
* that the script given to wasmtime is the one whose SHA-256 is recorded, and that it encodes
  the row's command: the same module binary, the same earlier actions (none for the float files,
whose modules have no state), the same command; for a linked file, every command the kernel ran
before it, in order, with the same module binaries and names (one script per file). `gen.py
  verify --scripts` regenerates every script and compares its SHA-256; it checks consistency
  of the record, not wasmtime's verdicts;
* the machine that ran it (`host`, `generated_at`): verdicts are only re-obtained by running
  `gen.py oracle` again.

What the oracle does **not** cover: whether Core is the specification (§1), the commands left
out (§2), the spec profile's nondeterminism (wasmtime picks one NaN payload, one grow outcome),
and the binaries themselves (both sides read wasm-tools' output for the text).

## 5. The bounded CI oracle job

Implemented as `.github/workflows/ci-wast-oracle.yml`, the `wast-oracle` job of `CI` (no Lean
build): on pull requests touching `tools/wasm-wast/**`, `examples/wasm-wast/**`, the pins files
or `.github/**`, on `workflow_dispatch`, and nightly (`nightly.yml`). Its steps, cost and the
wrong-expectation regression are in [wasm-wast.md](wasm-wast.md#the-ci-oracle-job):

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec   # spec archive and wasm-tools, SHA-256 checked
python3 -I tools/wasm-wast/gen.py fetch-wasmtime       # wasmtime archive and binary, SHA-256 checked
python3 -I tools/wasm-wast/gen.py convert              # spec files checked against report.json
python3 -I tools/wasm-wast/gen.py verify --scripts     # the committed record is consistent
python3 -I tools/wasm-wast/gen.py oracle --check       # re-run wasmtime; fail on any failure or difference
python3 -I tools/wasm-wast/gen.py regress              # wrong expectations must be rejected
```

The job fails on any oracle failure, on any difference between the re-run and the committed
`oracle.json` (verdicts, scripts, kernel statuses, upstream-file verdicts), on a stale record
(`verify`), and if wasmtime accepts any deliberately wrong expectation (`regress`: six committed
`wrong-*.wast` scripts, each required to fail on its marked line, among them a wrong
`nan:canonical` and a wrong signed zero, a passing control, and three generated mutants, one of
them a `nan:arithmetic` expectation made `nan:canonical`). About 55 s of work after downloads
(35 MB on a cold cache, then cached by the pins' SHA-256 and re-checked); timeout 5 minutes.

## 6. Staged acceptance criteria

| stage | scope | acceptance criterion | state |
|---|---|---|---|
| S0 | the slice of §2 | every command counted with a status and reason; every proved row a kernel theorem with termination; oracle 100 % agreement on executed commands; provenance verifiable | **met** in #843 (885 proved, 885/885 agree); with the `KMem` checker, 1140 proved, 1140/1140 agree; with the rejection shapes, 1253 proved (113 tool-level), 1253/1253 agree, re-checked in CI (§5) |
| S1 | numeric scripts (`i32`, `i64`, `f32`, `f64`, `conversions`, `int_exprs`, …) | ≥ 95 % of `assert_return`/`assert_trap` commands kernel-checked at `profile o`, NaN-pattern results as allowed-set claims under `Profile.spec`; every skip classified; oracle agreement 100 % on executed ones | `i32`, `i64`, `int_exprs`: 100 % of their 847 `assert_return`/`assert_trap` commands proved at `profile o`; `f32`, `f64`, `f32_bitwise`, `f64_bitwise`, `float_misc`, `conversions`: 100 % of their 6783 proved at `Profile.spec` (every normal form, termination), 6783/6783 oracle agreement; `f32_cmp`, `f64_cmp`, `float_exprs`, `float_literals`, `float_memory` not started |
| S2 | memory, tables, control (`address`, `memory*`, `br*`, `call*`, `traps`) | the same; data segments in the kernel (KMem, #796); `assert_unlinkable`/`assert_uninstantiable` shapes | `traps`, `fac` and `address` proved (`address` on `KMem` stores, `ScriptHolds.of_kernelKM`); `assert_unlinkable` and start-trap `assert_uninstantiable` shapes in place (`host.*`), 128 + 1 proved; segment-trap instantiation not modelled; the other files not started |
| S2' | linking (`imports`, `linking`, `exports`, `start`, `global`, `data`, `elem`) | whole-file scripts with imports, `register`, named modules, `get`; a stated `spectest` model; every command accounted for; oracle agreement on the same script context | 531 of 576 proved, 25 context, 20 unsupported (`assert_malformed` on text), 0 undetermined, 531/531 agree (before host references: 474, 51 undetermined behind `externref` arguments; before the residual store: 392, 136 undetermined behind segment traps); `spectest` is the typed host `Spectest.host` with the reference interpreter's identity semantics (§1), plus 4 hand-written rows (shared memory, fresh globals, the print log); `names.wast` left out for kernel memory |
| S3 | validation (`assert_invalid`) | validator completeness proved, or claims labelled tool-level; 100 % of commands accounted for | **met at the tool level** for the slice: 113/113 proved as `validator_rejects`, labelled tool-level; `validate?_complete` is proved, so they exclude `ModuleOk`-validity; invalidity in the spec waits on the `ModuleOk` ↔ SpecTec bridge |
| S4 | decoding (`assert_malformed` binary) | decoder rejection kernel-checked; completeness or an explicit weaker label | shape `decoder_rejects` (tool-level) in place; no binary `assert_malformed` in the slice; the 4 text ones unsupported (§3) |
| S5 | SIMD, relaxed SIMD, GC, exceptions, tail calls, memory64, multi-memory | per-proposal pass/skip counts; nondeterministic results as allowed-set claims | not started |
| C1 | component-model WAST suite (pinned) on REF | per-file PASS/FAIL/UNSUP counts as JSON, shown in the explorer; agreement with wasmtime 50 | not started |
| C2 | components with lists, strings, resources | IR/REF adequacy extended | in progress (#805, #827) |

CI budget per stage: kernel time is per generated module (here 33 s to 62 s each, 133 s with
9.3 GB peak RSS for `address.wast` on `KMem`, and up to about 320 s for the 5000 rows of
`f32.wast`/`f64.wast` at `Profile.spec`), so shard by file; the oracle job of §5 grows linearly
with the number of scripts (about 7 ms each).

## 7. Highest-risk caveats

1. **SpecTec ↔ Core 3.0 whole-step** simulation is open. Rows are proved against
   `Execution.Core`, not against the spec transcription. Closing `Task.wholeStep` is the top
   priority for "equivalent to the specification".
2. **Profiles:** uniqueness, interpreter completeness and the general termination argument are
   proved only at `profile o`. Under `Profile.spec`, every-normal-form and termination claims
   are proved only for straight-line numeric functions (the float rows); existence lifts in
   general (`Reaches.spec`). Relaxed SIMD and grow failure have no allowed-set rows yet.
3. **Hosts:** the single-module rows are host-free. The linked rows are relative to one concrete
   host, `Spectest.host` (a transcription of `spectest.ml`, checked by reading against the pinned
   source, §1), with its registry and its observation (the host-call log). Determinism with a host
   is proved for every deterministic host (`Step.join_of_hostDet`), so these rows keep
   every-normal-form claims and termination; they are not claims about arbitrary hosts, and
   printed output is a log projection, not text.
4. **Resource exhaustion** and stack overflow are not modelled.
5. **Rejections are tool-level.** The validator is complete for `ModuleOk`, but `ModuleOk` ↔
   SpecTec validation is open, so `assert_invalid` rows do not say "invalid in the spec"; decoder
   completeness is not proved, which limits `assert_malformed` to "the decoder rejects", and
   text `assert_malformed` has no shape.
6. **Components:** REF is a transcription, not an independent oracle; IR↔REF adequacy is
   fragmentary; the external oracles are not run in CI.
7. The **Binaryen interpreter** is unverified; `wasm-shell` agreement is tested only.

## 8. Direct evidence for the current API, and the plan

What the linked WAST rows rest on, by name (all depend only on `propext`, `Classical.choice`,
`Quot.sound`; `#print axioms` on each):

| theorem | statement (abridged) | relative to |
|---|---|---|
| `Silmaril.Wasm.Abstract.Step.join_of_hostDet` | `HostDet host → Step (profile o) host c c₁ → Step (profile o) host c c₂ → Det.Join (Step (profile o) host) c₁ c₂` | any host with at most one outcome per call; profile `profile o` |
| `Silmaril.Wasm.Abstract.Steps.always_of_hostDet` | `HostDet host → Steps … c₀ c → (∀ x, ¬ Step … c x) → ¬ Diverges (profile o) host c₀ ∧ ∀ c', Steps … c₀ c' → Steps … c' c` | the same |
| `Silmaril.Wasm.Abstract.LSteps.nf_unique_of_hostDet` | two logged runs from one configuration and log to normal forms end in the same configuration with the same host-call log | the same; observation: the log of `(host function, arguments)` |
| `Silmaril.Project.Shapes.WasmWastHost.Spectest.hostDet` | `HostDet Spectest.host` | the concrete `spectest` host |
| `….Spectest.hostTyped` | `HostTyped Spectest.host`: answers keep the store typed, extend it, and have the callee's result type | the same |
| `….Spectest.print_nf` | a host function of code `k` answered by the host, invoked with arguments of its parameter count: `NF o (invoke s a args, l) (⟨s, {}, []⟩, l ++ [(k, args)])` | the same; `profile o` |
| `….Spectest.resolve?_print_twice`, `….resolve?_global_twice`, `….resolve?_memory_twice` | two imports of a print function (a global) get two new addresses; two imports of `memory` get one shared address and leave the store unchanged | the registry `resolve?` (the reference interpreter's `lookup_import`) |
| `….ScriptHolds.of_kernel` | `scriptHK o fuel cmds = true → ScriptHolds o cmds` (every `host.*` claim of the script) | `Spectest.host`, `profile o`, `ByteArray` stores |
| `….ScriptAt.unique` | at `profile o` a script prefix reaches at most one context (store, registry, named modules, current module, log) | the same |
| `….LogIs.of_kernel` | `logHK o fuel cmds = some l → LogIs o cmds l` | the same; observation `Spectest.printed` |
| `Silmaril.Project.WasmWast.SpectestHost.shared_memory` | after `$W` stores 42 through its import of `spectest.memory`, `$R`'s load through its own import returns 42 at every normal form | the same |

Prioritized plan for the WAST bridge:

1. **Trap-aware instantiation** (segment traps keep the earlier writes): unblocks 98 undetermined
   linked commands (`linking.wast`, `data.wast`, `elem.wast`).
2. **Host references** (`ref.extern n`) as a typed host extension of the same shape as
   `Spectest.host` (an embedder-allocated reference type, deterministic): unblocks 38 `global.wast`
   commands and 6 reference-pattern expectations.
3. **The `ModuleOk` ↔ SpecTec validation bridge**, then `Task.wholeStep` (§7.1): the rows are
   about `Execution.Core`, not yet about the transcribed specification.
4. **Allowed-set rows beyond straight-line floats** and the remaining spec files.

