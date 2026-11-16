# WAST commands of the spec test suite as kernel-checked problems

A slice of the WebAssembly specification test suite, command by command, as problem rows of
the standard shapes `silmaril.shapes.wasm.wast.*`. Each `assert_return`/`assert_trap` row is
answered by a theorem about Core reduction (`Silmaril.Wasm.Execution.Core.Step`), checked by the
Lean kernel. Each `assert_invalid` row is answered by a **tool-level** theorem: silmaril-lean's
validator rejects the module (see [Rejections](#rejections-tool-level)). The same commands are
run by a pinned independent implementation (wasmtime 50.0.0), in CI by the
[WAST oracle job](#the-ci-oracle-job).

Tests establish agreement only on the cases tested. A row says what silmaril-lean's Core
semantics does on one command; it does not say that the Core semantics is the specification
(see [Trust boundary](#trust-boundary)). The roadmap towards that, with the theorem status of
each implementation-to-specification bridge and staged acceptance criteria, is
[Confidence in the Wasm semantics](wasm-confidence.md).

## The shapes

`Silmaril.Project.Shapes.WasmWast.Defs`:

| shape | Lean | statement |
|---|---|---|
| `silmaril.shapes.wasm.wast.returns` | `Returns o m pre act vs` | after the script `m`, `pre`, **some** host-free run of `act` under `profile o` reaches a normal form returning `vs` |
| `silmaril.shapes.wasm.wast.returns_only` | `ReturnsOnly o m pre act vs` | `Returns`, and **every** host-free **normal form** of `act` returns `vs`: no normal form is a trap, other values, a stuck or a host-call state |
| `silmaril.shapes.wasm.wast.traps` | `Traps o m pre act` | some host-free run of `act` traps |
| `silmaril.shapes.wasm.wast.traps_only` | `TrapsOnly o m pre act` | `Traps`, and every host-free normal form of `act` is a trap (the trap message is not part of the claim) |
| `silmaril.shapes.wasm.wast.validator_rejects` | `ValidatorRejects b` | **tool-level**: silmaril-lean's decoder `decode?` reads the bytes `b` as some module, and silmaril-lean's validator `validate?` rejects it |
| `silmaril.shapes.wasm.wast.decoder_rejects` | `DecoderRejects b` | **tool-level**: silmaril-lean's decoder `decode?` rejects the bytes `b` |

The `…_only` statements quantify over **normal forms** only ("every normal outcome is `r`"), not
over runs: on their own they do not exclude an infinite run. Divergence is excluded by a
theorem about the shapes, not by their statements (see [Termination](#termination)).

The definitions:

* `Instance m s mi`: `m` is valid (`ModuleOk m ⟨[], _⟩`, so no imports), and instantiating it
  from the empty store with `instantiateOnce?`, including the segment initialisation, gives the
  store `s`, the module instance `mi` and no start function.
* `InvokeNF o s a args c`: `c` is reachable from `$invoke(s, a, args)` by
  `Step (profile o) noHost` and has no such step.
* `Run o mi s acts s'`: each action `invoke name args` calls the function export `name` of
  `mi` and runs to an `InvokeNF` whose code is a result (values, trap or exception). Its store
  is the next state, so the store persists across calls, also after a trap.
* `ScriptAt o m pre mi s := ∃ s₀, Instance m s₀ mi ∧ Run o mi s₀ pre s`.
* `Reaches`/`Only o m pre act r`: some/every `InvokeNF` of `act` at some/every `ScriptAt` state has
  the outcome `r`.
* `Always o m pre act r`: at every `ScriptAt` state, no host-free run of `act` is infinite
  (`¬ Diverges (profile o) noHost (invoke s a args)`), and every finite host-free run extends to
  an `InvokeNF` with the outcome `r`.

**Script state, exactly.** `pre cmds k` is the list of the *actions* of the first `k` commands:
bare `invoke`s and the actions of `assert_return`/`assert_trap` alike (also those of assertions
outside the fragment, kept as actions). The store after each is the store of its normal form,
whatever its outcome: values, a trap or an exception. So a store write made before a trap is
visible to later commands, as in the reference interpreter. A command's claim is stated
relative to the **actual** run of the earlier actions, not to their expected outcomes: the
expectations of earlier assertions are their own rows and are not premises of later rows. The
`Reaches` part of a row does require every earlier action to end at a result (otherwise
`ScriptAt` is empty and `Reaches` is false), and at `profile o` the earlier actions leave at most
one state (`ScriptAt.unique`), so a row speaks about exactly one store.

Transfer lemmas (`….Thms`): `ScriptHolds.of_kernel`, `ScriptHolds.of_kernelKM` and
`scriptK_of_scriptKM` (below); `ScriptHolds.returnsOnly`,
`ScriptHolds.trapsOnly` (the row of command `k`); `ReturnsOnly.returns`, `TrapsOnly.traps`
(the weaker existence shapes); `Only.unique`, `ReturnsOnly.not_traps`,
`TrapsOnly.not_returns` (an `…_only` row excludes every other normal outcome);
`ScriptAt.unique`; `Reaches.always`, `ReturnsOnly.always`, `TrapsOnly.always`,
`ScriptHolds.always` (termination, below).

**Profile.** `profile o` is the deterministic profile: canonical NaNs, `$ND = false`, and
`memory.grow`/`table.grow` failing exactly when the oracle `o` says so. Every row of the slice
uses `o = neverFail` (growth fails only when it must). Under `profile o`, Core reduction is
deterministic up to bubbling (`Det.DStep.join'`), so host-free normal forms are unique
(`nf_unique_of_join`). That is what makes the `…_only` shapes provable. Under the
specification profile `Profile.spec` (nondeterministic NaN payloads, relaxed SIMD, grow
failure) uniqueness does not hold and an allowed-set shape is needed. None is implemented yet.

### Termination

The shapes do not mention divergence, but at `profile o` it is excluded by a theorem:

```lean
theorem Reaches.always (h : Reaches o m pre act r) : Always o m pre act r
theorem ScriptHolds.always (h : ScriptHolds o m cmds) (k : Nat)
    (hk : cmds[k]? = some ⟨act, some e⟩) :
    Reaches o m (pre cmds k) act e.result ∧ Only o m (pre cmds k) act e.result ∧
      Always o m (pre cmds k) act e.result
```

So every proved row also says: no host-free run of the command is infinite, and every finite
host-free run extends to a normal form with the expected outcome. Proof
(`Silmaril.Proofs.Project.Shapes.WasmWast.invokeNF_always`): Core reduction at `profile o` is
not a function (a trap bubbles out at several context depths), but two successors of a
configuration are joinable in at most one step each (`Det.DStep.join'`), and when they differ
both have strictly smaller code (`Det.DStep.shrink`). A lexicographic induction on (distance to
the normal form, code size) then rules out an infinite run from a configuration with a run to a
normal form, and the diamond carries every finite run to that normal form. All of this is for
host-free runs: a run that calls a host function stops at a normal form (a host call), which
the `…_only` rows exclude as an outcome.

### Rejections (tool-level)

```lean
def ValidatorRejects (b : ByteArray) : Prop :=
  ∃ m, Binary.Core.decode? b = some m ∧ validate? m = none
def DecoderRejects (b : ByteArray) : Prop := Binary.Core.decode? b = none
```

Both are statements about silmaril-lean's functions, not about the specification. Their titles
("silmaril-lean's validator rejects the module that silmaril-lean's decoder reads from given
bytes", "silmaril-lean's decoder rejects given bytes") do not say that the module is invalid or
that the bytes are malformed. What does follow, exactly:

* **Validator soundness gives nothing about a rejection.** `validate?_sound :
  validate? m = some mt → ModuleOk m mt` speaks only about acceptance.
* **Validator completeness** is proved: `validate?_complete : ModuleOk m mt → validate? m = some mt`
  (`Silmaril.Wasm.Validation.Check.ValidateFinal`, axioms `propext`, `Classical.choice`,
  `Quot.sound`). With the decoder's soundness `decode?_sound` and the functionality of the binary
  grammar (`Binary.Core.functional`), a validator rejection gives

  ```lean
  theorem ValidatorRejects.not_valid (h : ValidatorRejects b)
      (hm : Binary.Core.Encodes b.data.toList m) : ¬ Validation.ModuleValid m
  ```

  no module that `b` encodes in silmaril-lean's binary grammar `Binary.Core.Encodes` is valid in
  silmaril-lean's validation relation `ModuleOk`. Both relations are silmaril-lean's
  transcriptions of the specification; that they agree with the specification's binary format
  and validation rules is not a theorem here (the SpecTec validation bridge is fragmentary:
  [Confidence](wasm-confidence.md#1-bridge-matrix-implementation-to-specification)). So an
  `assert_invalid` row is "invalid relative to silmaril-lean's transcription", not "invalid in
  the specification".
* **Decoder completeness** is not proved: `decode?` is sound only, so `DecoderRejects b` does not
  exclude that `b` encodes a module. No binary `assert_malformed` is in this slice.
* **The bytes** are what wasm-tools 1.262.0 `json-from-wast` writes for the WAST module (also for
  the one `module quote` of `address.wast`, which wasm-tools encodes). The text-to-binary step is
  the upstream tool's.

`ValidatorRejects.of_kernel (h : validatorRejectsB b = true)` and `DecoderRejects.of_kernel (h :
(decode? b).isNone = true)` prove the shapes from one `decide +kernel` evaluation each. The
expected rejection must be the one that happens: an `assert_invalid` whose bytes the decoder
rejects, or a binary `assert_malformed` that the decoder accepts, would be a mismatch, not a row.

**Text `assert_malformed`** (four in `i32.wast`/`i64.wast`: `(i32.const nan:arithmetic)` and
`nan:canonical`, and the same for `i64`) stays unsupported. There is no binary, so the decoder
does not apply. silmaril-lean's WAT front end `Silmaril.Wasm.Tools.Parse.textModule` rejects all
four natively, but with its `.syntax` error, which also covers text outside its elaborator, and
the front end has no completeness theorem. A kernel row would only say "the front end does not
accept this text", which is also true of supported-but-unimplemented syntax.

## The proof route

`ScriptHolds o m cmds` says that every command of a script holds after the commands before it.
`ScriptHolds.of_kernel (h : scriptK o fuel m cmds = true)` proves it from **one** kernel
evaluation per module (`decide +kernel`). `scriptK` validates `m` (`validate?`), checks that it
has no imports and that its function exports have scalar types, instantiates it, and runs the
commands in order with `fuel` steps each of the kernel-evaluable interpreter `runInvokeK`. For
each command it checks that the arguments are typed (`invokeOkB`), that the run stopped at a
result, and the expected outcome. The proof (`Silmaril.Proofs.Project.Shapes.WasmWast`) uses:

* `validate?_sound` and `Silmaril.Wasm.Game.IsInstance.ok`: the instantiated store is well typed;
* `runInvokeK_eq`, `runInvoke?_steps_noHost`, `runInvoke?_stopped`, `runInvoke?_sound`: the
  stopped run is a host-free normal form, and the next store is well typed;
* `Det.DStep.join'` and `nf_unique_of_join`: normal forms are unique, so a script reaches at
  most one state (`scriptAt_unique`) and every normal form of the command is the one found.

### Modules with data segments: the checker on `KMem`

`scriptK` keeps memories as `ByteArray`s. The kernel evaluates `ByteArray` writes through their
logical definitions (`ByteArray.copySlice`, `Array.extract`), element by element over the whole
memory, so instantiating a module whose data segment is written into a 64 KiB memory exceeds its
recursion limit (all of `address.wast`). For such modules the rows use

```lean
theorem scriptK_of_scriptKM (h : scriptKM o fuel m cmds = true) : scriptK o fuel m cmds = true
theorem ScriptHolds.of_kernelKM (h : scriptKM o fuel m cmds = true) : ScriptHolds o m cmds
```

`scriptKM` is `scriptK` with the store over `KMem` (`Silmaril.Wasm.Execution.MemRep`, #796): a
balanced tree of bytes whose reads and writes touch only the leaves they need. It instantiates
`m` from `importStoreKM` (the empty `KMem` store) with the generic `instantiateOnce?`, and runs
each command with `runInvokeKR`, the structural driver `Verify.Kernel.runK` over the generic
interpreter head step `interpHead o`. The statement `ScriptHolds o m cmds` is unchanged: it is
about the `ByteArray` semantics (`Instance`, `InvokeNF` over `Step (profile o)`). The proof
(`Silmaril.Proofs.Project.Shapes.WasmWast.scriptK_of_scriptKM`) maps every `KMem` store to its
`ByteArray` reading `Store.toBytes`:

* `importStoreKM.toBytes = Game.importStore []` (by `rfl`) and `instantiateOnce?_toBytes`: the
  `KMem` instantiation, read through `toBytes`, is the `ByteArray` instantiation;
* `runK_eq` (now stated at any representation), `runI_toBytes` and
  `(invoke s a vs).toBytes = invoke s.toBytes a vs`: each `KMem` run, read through `toBytes`, is
  `runInvoke?` on the `ByteArray` store, with the same stop flag and outcome (`runInvokeK_toBytes`);
* `invokeOkB` and `exportsScalar` read only the functions of the store, which `toBytes` keeps.

So `scriptKM … = true` gives `scriptK … = true`, and `ScriptHolds.of_kernel` does the rest. The
kernel never evaluates a `ByteArray` memory.

Every answer depends only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms Silmaril.Project.WasmWast.I32.l37`, `….Traps.l17`, `….I32.script0`,
`….Address.script0`, `….Address.script3`, `….Address.l104` (`assert_return`), `….Address.l192`
(`assert_trap`), `ScriptHolds.of_kernel`, `ScriptHolds.of_kernelKM`, `scriptK_of_scriptKM`,
`Reaches.always`, `ScriptHolds.always`, `ScriptAt.unique`; and for the rejections
`ValidatorRejects.of_kernel`, `DecoderRejects.of_kernel`, `ValidatorRejects.not_valid` and all
113 `assert_invalid` answers, e.g. `….I32.l444`, `….I64.l457`, `….Address.l214`).

## The slice and its counts

WebAssembly/spec at `608711107b7f1edb13efd57b7d79b49477462d36` (the archive pinned in
`tools/wasm-tools/tests/pins.sh`, SHA-256
`22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b`):
`test/core/{i32,i64,int_exprs,fac,traps,address}.wast`. Each module is the binary that the
pinned wasm-tools 1.262.0 `json-from-wast` writes for it. The binary is read by silmaril-lean's
decoder (`decode?`, sound by `decode?_sound`), and `decodeJ : decode? bytesJ = some mJ` is
kernel-checked.

| file | commands | proved | unsupported | undetermined |
|---|---|---|---|---|
| `i32.wast` | 459 | 457 | 2 | 0 |
| `i64.wast` | 415 | 413 | 2 | 0 |
| `int_exprs.wast` | 89 | 89 | 0 | 0 |
| `fac.wast` | 7 | 6 | 1 | 0 |
| `traps.wast` | 32 | 32 | 0 | 0 |
| `address.wast` | 256 | 256 | 0 | 0 |
| **total** | **1258** | **1253** | **5** | **0** |

Commands are every command after a module (`module` commands themselves are not counted). The
1253 proved rows are 1025 `assert_return` (`returns_only`) and 115 `assert_trap` (`traps_only`),
claims about Core reduction, and 113 `assert_invalid` (`validator_rejects`: 83 in `i32.wast`, 29
in `i64.wast`, 1 in `address.wast`), **tool-level** claims (`report.json` field `strength`:
`only` or `tool`). Before the rejection shapes, the 113 were unsupported (1140 proved, 118
unsupported).
The 255 rows of `address.wast` (206 `assert_return`, 49 `assert_trap`, in 4 modules, every one
with a data segment) are proved on `KMem` stores (`ScriptHolds.of_kernelKM`); the others on
`ByteArray` stores (`ScriptHolds.of_kernel`). Before the `KMem` checker, the 255 were
undetermined: on `ByteArray` stores the kernel cannot instantiate their modules.
Reasons for the commands that are not proved:

| count | status | reason |
|---|---|---|
| 4 | unsupported | `assert_malformed` on text: no binary; the WAT front end has no completeness theorem and its syntax error also covers unsupported text ([above](#rejections-tool-level)) |
| 1 | unsupported | `assert_exhaustion` (`fac.wast`): resource exhaustion is not modelled |

No command was a mismatch, and none ran out of fuel (100 000 steps per call). Every
`assert_invalid` module is decoded by `decode?` and rejected by `validate?` (none is rejected by
the decoder, none accepted). `address.wast` line 214 is a `module quote` with
`offset=4294967296` on a 32-bit memory: the decoder reads the 64-bit offset and the validator
rejects it.

Kernel time (one `lake build` of each generated module, one core): `I32.Thms` 36 s, `I64.Thms`
43 s, `IntExprs.Thms` 33 s, `Fac.Thms` 62 s, `Traps.Thms` about 30 s. `Address.Thms` (four
modules on `KMem`, with their `decodeJ` checks): 133 s and 9.3 GB peak RSS for the whole `lean`
process (`lake env lean`, one run on a 2-vCPU sandbox). With the 113 rejection rows, one
`lake build` of the generated modules on a 2-vCPU sandbox (two modules at a time) took
`I32.Thms` 48 s (83 rejection rows), `I64.Thms` 45 s (29), `Address.Thms` 130 s (1).

Per module of `address.wast` (`benchmarks/wasm-wast-kmem`, one run each, whole `lean` process,
imports alone 3.6 s and 1.55 GB):

| module | commands | `scriptKM` (`KMem`) | `scriptK` (`ByteArray`) |
|---|---:|---|---|
| 0 (line 3) | 91 | passes, 27.8 s, 5.92 GB | `(kernel) deep recursion detected`, 38.4 s, 6.84 GB |
| 1 (line 223) | 126 | passes, 47.4 s, 9.49 GB | `(kernel) deep recursion detected`, 52.1 s, 10.15 GB |
| 2 (line 514) | 19 | passes, 5.3 s, 1.95 GB | `(kernel) deep recursion detected`, 15.6 s, 3.32 GB |
| 3 (line 564) | 19 | passes, 6.2 s, 2.00 GB | `(kernel) deep recursion detected`, 15.9 s, 3.32 GB |

The `ByteArray` checks fail while instantiating, before any command runs. Decoding module 1 alone
in the kernel takes about 40 s and 9 GB, so for the larger modules the decoder, not memory,
dominates. The generator emits `decodeJ` as a term (`Option.some_get`, `Option.get_eq_getD`):
the former `simp [mJ, hx]` proof exceeded the default heartbeats on module 1.

## The oracle

`gen.py oracle` runs the pinned wasmtime 50.0.0 (`tools/wasm-jco/tests/pins.sh`, binary SHA-256
`f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7`) as `wasmtime wast` on one
small script per command: the same module binary as `(module binary …)`, the actions before the
command in that module, then the command. For an `assert_invalid` row the script is
`(assert_invalid (module binary …) "message")` on the row's bytes. Results are in `examples/wasm-wast/oracle.json`
(schema `silmaril.wasm-wast.oracle.v0.2`), with their provenance:

* `oracle`: tool, version, release URL, archive SHA-256
  (`77c19ee0437991f9ac7837b9c269d9c7076744f85dad263fea5214cc2723c7ff`), binary SHA-256, the
  output of `wasmtime --version` (`wasmtime 50.0.0 (ebe5e8df1 2026-10-20)`);
* `inputs`: the spec pin, the converter pin, the SHA-256 of `report.json` and of each spec file;
* `generated_at` (UTC) and `host`;
* per command: `script_sha256` (the exact script given to wasmtime), the oracle verdict, the
  kernel status, and wasmtime's error message on failure (local paths removed).

Reproducing and checking it:

```sh
python3 -I tools/wasm-wast/gen.py fetch-wasmtime   # pinned archive, SHA-256 checked, binary SHA-256 checked
python3 -I tools/wasm-wast/gen.py convert          # needs the spec and wasm-tools pins (below)
python3 -I tools/wasm-wast/gen.py oracle           # rewrites oracle.json (fetches wasmtime if absent)
python3 -I tools/wasm-wast/gen.py verify --scripts # no wasmtime: re-checks oracle.json
python3 -I tools/wasm-wast/gen.py oracle --check   # re-runs wasmtime, compares with oracle.json (CI)
python3 -I tools/wasm-wast/gen.py regress          # wrong expectations must be rejected (CI)
```

`fetch-wasmtime` downloads the release archive into a fresh temporary directory, checks its
SHA-256, extracts only the `wasmtime` member, checks the binary's SHA-256, and installs it at
the pinned path (`$SIL_TOOLS/wasmtime-50.0.0/wasmtime`). `verify` does not run wasmtime. It
checks that the recorded tool provenance equals the pins, that `report.json` and the spec files
have the recorded SHA-256, that the commands run are exactly those the report selects (with the
report's statuses), and that the counts follow from the results. With the converted JSON present
(`--scripts` requires it) it regenerates all 1253 scripts and compares their SHA-256. `verify`
checks consistency of the record, not wasmtime's verdicts: those are re-obtained only by running
`oracle` again (in CI, `oracle --check`). `convert` also checks each unpacked spec file against
the SHA-256 that `report.json` records. The whole `oracle` run takes about 11 s on the
development sandbox (1253 scripts and the 6 upstream files).

Results:

* 1253 commands run, all of them kernel-proved (1140 executions, 113 validator rejections);
* **1253 of 1253** kernel-proved commands pass under wasmtime: wasmtime also rejects each of the
  113 `assert_invalid` binaries. The 1140 execution scripts and verdicts are those of the
  earlier runs;
* the unmodified upstream files: `int_exprs`, `fac`, `traps`, `address` pass. `i32` and `i64`
  fail on a text `assert_malformed` whose message wasmtime's text parser words differently
  (`nan:arithmetic` in an `i32.const`: "expected a i32", not "unexpected token"), not on an
  execution or validation command.

### The CI oracle job

`.github/workflows/ci-wast-oracle.yml` (job `wast-oracle` of `CI`, with no Lean build) runs on
pull requests that touch `tools/wasm-wast/**`, `examples/wasm-wast/**`,
`tools/wasm-tools/tests/{pins,fetch-pins}.sh`, `tools/wasm-jco/tests/pins.sh` or `.github/**`
(the `wast-oracle` filter of `.github/paths-filter.yml`), on `workflow_dispatch`, and nightly
(`.github/workflows/nightly.yml`). The `CI` result job requires it whenever its filter matches.

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec  # archives and binaries, SHA-256 checked
python3 -I tools/wasm-wast/gen.py fetch-wasmtime      # archive and binary, SHA-256 checked
python3 -I tools/wasm-wast/gen.py convert             # spec files checked against report.json
python3 -I tools/wasm-wast/gen.py verify --scripts    # the committed record is consistent
python3 -I tools/wasm-wast/gen.py oracle --check      # re-run wasmtime on every command
python3 -I tools/wasm-wast/gen.py regress             # wrong expectations must fail
```

The pinned tools are cached by the SHA-256 of the two pins files (`actions/cache`) and re-checked
against their pinned SHA-256 after every restore. `oracle --check` does not rewrite
`oracle.json`: it fails if any command fails under wasmtime, or if the re-run's (id, verdict,
script SHA-256, kernel status) set or the upstream files' verdicts differ from the committed
record, and it writes the fresh record to `$WASM_WAST_WORK/oracle.check.json`.

**The wrong-expectation regression** (`gen.py regress`) checks that the oracle can fail:

* `tools/wasm-wast/regress/wrong-{return,trap,invalid,malformed}.wast`, committed, each with one
  directive marked `;; WRONG` (`assert_return` of 2 where the function returns 1, `assert_trap`
  on `6 / 3`, `assert_invalid` on a valid module, `assert_malformed` on the empty module). wasmtime
  must fail on each, and on the marked line (so the failure is the wrong expectation, not a
  parse error);
* `regress/right-control.wast`: the same modules with right expectations; wasmtime must pass;
* two generated mutants: the first `assert_return` script of `oracle_scripts` with its result
  plus one, and the first `assert_invalid` script with its module replaced by the empty (valid)
  module. wasmtime must fail on each.

Locally: `oracle --check` and `verify --scripts` pass, `regress` passes (7 scripts). Tampering
with one committed verdict in `oracle.json` makes `oracle --check` exit 1, and making
`wrong-return.wast` right makes `regress` exit 1 ("wasmtime ACCEPTS a wrong expectation").

Cost: downloads of about 35 MB on a cold cache (spec archive 15.0 MB, wasm-tools and wasmtime
archives), then `convert` 0.2 s, `oracle --check` about 11 s, `verify --scripts` and `regress`
about 1 s each on the development sandbox; the job has a 5-minute timeout. It grows linearly with
the number of scripts (about 9 ms each).

## Trust boundary

* **Core vs the specification.** Rows are about silmaril-lean's `Execution.Core.Step`. Its
  agreement with the SpecTec transcription of Wasm 3.0 is partly proved, and the whole-step
  simulation goals are open (`docs/projects/wasm.md`).
* **Instantiation** is `instantiateOnce?` (a function, related to the relational `Instantiate`
  by `instantiateOnce?_steps`).
* **`KMem` rows** (`address.wast`) are kernel evaluations on `KMem` stores, carried to the
  `ByteArray` statements by proved simulations (`scriptK_of_scriptKM`): no extra assumption.
* **Modules** must be valid, with no imports, no start function and scalar function exports.
  `register`, named modules and the spectest host are not in this fragment.
* **The binaries** are wasm-tools' output for the WAST text. The text-to-binary step is the
  pinned upstream tool's, not silmaril-lean's.
* **Rejection rows** (`assert_invalid`) are tool-level: silmaril-lean's `decode?` and
  `validate?` on wasm-tools' bytes. Through `validate?_complete` they exclude validity in
  silmaril-lean's `ModuleOk`, a transcription of the specification's validation rules whose
  agreement with them is not proved ([Rejections](#rejections-tool-level)).
* **The oracle** is test-wise agreement of an independent implementation on the scripts it was
  given, not a proof (also when CI runs it); what it relies on is listed in
  [Confidence in the Wasm semantics](wasm-confidence.md#4-external-oracle-trust-boundary).
* **The generator** (`tools/wasm-wast/gen.py`) chooses which commands to give to the kernel from
  a native interpreter run. It cannot make a wrong row pass: every row is a kernel-checked
  theorem whose statement carries the module, the earlier actions, the action and the expected
  result. It can only leave commands out, and every command left out is counted with a reason
  in `examples/wasm-wast/report.json`.

## Files and how to regenerate

* `Silmaril/Project/Shapes/WasmWast/{Defs,Thms}.lean`, `Silmaril/Proofs/Project/Shapes/WasmWast.lean`:
  the shapes, the kernel checkers and their soundness, `ValidatorRejects.not_valid`.
* `Silmaril/Project/WasmWast/<File>/{Defs,Thms}.lean` (generated): the bytes, modules and
  command lists, then the kernel theorems and the rows `silmaril.wasm_wast.<file>.l<line>`.
  `Silmaril.Project.WasmWast.Thms` imports them all, and `silmaril.toml` puts it in the project
  dump.
* `examples/wasm-wast/report.json` (every command: inputs, expectation, observation, status,
  reason, row, claim strength `only` or `tool`), `examples/wasm-wast/oracle.json`.
* `tools/wasm-wast/regress/*.wast`: the oracle's wrong-expectation regression and its control;
  `.github/workflows/ci-wast-oracle.yml`: the CI oracle job.
* The explorer view `#/wast` (`tools/silmaril-project/src/project/explore/views/wast.js`, test
  `tests/explore/wast_view.test.mjs`) reads `wast/report.json` and `wast/oracle.json` next to
  the page, and the rows' answers from the database. Each proved row shows its claim strength:
"semantic: Core reduction" or "tool-level rejection".

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec      # pinned, SHA-256 checked
python3 -I tools/wasm-wast/gen.py fetch-wasmtime          # wasmtime 50.0.0 only (for `oracle`)
python3 -I tools/wasm-wast/gen.py convert                 # wasm-tools json-from-wast
python3 -I tools/wasm-wast/gen.py probe                   # native classification (not a proof)
python3 -I tools/wasm-wast/gen.py emit                    # Lean modules and report.json
python3 -I tools/wasm-wast/gen.py oracle                  # oracle.json (fetches wasmtime if absent)
python3 -I tools/wasm-wast/gen.py verify --scripts        # re-check oracle.json's provenance
lake build --wfail Silmaril.Project.WasmWast.Thms         # the kernel checks
python3 -I tools/wasm-wast/gen.py site .lake/silmaril     # report next to explore.html
```

## Not yet

NaN-pattern results (`nan:canonical`, `nan:arithmetic`) as allowed-set claims under
`Profile.spec`; `assert_invalid` relative to the specification (a proved bridge between
`ModuleOk` and the SpecTec validation rules); `assert_malformed` beyond the tool level (decoder
completeness; text: a WAT front end with a completeness theorem and an error that separates
malformed from unsupported text); `assert_unlinkable`/`assert_uninstantiable`; imports and the
spectest host; `register`; and the rest of the suite.
