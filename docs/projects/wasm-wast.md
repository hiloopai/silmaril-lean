# WAST commands of the spec test suite as kernel-checked problems

A slice of the WebAssembly specification test suite, command by command, as problem rows of
the standard shapes `silmaril.shapes.wasm.wast.*`. Each `assert_return`/`assert_trap` row is
answered by a theorem about Core reduction (`Silmaril.Wasm.Execution.Core.Step`), checked by the
Lean kernel: at the deterministic profile for the integer, control and memory files, and at the
**specification profile** `Profile.spec` (the specification's NaN result sets, with
`nan:canonical`/`nan:arithmetic` as allowed sets) for the float and conversion files
([Under the specification profile](#under-the-specification-profile)). Each `assert_invalid` row is answered by a **tool-level** theorem: silmaril-lean's
validator rejects the module (see [Rejections](#rejections-tool-level)). Seven files with
several modules, imports, `register` and the `spectest` module are checked as **linked scripts**,
one per file, against the typed `spectest` host `Spectest.host`, with the WAST host references
`(ref.extern n)` as arguments and results
([Linked scripts](#linked-scripts-imports-register-and-the-spectest-host)). Every row's script
state starts from the specification's `Instantiate`
([below](#single-module-files-on-the-specifications-instantiate)). The same commands are
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

`Silmaril.Project.Shapes.WasmWastSpec.Defs`, at `Profile.spec nd r` (below):

| shape | Lean | statement |
|---|---|---|
| `silmaril.shapes.wasm.wast.returns_allowed_exists` | `ReturnsAllowedExists nd r m pre act ps` | **some** host-free run of `act` reaches a normal form returning values in the allowed set `ps` |
| `silmaril.shapes.wasm.wast.returns_allowed_all` | `ReturnsAllowedAll nd r m pre act ps` | `ReturnsAllowedExists`, and **every** host-free normal form of `act`, at every state the earlier actions can leave, returns values in `ps` |
| `silmaril.shapes.wasm.wast.traps_all` | `TrapsAll nd r m pre act` | some host-free run of `act` traps, and every host-free normal form is a trap |
| `silmaril.shapes.wasm.wast.terminates_all` | `TerminatesAll nd r m pre act` | at every state the earlier actions can leave, **no** host-free run of `act` is infinite, and every finite run extends to a normal form |

The `…_only` statements quantify over **normal forms** only ("every normal outcome is `r`"), not
over runs: on their own they do not exclude an infinite run. Divergence is excluded by a
theorem about the shapes, not by their statements (see [Termination](#termination)).

The definitions:

* `Instance P m s mi`: **the specification's instantiation** under the profile `P`: `m` is
  valid (`ModuleOk m ⟨[], _⟩`, so no imports), and the configuration `c₀` of
  `Instantiate P Det.noHost (Game.importStore []) m [] c₀` (Wasm 3.0 `$instantiate` in the empty
  store: `$evalglobals`, `$allocmodule`, so every global is allocated as the specification
  allocates it, then the code of the element segments, the data segments and the start call)
  runs by host-free steps under `P` to the empty code, in the store `s`; `mi` is the module
  instance of `c₀`:

  ```lean
  def Instance (P : Numerics.Profile) (m : Module) (s : Store Nat) (mi : ModuleInst) : Prop :=
    (∃ xtE, ModuleOk m ⟨[], xtE⟩) ∧
      ∃ c₀ c : Config Nat, Instantiate P Det.noHost (Game.importStore []) m [] c₀ ∧
        c₀.frame.module = mi ∧ Steps P Det.noHost c₀ c ∧ c.code = [] ∧ c.store = s
  ```

  No function of silmaril-lean is part of it ([below](#single-module-files-on-the-specifications-instantiate)).
* `InvokeNF o s a args c`: `c` is reachable from `$invoke(s, a, args)` by
  `Step (profile o) noHost` and has no such step.
* `Run o mi s acts s'`: each action `invoke name args` calls the function export `name` of
  `mi` and runs to an `InvokeNF` whose code is a result (values, trap or exception). Its store
  is the next state, so the store persists across calls, also after a trap.
* `ScriptAt o m pre mi s := ∃ s₀, Instance (profile o) m s₀ mi ∧ Run o mi s₀ pre s`.
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
failure) uniqueness does not hold: the allowed-set shapes of the next section are stated there.

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

## Under the specification profile

The specification leaves NaN payloads open: a float operator returns a *set* of results, and an
`assert_return` may expect `nan:canonical` or `nan:arithmetic` instead of a value. The rows of
`f32.wast`, `f64.wast`, `f32_bitwise.wast`, `f64_bitwise.wast`, `float_misc.wast` and
`conversions.wast` are stated
at `Profile.spec nd r` (`nan := .spec`: float operators step to every member of
`floatUnOpRel`/`floatBinOpRel`/`convertRel`; grow failure nondeterministic), not at the
deterministic profile, and with three separate claims.

**Allowed sets** (`Silmaril.Project.Shapes.WasmWastSpec.Defs`), one pattern per result, over the
bits of the value (`M` = 23 or 52 trailing significand bits):

| WAST | `ValPat` | allowed values |
|---|---|---|
| `nan:canonical` | `.canonicalNaN t` | `CanonicalBits t`: exponent field all ones, payload exactly `2^(M-1)`; either sign |
| `nan:arithmetic` | `.arithmeticNaN t` | `ArithmeticBits t`: exponent field all ones, payload at least `2^(M-1)` (the quiet bit set); either sign |
| any other value | `.exact v` | exactly `v`, as bits: `-0 ≠ +0`, and a NaN constant is its exact bit pattern |

Every canonical NaN is arithmetic (`arithmeticBits_of_canonicalBits`), not conversely: the two
patterns stay distinct.

**The script semantics** is that of the deterministic shapes with `profile o` replaced by
`Profile.spec nd r`: `InvokeNFS` (a host-free normal form under `Profile.spec`), `RunS` (each
earlier action runs to *some* normal form at a result, whose store is the next state),
`ScriptAtS` (every state the earlier actions can leave). `ReachesS`/`AllS` quantify over these
states and normal forms.

**Three claims, three shapes.**

1. **Existence** (`returns_allowed_exists`; also the first half of `returns_allowed_all` and
   `traps_all`): some run reaches an allowed outcome.
2. **Every normal form** (`returns_allowed_all`, `traps_all`): every host-free normal form, at
   every state, has an allowed outcome. This is a statement about all runs of
   `Profile.spec`, not about one deterministic run.
3. **Termination** (`terminates_all`): no host-free run is infinite, and every finite run
   extends to a normal form. Under `Profile.spec` this does not follow from the other two
   (there is no determinism to derive it from), so it is its own shape and its own row
   (`….l<line>_terminates`).

**The fragment theorem** (`Silmaril.Wasm.Execution.StraightLine.Thms`, proofs in
`Silmaril.Proofs.Wasm.Execution.StraightLine`). A *straight-line numeric function*
(`StraightLine.Fn fi k op`) has no declared locals, one result, and the body
`local.get 0 … local.get (k-1); op` with `op` a scalar numeric instruction of arity `k`
(`NumericStep`: integer and float unary, binary, test and comparison operators, conversions).
Every function of the six files is one. For such a function at address `a` of the store `s`
and **any** profile `P`:

```lean
theorem StraightLine.nf (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op)
    (hex : ∃ is', NumericStep P (vals args ++ [.plain op]) is')
    (h : Steps P noHost (invoke s a args) c) (hnf : ∀ x, ¬ Step P noHost c x) :
    ∃ is', NumericStep P (vals args ++ [.plain op]) is' ∧ c = ⟨s, {}, is'⟩
theorem StraightLine.reaches (hf) (hfn) (hn : NumericStep P (vals args ++ [.plain op]) is') :
    Steps P noHost (invoke s a args) ⟨s, {}, is'⟩
theorem StraightLine.not_diverges (hf) (hfn) : ¬ Diverges P noHost (invoke s a args)
theorem StraightLine.extends_nf (hf) (hfn) (h : Steps P noHost (invoke s a args) c) :
    ∃ c', Steps P noHost c c' ∧ ∀ x, ¬ Step P noHost c' x
```

So the normal forms of the invocation are exactly the results of the numeric step, in the
empty frame and the **same store**, and every run terminates. The proof follows the stages of a
run (`call_ref`, `k` `local.get`s, the numeric step, `label-vals`/`trap-label`,
`frame-vals`/`trap-frame`) with a rank that every step decreases (`inv_step`); every step from a
stage is inverted through the head decomposition `Det.Step.decomp`, which holds at every
profile. Only the numeric step depends on `P`, and it is kept as the relation.

**The result classes.** `numericSet? op args` computes the class of the specification's result
set of a float operator, comparison or conversion on given arguments, by the case split of the
relations themselves: one exact value; the canonical NaNs of a type (the result is a NaN and
every NaN operand is canonical); the arithmetic NaNs of a type (the result is a NaN and some
operand is a non-canonical NaN); or a trap (`trunc` of a NaN or out of range). Then

```lean
theorem numericSet?_sound (h : numericSet? op args = some S) :
    (∀ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is' → S.Mem is') ∧
      ∃ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is'
```

from the repository's NaN classes (`F32.IsCanonicalNaN` ⊆ `CanonicalBits`, `F32.IsArithmeticNaN`
⊆ `ArithmeticBits`, and the same for `F64`). `NumSet.sub S e` decides that the class is contained
in the expectation (a class of canonical NaNs is contained in `nan:canonical` and in
`nan:arithmetic`; a class of arithmetic NaNs only in `nan:arithmetic`; an exact value in the
pattern it matches; never a NaN class in an exact value).

**The checker.** `scriptSK m cmds` validates `m`, checks that it has no element or data
segments and no start function (so the `Instantiate` configuration has no code), instantiates it
(as `scriptK`, with `instantiateCfg?`) and checks, for
every command, that its export is a straight-line numeric function (`StraightLine.fn?`) and
that its result class is contained in its expectation. It runs no interpreter.

```lean
theorem ScriptHoldsS.of_kernel (h : scriptSK m cmds = true) : ScriptHoldsS nd r m cmds
```

for **every** `nd` and `r` (the relaxed builtins play no role in scalar numerics); the rows state
`nd = true` and the default relaxed choice, `Profile.spec`'s defaults. The earlier actions of a
script cannot change the state: by `StraightLine.nf`, every normal form of every action keeps the
store, so `ScriptAtS` has exactly the instantiated state (`scriptAtS_iff`). Each command gives
two rows: `l<line>` (`returns_allowed_all` or `traps_all`) and `l<line>_terminates`
(`terminates_all`), answered by `ScriptHoldsS.returnsAllowedAll`, `.trapsAll` and
`.terminatesAll`; the row's index fact `cmdsJ[k]? = some …` is one more `decide +kernel`.

**Refinement, for existence only.** `Reaches.spec : Reaches o m pre act res → ReachesS nd {} m
pre act (· = res)` lifts a run at `profile o` to `Profile.spec nd {}` (by
`Steps.deterministic_refines_spec`; a result is a normal form at every profile), and
`Returns.allowedExists` turns a `returns` row into `returns_allowed_exists` with exact patterns.
Uniqueness (`Only`) and termination (`Reaches.always`) do **not** transfer this way: they are
about the runs of `profile o`, and `Profile.spec` has more. That is why the float rows are proved
by the fragment theorem, not by the deterministic interpreter. No row of the slice is left at the
existence shape: every command of the six files is in the fragment.

## Linked scripts: imports, register and the spectest host

The files `test/core/{imports,linking,exports,start,global,data,elem}.wast` have several
modules per file, imports, `register`, named modules (`module $M`, `(invoke $M …)`, `(get $M …)`),
imports from `spectest` and module assertions (`assert_unlinkable`, `assert_trap` on a module,
which wasm-tools calls `assert_uninstantiable`). Each is checked as **one script per file**, against
a concrete typed host, by the shapes of `Silmaril.Project.Shapes.WasmWastHost`:

| name | statement |
|---|---|
| `silmaril.shapes.wasm.wast.host.returns_only` | `ReturnsOnly o pre act vs`: after the commands `pre`, some normal form of the action `act` under `Step (profile o) Spectest.host` returns `vs`, and every one does |
| `silmaril.shapes.wasm.wast.host.traps_only` | `TrapsOnly o pre act`: the same with a trap |
| `silmaril.shapes.wasm.wast.host.returns_matching` | `ReturnsMatching o pre act ps`: some normal form of `act` returns values matching the result patterns `ps` (`WasmWastRef.MatchAll`: `(ref.func)` is any function reference, every other pattern an exact value), and every one does ([Host references](#host-references-refextern-n-and-reffunc)) |
| `silmaril.shapes.wasm.wast.host.unlinkable` | `Unlinkable o pre m`: after `pre`, `m` is valid, and its imports either do not resolve through the registry, or resolve (allocating fresh `spectest` entities) to addresses that do not have the import types (`ExternAddrOk`) |
| `silmaril.shapes.wasm.wast.host.uninstantiable` | `Uninstantiable o pre m`: after `pre`, `m` links, and the specification's instantiation configuration (`Instantiate`) traps at every normal form under `Spectest.host`, in a segment initialisation or in the start function |
| `silmaril.shapes.wasm.wast.host.log_is` | `LogIs o cmds l`: the script runs, and every context it reaches has the host-call log `l` (the observation; the printed values are `Spectest.printed l`) |

### The reference `spectest` at the pinned commit

The reference interpreter of WebAssembly/spec at `608711107b7f1edb13efd57b7d79b49477462d36`
(the commit pinned in `tools/wasm-tools/tests/pins.sh`; the files below are those of
`https://github.com/WebAssembly/spec/tree/608711107b7f1edb13efd57b7d79b49477462d36/interpreter`):

* `interpreter/main/main.ml` l. 11–12: `Run.register_virtual "spectest" Spectest.lookup` and
  `Run.register_virtual "env" Env.lookup`: `spectest` is a *virtual* module, a lookup function, not
  an instance.
* `interpreter/script/runner.ml` l. 314: the registry maps a module name to a function
  `name -> externtype -> externinst option`; l. 338–349 (`lookup_registry`, `lookup_import`):
  each import calls that function **once, when the importing module is linked**; l. 352–357
  (`register_virtual`, `register_instance`): `(register "M" $i)` binds `M` to the exports of the
  instance `$i`, so a later `register "spectest"` shadows the virtual one; l. 395–400
  (`run_instantiation`): every import of a module is looked up, in import order (`List.map2`),
  before `Eval.init` checks the import types (`interpreter/exec/eval.ml` l. 1183–1190
  `init_import`, a `Link` error otherwise). The lookup ignores the requested type.
* `interpreter/host/spectest.ml` l. 48–64 (`lookup`):
  * `print`, `print_i32`, `print_i64`, `print_f32`, `print_f64`, `print_i32_f32`, `print_f64_f64`
    call `func print ts []` (l. 34–36), which calls `Func.alloc_host`: **a fresh host function at
    every lookup**, of the defined type `ts → []` (one final sub type, no supertypes). Calling it
    runs `print` (l. 38–45): one line `"<value> : <type>"` per argument on standard output (the
    type is the value's own), then `flush_all`, and it returns no values. `eval.ml` l. 1131–1133
    applies it to the arguments and pushes its (empty) results; it never traps, diverges or
    touches the store. `print` with no arguments prints nothing.
  * `global_i32`, `global_i64`, `global_f32`, `global_f64` call `global (GlobalT (Cons, t))`
    (l. 10–20), which calls `Global.alloc`: **a fresh immutable global at every lookup**, value 666
    (`i32`, `i64`) or 666.6 (`F32.of_float 666.6` = bits `0x4426A666`, `F64.of_float 666.6` = bits
    `0x4084D4CCCCCCCCCD`).
  * `table`, `table64`, `memory` (l. 22–32) are top-level `let` values, allocated once when the
    module `Spectest` is initialised: **every lookup returns the same table or memory**, for the
    whole process (so across the scripts of one run). `table`: `i32`, limits 10..20, nullable
    `funcref`, null; `table64`: the same with `i64`; `memory`: `i32`, 1..2 pages.
  * Any other name: `None`, an `unknown import` link error.

What is observable inside a WAST script: tables and memory are mutable and shared, so writes
through one import are seen through another (the row `silmaril.wasm_wast.spectest_host.shared_memory`
below). The globals are immutable, and function references have no equality in Wasm 3.0
(`funcref` is not a subtype of `eqref`), so fresh versus shared globals and print functions are
a property of the store that Wasm code cannot observe; only the embedder (and the store) can. The
printed output is not observed by any WAST assertion.

### The typed host, the registry and the observation

`Silmaril.Project.Shapes.WasmWastHost.Defs` models the environment in exactly those respects:

* **Host.** `Spectest.host : HostSemantics Nat`: a call of host code `k < 7` (the `k`-th print
  function of `Spectest.entries`) in the store `s` returns `s` unchanged and no values, when every
  host function instance with code `k` has no results (`printsTyped`, a guard that makes the
  answers typed in every store; in a script it always holds). It never diverges. Facts (`….Thms`):
  - `Spectest.hostDet : HostDet Spectest.host`: at most one outcome per call;
  - `Spectest.hostTyped : HostTyped Spectest.host`: every answer keeps the store typed, extends it
    and has the callee's result type;
  - `Spectest.print_nf`: for `s.funcs[a]? = some fi` with `fi.code = .host k`, the host answering
    `k` in `s`, and arguments of the parameter count, `NF o (invoke s a args, l)
    (⟨s, {}, []⟩, l ++ [(k, args)])`: one logged step to the empty code in the same store, a
    normal form; the call is appended to the log.
* **Registry.** A registered name is a module instance (`Reg.inst`, by `register`) or the
  `spectest` environment (`Reg.spectest sh`). `resolve? regs s imps` is stateful and goes in
  import order: an import of an instance is its export; an import of `spectest` is
  `Spectest.lookup?`: a print function is a fresh `allocHost` (code `k`, type `ofFlatType (ps →
  [])`, the reference interpreter's final sub type), a global a fresh `allocGlobal`, and `table`,
  `table64`, `memory` the exports of the one instance `sh` of `Spectest.shared`, allocated in the
  empty store at `Init`. Facts: `Spectest.lookup?_print`, `….lookup?_global` (the next address,
  a new instance), `….lookup?_shared` (the shared address, store unchanged);
  `Spectest.resolve?_print_twice`, `….resolve?_global_twice` (two imports of one name: two
  addresses), `….resolve?_memory_twice` (two imports of `memory`: one address). The table and
  memory are shared within a script; the reference interpreter also shares them across the scripts
  of one process (one script per file here, so no row depends on it).
* **Observation.** Runs are `LStep` runs (`Silmaril.Wasm.Abstract.HostDet`): a host-free step
  keeps the log, an answered host call at the `decompose?` callout (under any label, handler or
  frame) appends `(host function, arguments)`, a divergent call stutters. The script context keeps
  the log; `Spectest.printed log` (the arguments, in order) is the reference interpreter's output,
  one line per value. The rows claim results; the log is determined (`ScriptAt.unique` covers the
  whole context, log included) and claimed by `log_is` rows. `report.json` records the printed
  values of each command that prints (`printed`, from the probe; not a proof).

**Determinism with a host** (`Silmaril.Wasm.Abstract.HostDet.Thms`, reusable for any host): with
`HostDet host` at `profile o`,

* `Step.join_of_hostDet`: two steps of a configuration join in at most one step each;
  `Step.eq_or_shrink_of_hostDet`: they are equal or the first has smaller code. Host-free steps
  join by `Det.DStep.join'`; a host-free step has no callout (`Step.noRedex`,
  `decompose?_none_of_noRedex`), so it never competes with a host step; two host steps are at the
  same callout (`Step.split_host`) with the same outcome.
* `Steps.nf_unique_of_hostDet`, `Steps.always_of_hostDet`: normal forms are unique, and a run to
  one excludes infinite runs (a divergent host call included).
* `LSteps.nf_unique_of_hostDet`: the normal form **and the log** of a run to it are unique.

No typing hypothesis is needed for these.

**Script state.** A context (`Ctx`) is the store, the registry, the named modules, the current
module and the host-call log. `pre` lists the commands before the row, from `Init`; each changes
the context as the reference interpreter does when its assertion holds (`CmdRun`):

* `module`: valid (`ModuleOk`), every import resolved (`resolve?`, allocating the fresh `spectest`
  entities), the resolved addresses of the import types in the resolved store (`ExternAddrOk`: the
  premise of the specification's `$instantiate`), and **the specification's instantiation
  configuration** `c₀` (`Instantiate (profile o) Spectest.host s₀ m xas c₀`: `$evalglobals`,
  `$allocmodule`, then the code of the element segments, the data segments and the start call) run
  to a normal form under `Spectest.host` that is a result. The instance (the module instance of
  `c₀`) becomes current (and named); the log grows by the start function's print calls;
* `register "M" $t?`: the current (or named) instance registered as `M`;
* an action, whatever its expectation: a normal form that is a result, whose store and log are the
  next ones. Stores persist across modules, through imported memories, tables and globals, and
  after traps;
* `assert_unlinkable`: no change (the entities its resolution allocated are dropped, as the
  reference interpreter drops them); `assert_uninstantiable` (`assert_trap (module …)`): the store
  and log of the normal form of `c₀`, a trap of a segment initialisation or of the start function:
  the **residual store**, with the allocation and every earlier write (below). The failed
  instance is never current, named or registered.

`ScriptAt.unique`: at `profile o` the prefix reaches at most one context, so `Only` (every normal
form) is meaningful; `ReturnsOnly.always`, `TrapsOnly.always` add that no run of the invoked
function under `Spectest.host` diverges. `Unlinkable.not_instantiate`: no `Instantiate`
derivation exists for the resolved store and addresses, under any profile and host. The name
resolution is the WAST script semantics (the reference interpreter's registry), not part of the
Wasm specification.

**The checker.** `scriptHK o fuel cmds` allocates the shared instance, then validates, resolves,
type-checks the imports (`externAddrsOk?`), instantiates (`instantiateCfg?`: `prepare?`, the
specification's allocation, then the trap-aware segment initialisation, giving the start code or
`trap` in the residual store) and runs that configuration and every action on `KMem` stores with `runHG`: host-free runs of at most `fuel` steps of
the interpreter head step under `Verify.Kernel.runK`, and at a callout (`decompose?`) whose host
code the host answers (`Spectest.answers`), the empty result plugged into the context and the call
logged, at most `fuel` times. `ScriptHolds.of_kernel` carries one `decide +kernel` evaluation to
the claims, through: `instantiateCfg?_toBytes`, `runI_toBytes`, `decompose?_toBytes`,
`resolve?_toBytes` (the `KMem` run is the `ByteArray` run read through `toBytes`);
`instantiateCfg?_sound` (the checker's configuration is reached from the `Instantiate`
configuration, whose frame names the instance; `instantiate?_evalConst_complete`: `Instantiate`
has one configuration); `Game.instantiateCfg?_configOk` and `resolve?_ok` (fresh host functions by `allocHost_storeOk`,
fresh numeric globals by `storeOk_allocGlobal`), so every store is typed; between host calls
`runG_sound` (a stopped run is a host-free normal form and stays typed); at a host call
`Ctx.fill_callout_typed` (the empty result has the callee's empty result type, by `printsTyped`);
a stopped configuration with no callout, or a callout the host does not answer, has no step under
`Spectest.host` (`Step.split_host`); and `LSteps.nf_unique_of_hostDet` with `Spectest.hostDet`.
`logHK` runs the same commands and returns the log (`LogIs.of_kernel`).

**Strength labels** (`report.json` `strength`): `only` for `host.returns_only`, `host.traps_only`,
`host.returns_matching` and `host.uninstantiable` (Core reduction against `Spectest.host`, every normal form); `link` for
`host.unlinkable` (relative to `resolve?` and the `ExternAddrOk` transcription). `register` and
bare actions are `context` rows. Every row of a linked file records its context (`context`:
registered names, named modules, the current module and its imports, the module's own imports for
a module assertion, the host model), the host model (`host`), the observation (`observation`) and,
when the command printed, the printed values (`printed`).

**The hand-written rows** `silmaril.wasm_wast.spectest_host.*` (`Silmaril.Project.WasmWast.SpectestHost`,
the script `tools/wasm-wast/regress/right-spectest-shared.wast` written as Lean modules): `$W`
and `$R` import `spectest`'s `memory` separately; `before_write` (`$R` reads 0),
`shared_memory` (after `$W` stores 42, `$R` reads 42: shared, as upstream; a memory per import
would give 0, the expectation of `regress/wrong-spectest-shared.wast` that wasmtime must reject),
`globals` (two imports of `global_i32` add to 1332) and `log` (`log_is`: the log is
`[(1, [i32 42])]`, one `print_i32` call; upstream prints `42 : i32`).

**The closed-module shapes are superseded.** `Silmaril.Project.Shapes.WasmWastLink` (the shapes
`silmaril.shapes.wasm.wast.link.*`, `spectest` as the closed Wasm module `Spectest.module` with
empty print bodies and one shared instance, host-free reduction `Step (profile o) Det.noHost`,
printed output erased) is kept for its definitions (`Cmd`, `Action`, `Target`, which the scripts
use) and its theorems; no row uses its shapes any more. Its sharing of globals and print
functions differs from the reference interpreter (above); the typed host does not.

**What stops a script.** The script is cut at the first command the kernel cannot run, and every
later command of the file is undetermined (with the reason): an action with an argument outside
numbers and `(ref.extern n)`, or an instantiation that fails without a trap. No command of the
seven files stops a script any more. Expectations outside exact values and `(ref.func)` (NaN
patterns, other reference patterns; none occur in the seven files) would be unsupported rows
whose actions still run for the context. An `assert_trap (module …)` whose segment
initialisation traps does not stop a script either: the script goes on with the residual store
(below).

### Host references: `(ref.extern n)` and `(ref.func)`

`global.wast` (lines 235–241: `set-mr`/`get-mr` store and read `(ref.extern 10)` in a mutable
`externref` global; lines 660–661: `(ref.func)` results of a `funcref` table) and `elem.wast`
(lines 1019–1030: `set`/`get` store and read `(ref.extern 42)`, `(ref.extern 137)` in an
`externref` table) pass **host references** as arguments and expect them as results. No Wasm
module can write these values; they are part of the WAST script language.

**Upstream semantics** (WebAssembly/spec `608711107b`; the reference interpreter's files):

* `interpreter/text/parser.mly` (SHA-256
  `85c4e03eded78d1774ecffa9fa4a21a7d8cfc6779aea3aa64672ab0a827b6c57`) lines 1507–1509
  (`literal_ref`): `(ref.host n)` is `Script.HostRef n` and **`(ref.extern n)` is
  `Extern.ExternRef (Script.HostRef n)`**: the host reference `n`, converted to `extern`. Lines
  1525–1537 (`result`): `(ref.extern n)`, `(ref.host n)` and `(ref.null)` are `RefPat` (a
  value), `(ref.null ht)` is `NullPat`, `(ref.func)` is `RefTypePat FuncHT`, `(ref.extern)` is
  `RefTypePat ExternHT`.
* `interpreter/script/script.ml` (SHA-256
  `a0f3d4168f4bd1405de0a5aa1b9cb4c7bb13a6ea41c27cffaec773e9f7cf0555`) line 3: `HostRef of int32`
  extends `Value.ref_`; lines 77–81: its type is `any` (`type_of_ref'`); lines 89–94: two host
  references are equal when their numbers are. `interpreter/runtime/extern.ml` (SHA-256
  `d903075808640a32a2faa4cfcf3016ade8fa7acf07e2e97dc36e7c3cbb616c42`): `ExternRef of ref_`,
  of type `extern`, equal when the wrapped references are.
* `interpreter/script/runner.ml` (SHA-256
  `ac35f60152daa83b6b5b94d39a1cc9586d9aadbb265a7e51f8d1e8d3791be5a3`) lines 402–417
  (`run_action`): an `invoke` checks each literal's type against the parameter type
  (`Match.match_valtype`; `(ref.extern n)` has type `(ref extern)`), then calls the function.
  Lines 464–477 (`assert_ref_pat`): a `RefPat` holds when `Value.eq_ref` does (for
  `ExternRef`/`HostRef`/`NullRef`: structural equality), `NullPat` holds for every null,
  `RefTypePat FuncHT` for every function reference (`Instance.FuncRef _`, never null), and
  `RefTypePat ExternHT` for **every** reference, null included.
* The specification (SpecTec Wasm 3.0, vendored): `4.0-execution.configurations.spectec` lines
  42–43, `REF.HOST_ADDR hostaddr` and `REF.EXTERN ref` are reference values;
  `4.1-execution.values.spectec` lines 57–63, `Ref_ok/host: s ⊢ REF.HOST_ADDR a : REF ANY` and
  `Ref_ok/extern: s ⊢ REF.EXTERN ref : REF EXTERN` if `ref : REF ANY` and `ref ≠ REF.NULL`.

So `(ref.extern n)` is the specification's `REF.EXTERN (REF.HOST_ADDR n)`. silmaril-lean's Core
already has both (`Ref.host`, `Ref.extern`, typed by `RefOk.host`, `RefOk.extern`): the argument
is the Core value `.ref (.extern (.host n))` (`WasmWastRef.externHost n`), with no new runtime
syntax and no change to `Step`.

**silmaril-lean** (`Silmaril.Project.Shapes.WasmWastRef`, a small header of its own):

* Arguments: `argsOkR` accepts a number of exactly its parameter type and `(ref.extern n)` for a
  parameter `(ref null? extern)`; `invokeOkRB s a args` reads the parameter types of function
  `a`. The linked checker `scriptHK` uses it in place of `WasmWast.invokeOkB` (numbers only), and

  ```lean
  theorem invokeOkRB_sound (h : invokeOkRB s a args = true) : InvokeOk s a args
  ```

  gives the premise of `$invoke` (`RefOk.extern (RefOk.host n)`, and `Reftype_sub/null` for a
  nullable parameter), so the soundness proof of `scriptHK` is unchanged otherwise.
* Results: `(ref.extern n)` and `(ref.null …)` are exact values, compared by `Val` equality,
  which is `eq_ref` on these references; they stay `host.returns_only` rows. `(ref.func)` is the
  pattern `Pat.funcRef` (`Pat.Matches .funcRef w ↔ ∃ a, w = .ref (.func a)`), stated by the shape
  `host.returns_matching`. Its rows come from the exact row of the values the kernel run returns:

  ```lean
  theorem ReturnsOnly.matching (h : ReturnsOnly o pre act vs)
      (hm : WasmWastRef.matchAll ps vs = true) : ReturnsMatching o pre act ps
  ```

  (the generator puts the probe's values, e.g. `[.ref (.func 54)]` for `global.wast` line 660,
  into the kernel's command list; `matchAll_sound` decides the pattern). The claim of the row is
  the pattern, not the address.
* Not modelled: `(ref.host n)` arguments (none in the slice), `(ref.extern)` and the other
  type patterns (`(ref.any)`, `(ref.eq)`, …), `either`, and null arguments `(ref.null …)` (none
  in the seven files).

Of the 51 formerly undetermined commands of `global.wast` and `elem.wast`, 48 are proved rows
now and 3 are `context` rows (2 `register`, 1 bare action); the 3 commands with `externref`
arguments and the 6 `(ref.extern n)`/`(ref.func)` expectations are proved rows: 57 more proved
rows, 0 undetermined. wasmtime 50.0.0 agrees on each (`oracle --check`).

`#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` (or fewer) for
`WasmWastRef.invokeOkRB_sound`, `WasmWastRef.matchAll_sound`, `ReturnsOnly.matching`,
`WasmWastHost.ScriptHolds.of_kernel`, and the rows `….Global.l235`, `….Global.l241`,
`….Global.l660` (`(ref.func)`), `….Elem.l1019`, `….Elem.l1030`.

### Instantiation that traps: the residual store

**The specification** (WebAssembly/spec `608711107b`, SpecTec Wasm 3.0, vendored unmodified under
`specs/spectec/src/specification/wasm-3.0/`):

* `4.4-execution.modules.spectec` (SHA-256
  `4a34f8b5592e837e0b3f735230117ade01b5c8101a5e2ca75a816cc7c9c238ca`) lines 183–208: `$instantiate`
  checks `Module_ok` and `Externaddr_ok` for the imports, runs `$evalglobals`, `$evalexprs`,
  `$evalexprss`, allocates the instance with `$allocmodule` into the store, and returns the
  configuration `s''''; {MODULE moduleinst}; instr_E* instr_D* instr_S?`: the element segments'
  code, **then** the data segments' code, then `(CALL x)` for a start function. Lines 148–157:
  `$rundata_` of an active segment is its offset, `(CONST I32 0) (CONST I32 n) (MEMORY.INIT y x)
  (DATA.DROP x)`; `$runelem_` of an active segment is its offset, `(CONST I32 0) (CONST I32 n)
  (TABLE.INIT y x) (ELEM.DROP x)`, of a declarative one `(ELEM.DROP x)`; passive segments have
  no code.
* `4.3-execution.instructions.spectec` (SHA-256
  `2d00920d82e2c0b26bb5b3a29e3db65bbcd014f4d843bab28c6cc6853515636b`) lines 411–414 and 613–616:
  `Step_read/table.init-oob`, `Step_read/memory.init-oob`: the initial bounds check fails and the
  instruction steps to `TRAP`, before any element or byte is written; line 300:
  `Step_pure/trap-instrs`, the trap absorbs the remaining code (later segments, the drops, the
  start call). Nothing restores the store: the allocation and every write of the earlier segments,
  also into imported tables and memories, remain.

**The reference interpreter** at the same commit agrees: `interpreter/exec/eval.ml` (SHA-256
`c83974bfbe76185382a951d00088a4765f16e5db5aff584ffa572e1c8ab90136`) lines 1264–1296 (`run_elem`,
`run_data`, `run_start`) and 1305–1326 (`init`): the instance is built first, then
`eval (config inst [] (es_elem @ es_data @ es_start))` runs on mutable table and memory objects,
so a trap raised there (line 1143) leaves the earlier writes in place. In
`interpreter/text/parser.mly` (SHA-256
`85c4e03eded78d1774ecffa9fa4a21a7d8cfc6779aea3aa64672ab0a827b6c57`) lines 1439–1443 and 1471–1472,
`(assert_trap (module …) "…")` is `AssertUninstantiable` of an anonymous module definition, and in
`interpreter/script/runner.ml` (SHA-256
`ac35f60152daa83b6b5b94d39a1cc9586d9aadbb265a7e51f8d1e8d3791be5a3`) lines 559–566 the assertion
holds when `run_instantiation` (lines 395–400) raises a trap; no instance is bound, so the current
instance and the registry are unchanged, and later commands see the shared tables and memories as
the trap left them. `linking.wast` lines 397–423 test exactly this (line 399: "active element segments
stored before an out-of-bounds access persist after the instantiation failure").


**The script semantics** states this directly: `InstNF` runs the `Instantiate` configuration to
a normal form under `Spectest.host`, so a segment trap and a start trap are both a normal form
`trap`, and its store is the next store of the script. No function of silmaril-lean appears in
the statement of `InstNF`: the claims of the rows are relative to `Instantiate` and `Step`.

**Globals are allocated as the specification allocates them.** `$evalglobals` allocates every
global it evaluates (so that later initialisers can read it), and `$allocmodule` allocates every
global again from the values; the module instance names the second copies. Before this change the
linked scripts used `instantiateOnce?` (every global allocated once), which agrees with
`Instantiate` only on modules without globals, and otherwise only up to a renaming of global
addresses (`Silmaril.Proofs.Wasm.Game.SpecGlobals`). `InstNF` is now stated with `Instantiate`
itself, and the checker instantiates with `prepare?` (the specification's allocation order,
`prepare?_sound`), so the rows of modules with globals (`global.wast`, `linking.wast`,
`imports.wast`, …) are exact: no statement has a renaming or a no-globals hypothesis.

**silmaril-lean** (`Silmaril.Wasm.Execution.InstantiateTrap`):

* `initSegmentsR?`: the element segments, then the data segments, applied to the store directly,
  at any memory representation; a segment whose initial bounds check fails ends in `.trap s₁`, `s₁`
  the store after the earlier segments and the segment's offset. On `ByteArray` stores it is the
  existing `initSegmentsT?` (`initSegmentsR?_trap`).
* `instantiateT? s m xas : InstOutcome`: `prepare?` (allocation as `$instantiate`, globals
  allocated twice), then `initSegmentsR?`: `.ok s' f st`, `.trap s'` or `.fail`.
  `instantiateCfg? s m xas`: the same as the configuration to continue from (the start code, or
  `trap` in the residual store) with the module instance; the checker uses it.
  `instantiateOnceT?`: single allocation, as `instantiateOnce?` (`instantiateOnceT?_of_nil`: equal
  to `instantiateT?` without globals); the scripts do not use it.
* Agreement: `instantiateT?_ok_iff` (with `prepareDirect?`), `instantiateOnceT?_ok_iff`,
  `instantiateCfg?_eq_none_iff` (`instantiateCfg?` fails exactly when `instantiateT?` does);
  `instantiateT?_toBytes`, `instantiateCfg?_toBytes`: on `KMem` stores, read through `toBytes`, the
  outcome is the `ByteArray` one.
* **Soundness** (`….InstantiateTrap.Thms`, any profile and host, a valid module, imports of the
  import types):

  ```lean
  theorem instantiateT?_trap_sound (hvalid) (h : instantiateT? s m xas = .trap s') :
      ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧
        initSegmentsT? evalConst? c.store c.frame m = .trap s' ∧
        Instantiate P host s m xas (c.withStart st) ∧
        Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩

  theorem instantiateCfg?_sound (hvalid) (h : instantiateCfg? s m xas = some (c, mi)) :
      ∃ c₀, Instantiate P host s m xas c₀ ∧ c₀.frame.module = mi ∧ Steps P host c₀ c
  ```

  the residual store is **exactly the store of the trapping configuration**, reached from the
  `Instantiate` configuration by Core reduction. `instantiateT?_ok_sound`: `.ok s' f st` is a run
  to `⟨s', f, startCode st⟩`.
* **Completeness** (`Silmaril.Wasm.Game.InstantiateTrap.Thms`): `instantiateT?_ne_fail_iff`: for a
  valid module, typed imports and a typed store, `instantiateT? s m xas ≠ .fail ↔ ∃ c, Instantiate P
  host s m xas c` (with `instantiateCfg?_eq_none_iff`, the checker's instantiation fails only when
  no `Instantiate` configuration exists).
* **Typing**: `Game.instantiateCfg?_configOk`: the configuration of `instantiateCfg?` is typed
  (`Instantiate.ok`, carried along the run), so the residual store and every later store of the
  script are typed.
* **The script** (`….WasmWastHost.Thms`): `InstNF.of_trap`: when the imports of a valid `m`
  resolve to `s₀`, `xas` of the import types and `instantiateT? s₀ m xas = .trap s'`, then
  `∃ mi, InstNF o ctx m (some .trap) s' ctx.log mi`; `InstNF.unique`: at `profile o`,
  instantiation has one outcome (`instantiate?_evalConst_complete`: `Instantiate` has one
  configuration; `LSteps.nf_unique_of_hostDet`).
* Single allocation with globals (kept from the trap-aware single allocation):
  `instantiateOnceT?_trap_spec`, `instantiateOnceT?_trap_outcome` (`Game.InstantiateTrap.Thms`):
  the specification's instantiation plays as the thread stopped at the trap in the residual store
  of single allocation, up to the global address embedding of `spec_trap_seg`. The scripts do not
  need them.

`#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for
`instantiateCfg?_sound`, `instantiateCfg?_toBytes`, `instantiateCfg?_eq_none_iff`,
`instantiateT?_trap_sound`, `instantiateT?_ok_sound`, `instantiateT?_eq_fail_iff`,
`instantiateT?_toBytes`, `instantiateOnceT?_trap_steps`, `instantiateOnceT?_ok_iff`,
`instantiateOnceT?_toBytes`, `Game.instantiateT?_ne_fail_iff`, `Game.instantiateOnceT?_trap_spec`,
`Game.instantiateOnceT?_trap_outcome`, `Game.instantiateCfg?_configOk`, `InstNF.of_trap`,
`InstNF.unique`, `ScriptHolds.of_kernel`, `LogIs.of_kernel`, `….Global.script`, and the rows
`….Linking.l402` (segment trap), `….Linking.l410`, `….Linking.l411` (residual table),
`….Data.l211`, `….Data.l543`, `….Elem.l594`, `….Elem.l1017`.

## The proof route

`ScriptHolds o m cmds` says that every command of a script holds after the commands before it.
`ScriptHolds.of_kernel (h : scriptK o fuel m cmds = true)` proves it from **one** kernel
evaluation per module (`decide +kernel`). `scriptK` validates `m` (`validate?`), checks that it
has no imports, instantiates it with `instantiateCfg?` (the specification's allocation `prepare?`,
then the segment initialisation) and checks that the configuration has the empty code, and runs the
commands in order with `fuel` steps each of the kernel-evaluable interpreter `runInvokeK`. For
each command it checks that the arguments are typed (`invokeOkB`), that the run stopped at a
result, and the expected outcome. The proof (`Silmaril.Proofs.Project.Shapes.WasmWast`) uses:

* `instance_of_cfg` (below): the checker's instantiation is `Instance`, and its store is well
  typed (`Game.instantiateCfg?_configOk`);
* `runInvokeK_eq`, `runInvoke?_steps_noHost`, `runInvoke?_stopped`, `runInvoke?_sound`: the
  stopped run is a host-free normal form, and the next store is well typed;
* `Det.DStep.join'` and `nf_unique_of_join`: normal forms are unique, so a script reaches at
  most one state (`scriptAt_unique`) and every normal form of the command is the one found.

### Single-module files on the specification's `Instantiate`

Until this change the single-module files stated their script state with `instantiateOnce?` in
the empty store: a function of silmaril-lean that allocates every global once, while the
specification's `$instantiate` allocates every global twice (`$evalglobals`, then
`$allocmodule`). The two agree exactly only on modules without globals; with globals, only up to
a renaming of global addresses. So no lemma `instantiateOnce? ∅ m = some x → Instantiate …` can
make rows exact for every module, and the shape now states the specification directly:
`Instance P m s mi` (above) is `Instantiate P Det.noHost (Game.importStore []) m [] c₀` run to the
empty code, at the row's profile (`profile o` in `ScriptAt`, `Profile.spec nd r` in
`ScriptAtS`). The row statements are textually unchanged (their shapes' arguments are the same);
what they mean is now relative to `Instantiate` and `Step` only, also for modules with globals.

The checkers instantiate as the specification does, with `instantiateCfg?` (`prepare?`, globals
allocated twice), as the linked scripts already did:

```lean
theorem instance_of_cfg (hv : validate? m = some mt) (himp : mt.imports = [])
    (hcfg : instantiateCfg? (Game.importStore []) m [] = some (c, mi)) (hc : c.code = []) :
    Instance P m c.store mi ∧ StoreOk c.store                 -- every profile P
theorem instance_unique (h : Instance (profile o) m s mi) (h' : Instance (profile o) m s' mi') :
    s = s' ∧ mi = mi'
```

(`Silmaril.Proofs.Project.Shapes.WasmWast`): `instantiateCfg?_sound` gives the `Instantiate`
configuration and its run to the checker's configuration, `Game.instantiateCfg?_configOk` its
typing; uniqueness from `instantiate?_evalConst_complete` (`Instantiate` has one configuration)
and `nf_unique_of_join` (host-free normal forms at `profile o`). Under `Profile.spec`
(`scriptSK`) the checker also requires no element or data segments and no start function, so the
`Instantiate` configuration has no code and the state is unique without determinism
(`instance_unique_nil`); every module of the six float files is such a module. `Reaches.spec`
lifts an instance at `profile o` to `Profile.spec nd {}` (`instance_spec`: `Instantiate` does
not depend on the profile, `instantiate?_iff`; the run refines, `Steps.deterministic_refines_spec`).

The kernel checks themselves are the same `decide +kernel` evaluations in the same row modules;
only the checker definitions changed, so the rows were rebuilt, not regenerated. In the slice no
instantiated module of a single-module file has a global (the three `i32.wast` modules with
globals are `assert_invalid` modules, never instantiated), so no row's verdict depends on the
change; the statements are exact for modules with globals as well. The former `exportsScalar`
check (needed only for `Game.IsInstance.ok`) is gone. `Instance.of_cfg` and `Instance.unique`
restate the two theorems in `….WasmWast.Thms`.

`#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for `instance_of_cfg`,
`instance_unique`, `instance_unique_nil`, `instance_spec`, `ScriptHolds.of_kernel`,
`ScriptHolds.of_kernelKM`, `scriptK_of_scriptKM`, `ScriptAt.unique`, `ScriptHoldsS.of_kernel`,
`Reaches.spec`, and the rows `….I32.l37`, `….I32.script0`, `….Traps.l17`, `….Address.l104`
(`KMem`), `….F32.l19`, `….F32.l19_terminates` (`Profile.spec`).

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
`m` from `importStoreKM` (the empty `KMem` store) with the generic `instantiateCfg?`, and runs
each command with `runInvokeKR`, the structural driver `Verify.Kernel.runK` over the generic
interpreter head step `interpHead o`. The statement `ScriptHolds o m cmds` is unchanged: it is
about the `ByteArray` semantics (`Instance`, `InvokeNF` over `Step (profile o)`). The proof
(`Silmaril.Proofs.Project.Shapes.WasmWast.scriptK_of_scriptKM`) maps every `KMem` store to its
`ByteArray` reading `Store.toBytes`:

* `importStoreKM.toBytes = Game.importStore []` (by `rfl`) and `instantiateCfg?_toBytes`: the
  `KMem` instantiation, read through `toBytes`, is the `ByteArray` instantiation;
* `runK_eq` (now stated at any representation), `runI_toBytes` and
  `(invoke s a vs).toBytes = invoke s.toBytes a vs`: each `KMem` run, read through `toBytes`, is
  `runInvoke?` on the `ByteArray` store, with the same stop flag and outcome (`runInvokeK_toBytes`);
* `invokeOkB` reads only the functions of the store, which `toBytes` keeps.

So `scriptKM … = true` gives `scriptK … = true`, and `ScriptHolds.of_kernel` does the rest. The
kernel never evaluates a `ByteArray` memory.

Every answer depends only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms Silmaril.Project.WasmWast.I32.l37`, `….Traps.l17`, `….I32.script0`,
`….Address.script0`, `….Address.script3`, `….Address.l104` (`assert_return`), `….Address.l192`
(`assert_trap`), `ScriptHolds.of_kernel`, `ScriptHolds.of_kernelKM`, `scriptK_of_scriptKM`,
`Reaches.always`, `ScriptHolds.always`, `ScriptAt.unique`; and for the rejections
`ValidatorRejects.of_kernel`, `DecoderRejects.of_kernel`, `ValidatorRejects.not_valid` and all
113 `assert_invalid` answers, e.g. `….I32.l444`, `….I64.l457`, `….Address.l214`). The same holds
for the specification-profile theorems and rows: `StraightLine.nf`, `.reaches`,
`.not_diverges`, `.extends_nf`, `.fn?_sound`, `ScriptHoldsS.of_kernel`,
`ScriptHoldsS.terminatesAll`, `numericSet?_sound`, `Reaches.spec`, `Returns.allowedExists`,
`….F32.check0`, `….F32.l19`, `….F32.l19_terminates`, `….F32.l51` (`nan:canonical`), `….F32.l52`
(`nan:arithmetic`), `….F32.l2523` (`assert_invalid`), `….F64.l52`, `….F64.l52_terminates`,
`….Conversions.l78` (`assert_trap`), `….Conversions.l78_terminates`, `….Conversions.l560`,
`….F32Bitwise.l10`.

## The slice and its counts

WebAssembly/spec at `608711107b7f1edb13efd57b7d79b49477462d36` (the archive pinned in
`tools/wasm-tools/tests/pins.sh`, SHA-256
`22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b`):
`test/core/{i32,i64,int_exprs,fac,traps,address}.wast` at the deterministic profile and
`test/core/{f32,f64,f32_bitwise,f64_bitwise,float_misc,conversions}.wast` at the specification profile. Each module is the binary that the
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
| `f32.wast` | 2513 | 2511 | 2 | 0 |
| `f64.wast` | 2513 | 2511 | 2 | 0 |
| `f32_bitwise.wast` | 363 | 363 | 0 | 0 |
| `f64_bitwise.wast` | 363 | 363 | 0 | 0 |
| `float_misc.wast` | 470 | 470 | 0 | 0 |
| `conversions.wast` | 618 | 618 | 0 | 0 |
| **total** | **8098** | **8089** | **9** | **0** |

Commands are every command after a module (`module` commands themselves are not counted).

The linked files (one script per file, [Linked scripts](#linked-scripts-imports-register-and-the-spectest-host)):
every command of the file but its `module` commands.

| file | commands | proved | context | unsupported | undetermined |
|---|---|---|---|---|---|
| `imports.wast` | 150 | 128 | 6 | 16 | 0 |
| `linking.wast` | 142 | 133 | 9 | 0 | 0 |
| `exports.wast` | 41 | 41 | 0 | 0 | 0 |
| `start.wast` | 15 | 10 | 4 | 1 | 0 |
| `global.wast` | 115 | 111 | 1 | 3 | 0 |
| `data.wast` | 36 | 35 | 1 | 0 | 0 |
| `elem.wast` | 77 | 73 | 4 | 0 | 0 |
| **total** | **576** | **531** | **25** | **20** | **0** |

Before host references ([above](#host-references-refextern-n-and-reffunc)): 474 proved, 22
context, 29 unsupported, 51 undetermined (`global.wast` 70 proved, 38 undetermined; `elem.wast`
57 proved, 13 undetermined).

Before the scripts went on after a segment trap (the residual store, above): 392 proved, 16
context, 32 unsupported, 136 undetermined; `linking.wast` 93, `data.wast` 20, `elem.wast` 30
proved.

The 531 proved rows: 199 `assert_return` (`host.returns_only`), 2 `assert_return` with the
`(ref.func)` pattern (`host.returns_matching`, `global.wast` lines 660 and 661), 34 `assert_trap`
(`host.traps_only`), 136 `assert_unlinkable` (`host.unlinkable`, strength `link`), 34
`assert_uninstantiable` (`host.uninstantiable`: 32 segment initialisations that trap, in
`linking.wast`, `data.wast` and `elem.wast`, and 2 start functions that trap, `start.wast` and
`linking.wast` line 593), and 126 rejections (122 `assert_invalid`, 4 binary `assert_malformed`,
tool-level, as above). The rows after a segment trap read the residual store: `linking.wast`
lines 410 and 411 call, through the shared table, the element that the failed module stored
before its out-of-bounds data segment trapped (`….Linking.l410`, `….Linking.l411`). Every call of
a print function in these scripts is a host call answered by `Spectest.host` and logged: the rows
at lines 97, 98 and 116 of `imports.wast` print 15 values (`report.json` `printed`, from the
probe), and the start functions of three modules of `start.wast` call `print_i32` (twice) and
`print` (no values). Besides the 531 rows of the suite there are the 4 hand-written rows
`silmaril.wasm_wast.spectest_host.*` (3 `host.returns_only`, 1 `host.log_is`). The 25 `context`
rows are 19 `register` commands and 6 bare actions (`start.wast`, `data.wast`, `elem.wast`), run
as part of every later row's prefix. The rows with host references: `global.wast` lines 235
(`set-mr` with `(ref.extern 10)`, no results) and 241 (`get-mr` returns `(ref.extern 10)`),
`elem.wast` lines 1019, 1020 (`set` with `(ref.extern 42)`, `(ref.extern 137)` into the
`externref` table of `$m`), 1022, 1023 (`get` returns them) and 1030 (after a module importing
that table re-initialises index 0 with `(ref.null extern)` by an element segment, index 1 still
holds `(ref.extern 137)`); e.g. `….Global.l241 : host.returns_only neverFail (pre cmds 32)
(.invoke .cur "get-mr" []) [Val.ref (.extern (.host 10))]`.

| count | status | reason |
|---|---|---|
| 20 | unsupported | `assert_malformed` on text (as above) |
| 0 | undetermined | — |
| 0 | mismatch | — |

`names.wast` is left out for kernel time: the kernel check of its third module (7.6 KB, 480
exports) exceeded 33 GB of memory within two minutes; the native probe passes all its 482
`assert_return` and the 2 calls of `spectest.print_i32` of its last module.

Kernel time of the linked files (one `lake build` of all row modules after the change to the
specification's instantiation, 2-vCPU sandbox, two modules at a time): `Imports.Thms` 74 s (161
modules, 128 `assert_unlinkable` among them), `Global.Thms` 130 s (the whole script now, 41
rejection rows), `Elem.Thms` 52 s, `Linking.Thms` 42 s, `Data.Thms` 11 s, `Exports.Thms` 8 s,
`Start.Thms` 4 s. The check of `global.wast`'s script alone (one
`decide +kernel` of `decodesB && scriptLK …`) takes 104 s and 20.7 GB peak RSS; the kernel's
cache shares the decoding of each module between `decodesB` and the checker (with separate
`decode` theorems the two together took about 290 s). Decoding dominates: the modules are
read by `decode?` in the kernel.

The six float files (6840 commands, 6836 proved): 6716 `assert_return` and 67 `assert_trap` at
`Profile.spec` (`returns_allowed_all`/`traps_all` plus `terminates_all`, so 13 566 rows), and 53
`assert_invalid` (`validator_rejects`, tool-level: 11 in each of `f32.wast`/`f64.wast`, 3 in each
bitwise file, 25 in `conversions.wast`). The 6716 `assert_return` expectations are 4885 exact
values, 895 `nan:canonical` and 936 `nan:arithmetic`; each `nan:canonical` command's class is
the canonical NaNs, and each `nan:arithmetic` command's class the arithmetic NaNs (an operand is
the non-canonical `nan:0x200000`, or `nan:0x4000000000000` for `f64`). Not in the slice:
`f32_cmp.wast`, `f64_cmp.wast` (4800 comparisons with deterministic `i32` results, in the
fragment, left out for kernel time: about 9 minutes of row elaboration), and `float_exprs.wast`,
`float_literals.wast`, `float_memory.wast` (constants, memory and compound expressions: outside
the straight-line fragment).

At the deterministic profile, the
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
| 8 | unsupported | `assert_malformed` on text: no binary; the WAT front end has no completeness theorem and its syntax error also covers unsupported text ([above](#rejections-tool-level)); 2 in each of `i32`, `i64`, `f32`, `f64` (`(… .const nan:arithmetic)` and `nan:canonical` as constants) |
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
The float files at `Profile.spec` (one `lake build`, 2-vCPU sandbox, two modules at a time):
`F32.Thms` about 300 s and `F64.Thms` 319 s (2500 commands, 5000 rows each), `Conversions.Thms`
133 s, `F32Bitwise.Thms` and `F64Bitwise.Thms` 19 s each, `FloatMisc.Thms` 55 s. The kernel evaluation of `scriptSK` on
all 2500 commands of `f32.wast`, with `decode0`, takes about 15 s (whole `lean` process 20 s);
the rest is the elaboration of the rows and their index facts. The index fact `cmdsJ[k]? = some
…` of a row is checked by `decide +kernel`: with `rfl`, the elaborator's unfolding of the list
made `F32.Thms` take over 10 minutes.

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
command in that module, then the command. For the six float files the script is the module and
the command alone: their modules have no memory, table, global or data (type, function, export,
code and name sections only), and every function is straight-line numeric (the kernel checker
requires it), so no earlier action can affect a command; with the earlier actions the scripts
grew quadratically (2500 commands per module). For an `assert_invalid` row the script is
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
(`--scripts` requires it) it regenerates all 8215 single scripts and the 7 linked-file scripts
and compares their SHA-256. `verify`
checks consistency of the record, not wasmtime's verdicts: those are re-obtained only by running
`oracle` again (in CI, `oracle --check`). `convert` also checks each unpacked spec file against
the SHA-256 that `report.json` records. The whole `oracle` run takes about 75 s on the
development sandbox (8222 scripts and the 19 upstream files).

**Linked files.** For a linked file the oracle runs **one script per file**: every command the
kernel ran, in order, as the file writes it (modules as `(module $name? binary …)` of the same
bytes, `register`, actions and assertions with their original expectations, `assert_unlinkable`
and `assert_trap (module …)`), so each command sees exactly the context of its row. A command
passes when wasmtime gets past its line (`script_line`); every command of the file records the
file script's SHA-256 (`script: linked:<file>`). wasmtime uses its own `spectest` (one shared
instance of everything, also globals and functions), so its agreement is evidence about the
outcomes, not a proof about `Spectest.host`; where the two differ (identity of globals and print
functions) Wasm code cannot observe it. A rejection row passes when wasmtime rejects the module; wasmtime also compares its own
message with the file's, and for 6 `global.wast` rows only the wording differs ("global is
immutable: cannot modify it with `global.set`" for "immutable global", a parse error for
"malformed mutability"): those record `message: differs` with wasmtime's error.

Results:

* 8626 commands run: the 8620 kernel-proved and 6 context actions (4 of `start.wast`, 1 of
  `data.wast`, 1 of `elem.wast`; native only); **8620 of 8620** kernel-proved commands pass,
  among them the 531 of the linked files (405 in 7 linked-file scripts, 126 rejections in single
  scripts), with every `(ref.extern n)` argument and result and both `(ref.func)` results;
* before host references: 8568 commands run, 8563 of 8563 kernel-proved pass (474 of the linked
  files);
* before the residual store: 8485 commands run, 8481 of 8481 kernel-proved pass (392 of the
  linked files);
* earlier: 8089 commands run, all of them kernel-proved (1140 executions at `profile o`, 6783 at
  `Profile.spec`, 166 validator rejections);
* **8089 of 8089** kernel-proved commands pass under wasmtime: wasmtime also rejects each of the
  166 `assert_invalid` binaries. The 1253 earlier scripts and their verdicts are unchanged;
* wasmtime's `wast` runner keeps the patterns' meaning: `nan:canonical` passes only on
  `0x7fc00000`/`0xffc00000` (`f32`) and the `f64` analogues, `nan:arithmetic` on any NaN with the
  quiet bit set, and an exact float constant is compared as bits. It returns one NaN per
  command (on `f32.add` of `nan:0x200000` and `0`: `0x7fe00000`, the quieted operand), so its
  agreement is agreement of one member of the allowed set, not of the whole result set;
* the unmodified upstream files: `int_exprs`, `fac`, `traps`, `address`, `f32_bitwise`,
  `f64_bitwise`, `float_misc`, `conversions` pass. `i32`, `i64`, `f32` and `f64` fail on a text
  `assert_malformed` whose message wasmtime's text parser words differently (`nan:arithmetic`
  in an `i32.const`: "expected a i32", in an `f32.const`: "expected a float", not "unexpected
  token"), not on an execution or validation command. Of the linked files, `imports`,
  `linking`, `exports`, `data` and `elem` pass; `start.wast` fails on a text
  `assert_malformed` (wasmtime: "attempted to parse a wasm module with a component parser", not
  "multiple start sections") and `global.wast` on an `assert_invalid` whose message wasmtime words
  differently (above).

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

* `tools/wasm-wast/regress/wrong-{return,trap,invalid,malformed,nan-canonical,signed-zero}.wast`,
  committed, each with one directive marked `;; WRONG` (`assert_return` of 2 where the function
  returns 1, `assert_trap` on `6 / 3`, `assert_invalid` on a valid module, `assert_malformed` on
  the empty module, `nan:canonical` for `f32.add` of the non-canonical `nan:0x200000` and `0`,
  whose results are arithmetic NaNs only, and `0` for `f32.neg 0`, which is `-0`). wasmtime
  must fail on each, and on the marked line (so the failure is the wrong expectation, not a
  parse error); the NaN script fails with "expected canon-nan / 0x7fc00000, actual NaN /
  0x7fe00000", the zero script with "expected 0 / 0x00000000, actual -0 / 0x80000000";
* `regress/wrong-linked-state.wast`: **cross-module state**. `$Mem` exports a memory and a
  mutable global and is registered; `$Writer` imports both (and `spectest.print_i32`), stores 42
  at address 0 and sets the global to 7; `$Reader` imports the same memory and global and reads
  them. The marked line expects 43 where the other module wrote 42; wasmtime must fail on it
  ("expected 43 / 0x…2b, actual 42 / 0x…2a"). `regress/right-linked-state.wast`, the same with
  42, must pass;
* `regress/wrong-spectest-shared.wast`: **spectest's shared memory**. `$W` and `$R` import
  `spectest`'s `memory` separately; after `$W` stores 42, the marked line expects 0 from `$R`'s
  load (what a memory per import would give). wasmtime must fail on it.
  `regress/right-spectest-shared.wast` (42) must pass; it is also the kernel-checked script of the
  rows `silmaril.wasm_wast.spectest_host.*`;
* `regress/right-control.wast`: the same modules with right expectations (`nan:arithmetic`,
  `nan:canonical` for `f32.add` of the canonical `nan` and `0`, `-0`); wasmtime must pass;
* `regress/wrong-segment-trap-state.wast`: **the residual store**. `$Shared` exports a table and a
  memory and is registered; the module of an `assert_trap` imports both, its element segment
  stores a function at table index 0, its first data segment writes 42 at address 0, and its
  second data segment is out of bounds and traps; `$Reader` imports the same table and memory. The
  marked line expects 0 (a rolled-back memory); wasmtime must fail on it ("expected 0, actual
  42"). `regress/right-segment-trap-state.wast` (42; the stored function is callable, index 1
  traps) must pass;
* `regress/wrong-externref.wast`: **a host reference**. A module stores its `externref` argument
  in a mutable global and a table; after `(invoke "set" (ref.extern 1))` the marked line expects
  `(ref.extern 2)` from the global; wasmtime must fail on it ("expected 2 found 1").
  `regress/right-externref.wast` (`(ref.extern 1)`) must pass;
* six generated mutants: the first `assert_return` script of `oracle_scripts` with its result
  plus one, the first `assert_invalid` script with its module replaced by the empty (valid)
  module, the first `nan:arithmetic` script of an `add` of a non-canonical NaN with
  `nan:canonical` instead, and, in the linked script of `linking.wast`, the first
  `assert_return` on a current module that imports from another registered module, plus one,
  with the script cut after it (wasmtime must fail on that line), and in the same script the
  first `assert_return` after a segment-trapping `assert_trap (module …)` (line 410, which reads
  the residual table), plus one (wasmtime must fail on that line), and in the linked script of
  `global.wast` the first `assert_return` expecting `(ref.extern n)` (line 241, `(ref.extern 10)`)
  with `(ref.extern 11)` (wasmtime must fail on that line). wasmtime must fail on each.

Locally: `oracle --check` and `verify --scripts` pass, `regress` passes (21 scripts: 10 committed
wrong, 5 committed controls, 6 generated wrong). Tampering
with one committed verdict in `oracle.json` makes `oracle --check` exit 1, and making
`wrong-return.wast` right makes `regress` exit 1 ("wasmtime ACCEPTS a wrong expectation").

Cost: downloads of about 35 MB on a cold cache (spec archive 15.0 MB, wasm-tools and wasmtime
archives), then `convert` 0.5 s, `oracle --check` about 63 s (8215 single scripts, 7 linked-file
scripts, 19 upstream files), `verify --scripts` and `regress` about 1 s each on the development
sandbox; the job has a 5-minute timeout. It grows linearly with the number of scripts (about
7 ms each); a linked file adds one script, not one per command.

## Trust boundary

* **Core vs the specification.** Rows are about silmaril-lean's `Execution.Core.Step`. Its
  agreement with the SpecTec transcription of Wasm 3.0 is partly proved, and the whole-step
  simulation goals are open (`docs/projects/wasm.md`).
* **Instantiation.** Every statement uses the specification's `Instantiate` itself: `Instance`
  in the single-module files (in the empty store), `InstNF` in the linked files (globals allocated
  as `$instantiate` allocates them, segment code and start call run by `Step`); the checkers'
  `instantiateCfg?` is related to it by `instantiateCfg?_sound`. `Instantiate` is silmaril-lean's
  transcription of `$instantiate` (with the documented closing of global types over the allocated
  types), not proved equal to the SpecTec rule.
* **Profiles.** The integer, control and memory rows are at `profile neverFail`; the float rows
  at `Profile.spec nd r` (the theorems hold for every `nd` and `r`; the rows state `Profile.spec`'s
  defaults). A `Profile.spec` row quantifies over every run of the specification's NaN choices;
  wasmtime makes one.
* **The fragment** of the float rows is the straight-line numeric functions; the kernel checker
  verifies it per function (`StraightLine.fn?_sound`), so a function outside it is a failed
  check, not a weaker claim.
* **`KMem` rows** (`address.wast`) are kernel evaluations on `KMem` stores, carried to the
  `ByteArray` statements by proved simulations (`scriptK_of_scriptKM`): no extra assumption.
* **Modules** of the single-module files must be valid, with no imports; the checkers also
  require the instantiation code to end empty (so no start function in practice), and, under
  `Profile.spec`, no element or data segments. In the **linked files** modules may import (resolved by name
  through the registry, typed by `ExternAddrOk`) and have start functions; a segment trap during
  instantiation is a trap of the `Instantiate` configuration, and the script goes on with the
  residual store.
* **The `spectest` environment** of the linked files is the concrete typed host `Spectest.host`
  with its registry (`resolve?`, `Spectest.lookup?`) and its observation (the host-call log), an
  explicit parameter of every linked row (`Step (profile o) Spectest.host`, `Init`). It is a
  transcription of the reference interpreter's `spectest.ml` (fresh print functions and globals per
  import, shared table and memory, print calls returning no values with the store unchanged);
  the transcription is checked against the source by reading, not proved. The rows are claims
  about this host, not about arbitrary hosts, and nothing here says that a context cannot tell it
  from another `spectest` implementation. The printed output is the log projection
  `Spectest.printed`, not bytes (the text of a value is the reference interpreter's printer).
* **Name resolution** (`resolve?`) and the script semantics of `register`, named modules and
  `get` are the reference interpreter's script semantics, transcribed; they are not part of the
  Wasm specification.
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
* `Silmaril/Project/Shapes/WasmWastSpec/{Defs,Thms}.lean`,
  `Silmaril/Proofs/Project/Shapes/WasmWastSpec.lean`: the allowed sets, the shapes at
  `Profile.spec`, the result classes and the checker `scriptSK` with its soundness, and the
  refinement `Reaches.spec`.
* `Silmaril/Wasm/Execution/StraightLine/{Defs,Thms}.lean`,
  `Silmaril/Proofs/Wasm/Execution/StraightLine.lean`: every run of a straight-line numeric
  function, at any profile.
* `Silmaril/Project/WasmWast/<File>/{Defs,Thms}.lean` (generated): the bytes, modules and
  command lists, then the kernel theorems and the rows `silmaril.wasm_wast.<file>.l<line>`.
  `Silmaril.Project.WasmWast.Thms` imports them all, and `silmaril.toml` puts it in the project
  dump.
* `Silmaril/Project/Shapes/WasmWastRef/{Defs,Thms}.lean`,
  `Silmaril/Proofs/Project/Shapes/WasmWastRef.lean`: host references, `(ref.extern n)` arguments
  (`argsOkR`, `invokeOkRB`, `invokeOkRB_sound`) and the result patterns `Pat` (`matchAll_sound`).
* `Silmaril/Project/Shapes/WasmWastHost/{Defs,Thms}.lean`,
  `Silmaril/Proofs/Project/Shapes/WasmWastHost.lean`: the typed host `Spectest.host`, the registry
  `resolve?`, the script contexts with the host-call log, the shapes `host.*`, the checkers
  `scriptHK`, `logHK` and their soundness; `Silmaril/Wasm/Abstract/HostDet/{Defs,Thms}.lean`
  (proofs `Silmaril/Proofs/Wasm/Abstract/HostDet.lean`): `HostDet`, logged runs `LStep`, and
  determinism, uniqueness of normal forms and logs, and termination with a deterministic host.
  `Silmaril/Project/WasmWast/SpectestHost/{Defs,Thms}.lean`: the hand-written rows.
* `Silmaril/Project/Shapes/WasmWastLink/{Defs,Thms}.lean`,
  `Silmaril/Proofs/Project/Shapes/WasmWastLink.lean` (superseded, no rows): `Spectest.module`, the
  closed-module script contexts and runs, the `link.*` shapes, the checker `scriptLK` and its soundness (with `nf_unique`,
  `nf_always` for the normal forms of any configuration); `Silmaril/Wasm/Game/InstantiateTyped/Thms.lean`
  (proofs `Silmaril/Proofs/Wasm/Game/Instantiate/Typed.lean`): `instantiateOnce?_configOk`
  (instantiation against typed imports is typed) and `importStore_nil_ok`, in a small header of
  their own so that the widely imported `Wasm.Game.Instantiate.Thms` and
  `Project.Shapes.WasmWast.Thms` are unchanged (no rebuild of their importers).
* `Silmaril/Wasm/Execution/InstantiateTrap/{Defs,Thms}.lean` (proofs
  `Silmaril/Proofs/Wasm/Execution/InstantiateTrap.lean`): `initSegmentsR?`, `instantiateT?`,
  `instantiateOnceT?`, `instantiateCfg?` and their soundness and `toBytes` theorems;
  `Silmaril/Wasm/Game/InstantiateTrap/Thms.lean` (proofs
  `Silmaril/Proofs/Wasm/Game/InstantiateTrap.lean`): completeness (`instantiateT?_ne_fail_iff`),
  typing (`instantiateCfg?_configOk`) and single allocation with globals
  (`instantiateOnceT?_trap_spec`, `instantiateOnceT?_trap_outcome`).
  `Silmaril/Wasm/Execution/MemRep/Inst/Thms.lean` gains `initElemSeg?_toBytes` and
  `initDataSeg?_toBytes` (restated from its proofs module).
* `examples/wasm-wast/report.json` (every command: inputs, expectation, observation, status,
  reason, row, claim strength `only`, `all` or `tool`; for a proved execution row its `profile`,
  its `allowed` set and its `claims`, each with a kind: `only`, `all`, `terminates`), and
  `examples/wasm-wast/oracle.json`. For a float row the observation is the class of the
  specification's result set (`values f32:…`, `nan:canonical f32`, `nan:arithmetic f32`, `trap`).
* `tools/wasm-wast/regress/*.wast`: the oracle's wrong-expectation regression and its control;
  `.github/workflows/ci-wast-oracle.yml`: the CI oracle job.
* The explorer view `#/wast` (`tools/silmaril-project/src/project/explore/views/wast.js`, test
  `tests/explore/wast_view.test.mjs`) reads `wast/report.json` and `wast/oracle.json` next to
  the page, and the rows' answers from the database. Each proved row shows its claim strength
("semantic: Core reduction", "semantic: Core reduction under Profile.spec, every normal form" or
"tool-level rejection"), its profile and allowed set, and each claim with its kind ("every normal
form", "some run (existence)", "every run terminates") and problem. A row of a linked file also
shows its input on its target module (`$M.f(…)`, `get g`, `register "M" $M`) and its script
context: the registered names, the named modules, the current module and its imports, the
module's own imports for a module assertion, the host model (`spectest` = `Spectest.host`), the
observation and the printed values; `linking` labels the claim strength of `assert_unlinkable` rows, and
`context` the status of `register` and bare actions.

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

Float rows beyond straight-line numeric functions (`float_exprs`, `float_misc`, `float_memory`:
a general theorem about the spec profile's runs, e.g. a simulation of `Profile.spec` by the
deterministic interpreter up to NaN payloads, which needs the payloads not to reach control);
`f32_cmp`/`f64_cmp` (in the fragment, left out for kernel time); relaxed SIMD and grow failure
as allowed sets; `assert_invalid` relative to the specification (a proved bridge between
`ModuleOk` and the SpecTec validation rules); `assert_malformed` beyond the tool level (decoder
completeness; text: a WAT front end with a completeness theorem and an error that separates
malformed from unsupported text); the WAST reference patterns other than exact values and
`(ref.func)` (`(ref.extern)`, `(ref.any)`, …, `either`) and `(ref.host n)` arguments (none in the
slice); `names.wast` (kernel memory); the `env` virtual module of the reference interpreter;
claims about printed output as text; and the rest of the suite.
