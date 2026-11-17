# WAST commands of the spec test suite as kernel-checked problems

A slice of the WebAssembly specification test suite, command by command, as problem rows of
the standard shapes `silmaril.shapes.wasm.wast.*`. Each `assert_return`/`assert_trap` row is
answered by a theorem about Core reduction (`Silmaril.Wasm.Execution.Core.Step`), checked by the
Lean kernel: at the deterministic profile for the integer, control and memory files, and at the
**specification profile** `Profile.spec` (the specification's NaN result sets, with
`nan:canonical`/`nan:arithmetic` as allowed sets) for the float and conversion files
([Under the specification profile](#under-the-specification-profile)). Each `assert_invalid` row is answered by a **tool-level** theorem: silmaril-lean's
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

**The checker.** `scriptSK m cmds` validates and instantiates `m` (as `scriptK`) and checks, for
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
(`--scripts` requires it) it regenerates all 8089 scripts and compares their SHA-256. `verify`
checks consistency of the record, not wasmtime's verdicts: those are re-obtained only by running
`oracle` again (in CI, `oracle --check`). `convert` also checks each unpacked spec file against
the SHA-256 that `report.json` records. The whole `oracle` run takes about 52 s on the
development sandbox (8089 scripts and the 12 upstream files).

Results:

* 8089 commands run, all of them kernel-proved (1140 executions at `profile o`, 6783 at
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
  token"), not on an execution or validation command.

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
* `regress/right-control.wast`: the same modules with right expectations (`nan:arithmetic`,
  `nan:canonical` for `f32.add` of the canonical `nan` and `0`, `-0`); wasmtime must pass;
* three generated mutants: the first `assert_return` script of `oracle_scripts` with its result
  plus one, the first `assert_invalid` script with its module replaced by the empty (valid)
  module, and the first `nan:arithmetic` script of an `add` of a non-canonical NaN with
  `nan:canonical` instead. wasmtime must fail on each.

Locally: `oracle --check` and `verify --scripts` pass, `regress` passes (10 scripts). Tampering
with one committed verdict in `oracle.json` makes `oracle --check` exit 1, and making
`wrong-return.wast` right makes `regress` exit 1 ("wasmtime ACCEPTS a wrong expectation").

Cost: downloads of about 35 MB on a cold cache (spec archive 15.0 MB, wasm-tools and wasmtime
archives), then `convert` 0.5 s, `oracle --check` about 52 s, `verify --scripts` and `regress`
about 1 s each on the development sandbox; the job has a 5-minute timeout. It grows linearly with
the number of scripts (about 7 ms each).

## Trust boundary

* **Core vs the specification.** Rows are about silmaril-lean's `Execution.Core.Step`. Its
  agreement with the SpecTec transcription of Wasm 3.0 is partly proved, and the whole-step
  simulation goals are open (`docs/projects/wasm.md`).
* **Instantiation** is `instantiateOnce?` (a function, related to the relational `Instantiate`
  by `instantiateOnce?_steps`).
* **Profiles.** The integer, control and memory rows are at `profile neverFail`; the float rows
  at `Profile.spec nd r` (the theorems hold for every `nd` and `r`; the rows state `Profile.spec`'s
  defaults). A `Profile.spec` row quantifies over every run of the specification's NaN choices;
  wasmtime makes one.
* **The fragment** of the float rows is the straight-line numeric functions; the kernel checker
  verifies it per function (`StraightLine.fn?_sound`), so a function outside it is a failed
  check, not a weaker claim.
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
form", "some run (existence)", "every run terminates") and problem.

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
malformed from unsupported text); `assert_unlinkable`/`assert_uninstantiable`; imports and the
spectest host; `register`; and the rest of the suite.
