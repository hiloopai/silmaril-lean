module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Mono.Eval
public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Mono.Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoDerive
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoName

/-!
# Monotonicity across the 2.0 `$utf8` erratum: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Utf8Mono`; see `docs/projects/spectec/README.md`, "fwd20
".

* `Raw/…/Utf8Mono/Eval`, `Raw/…/Utf8Mono/Typ`: for two environments that agree everywhere but at
  one definition `x₀`, at which `e₂` answers at least what `e₁` answers (`EnvExt`), every member
  of the evaluator and of the typing block answers in `e₂` at least what it answers in `e₁`
  (`extMonoAt`, `extMonoTypAt`). Round 7's `Round7/Utf8/Mono` and `MonoTyp`, for any pair.
* `Utf8MonoCall`: in any environment with the 2.0 clauses of `$utf8`, `$utf8` never returns on a
  non-empty list (`tryClauses_utf8_single`, `tryClauses_utf8_long20`), returns `[]` or runs out
  of fuel on `[]` (`tryClauses_utf8_nil20`), and is below the primitive `utf8Call` at every fuel
  (`utf8_le20`).
* `Utf8MonoEnv`: `simEnv20 B`/`utf8Env20 B` and `simEnv20T B`/`utf8Env20T B` are `EnvExt` pairs
  at `$utf8` (`envExt20`, `envExt20T`); `storeB P` leaves `$utf8` uninterpreted (`storeB_utf8`).
* `Utf8MonoDerive`: typing and positive derivations move (`typedV_ext`, `dderivesB_ext`); a step
  moves when its `otherwise` premises do (`sstepB_ext`). Every `Good20B` configuration is
  `Good20BU` (`good20BU_of_good20B`), its image is typed in `utf8Env20T` (`typed20U_of_good20B`),
  and its V2 steps are steps of `utf8Env20T` under `ElseMono` (`fwd_good20B_utf8T`,
  `runU_good20B`).

* `Utf8MonoName`: in `simEnv20 B` a string is a `name` exactly when it is empty
  (`typedV_name20_iff`), so every export of the frame's module of a `Good20B` configuration is
  named `""` (`good20B_names_empty`).

`Task.fwdU20` (the forward theorem from `Good20BU`, which admits non-empty export names) is open.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.extMonoAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.extMonoAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.extMonoTypAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.extMonoTypAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.tryClauses_utf8_long20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.tryClauses_utf8_long20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.utf8_le20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.utf8_le20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.envExt20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.envExt20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.envExt20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.envExt20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.good20BU_of_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.good20BU_of_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.fwd_good20B_utf8T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.fwd_good20B_utf8T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.typedV_name20_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.typedV_name20_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.good20B_names_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.good20B_names_empty
