module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypFlat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypPair
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypOps
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypBody

/-!
# IL typing of erased function bodies: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.BodyTyp`; see `docs/projects/spectec/README.md`, "fwd20
".

* `BodyTypFlat`, `BodyTypPair`: the covered instructions with no payload, one or two indices, a
  list of labels, value types, a reference type or a constant are `admininstr`s of `simEnv20 B`,
  with no hypothesis (`typedA_br`, `typedA_callIndirect`, `typedA_brTable`, `typedA_select`, …).
* `BodyTypOps`: the numeric operators at their number types (`typedA_intBinOp`, …), `CVTOP`
  wherever V2 defines the conversion (`typedA_cvtOp`, through `ne_of_toShared`), and the loads,
  packed ones below their type's width (`typedA_intLoad`, `hasTyp_loadop`, checked by evaluation
  at the ten pairs).
* `BodyTypBody`: **`typedA_eD`**: every `StoreBulk.ctrlOkB` instruction whose packed loads are
  below their width (`packOkI`), erased by `StoreDeep.eD`, is typed; **`typedV_body_eD`**: so is
  such a body, as an `instr*`. **`invokeOk_of_S`** discharges the body-typing component of
  `StoreBulk.InvokeOk`, and **`good20B_invoke_okS`** gives `Good20B` at `val* (CALL_ADDR a)` from
  `InvokeOkS` (bounded types, typed names, `packOkI` bodies), `StoreOkB` and `StoreSmall`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedA_cvtOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedA_cvtOp

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.hasTyp_loadop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.hasTyp_loadop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedA_eD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedA_eD

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedV_body_eD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.typedV_body_eD

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.invokeOk_of_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.invokeOk_of_S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.BodyTyp.good20B_invoke_okS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.BodyTyp.good20B_invoke_okS
