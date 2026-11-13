module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PackValid

/-!
# V2 validation implies `packOkI`: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.PackValid`; see `docs/projects/spectec/README.md`, "Round 7,
vec-erratum".

* `packOkI_of_immediatesValid`: the syntactic side conditions of V2's `syntax instr`
  productions imply `BodyTyp.packOkI` at every depth.
* **`packOkI_of_instrOk`**, `packOkI_of_instrsOk`, `packOkI_of_exprOk`, **`packOkI_of_funcOk`**,
  **`packOkI_of_moduleOk`**: V2 typing implies it, for instructions, sequences, expressions,
  function bodies and every function of a valid module.
* **`invokeOkS_of_valid`**: `BodyTyp.InvokeOkS` from bounded types, typed names and a store
  whose Wasm functions are valid (`FuncsValid`), with no `packOkI` hypothesis.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.PackValid.packOkI_of_moduleOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.PackValid.packOkI_of_moduleOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.PackValid.invokeOkS_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.PackValid.invokeOkS_of_valid
