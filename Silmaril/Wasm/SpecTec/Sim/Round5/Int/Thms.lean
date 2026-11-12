module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass-1 integration: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Int`; see `docs/projects/spectec/README.md`.

* `typesB`: `Fwd.TypesB`, in every `simEnv B`.
* `wholeStepValidOk_of_partsOkR`: the restated target `Round5.Task.wholeStepValidOk` from
  `PartsOkR`; `partsOkR_of_partsOk`: `PartsOkR` is no stronger than `PartsOk`.
* `partsOkR_of_open`, `wholeStepValidOk_of_open`: the restated target from `Open`, the leaves
  still open after pass 1.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int.typesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int.typesB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int.wholeStepValidOk_of_partsOkR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Int.wholeStepValidOk_of_partsOkR

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int.partsOkR_of_partsOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int.partsOkR_of_partsOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int.partsOkR_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int.partsOkR_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int.wholeStepValidOk_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int.wholeStepValidOk_of_open
