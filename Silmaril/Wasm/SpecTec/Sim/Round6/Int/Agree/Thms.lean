module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Int.Agree.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 3): what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Int`; see `docs/projects/spectec/README.md`.

* `openR_backend_of_agree`, `wholeStepValidR_backend_of_agree`, `runsR_backend_of_agree`:
  `Target.OpenR Int.backend`, `Round6.Task.wholeStepValidR Int.backend` and its multi-step
  corollary from the interpreter half `RefOkV.Agree` (open), through track refokbv-prove's
  `RefOkV.refOkBV_of_agree` and `CastsV.*_of_refOkBV`.
* `openR_backend_of_agreeTy`, `wholeStepValidR_backend_of_agreeTy`, `runsR_backend_of_agreeTy`:
  the same from the store-free `RefOkV.AgreeTy` (open), through `RefOkV.agree_of_agreeTy`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.openR_backend_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidR_backend_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidR_backend_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsR_backend_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.runsR_backend_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend_of_agreeTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.openR_backend_of_agreeTy

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidR_backend_of_agreeTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidR_backend_of_agreeTy

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsR_backend_of_agreeTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.runsR_backend_of_agreeTy
