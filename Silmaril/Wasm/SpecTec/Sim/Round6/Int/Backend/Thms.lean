module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Backend.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Int.Backend.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 2): what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Int`; see `docs/projects/spectec/README.md`.

* `openR_backend_of_refOkBB`, `wholeStepValidR_backend_of_refOkBB`, `runsR_backend_of_refOkBB`:
  `Target.OpenR Int.backend`, `Round6.Task.wholeStepValidR Int.backend` and its multi-step
  corollary from `Reading.RefOkBB`. **Vacuous**: the hypothesis is false
  (`not_refOkBB_family`, from `RefOkB.not_refOkBB`).
* `wholeStepValidRNC_backend`, **proved outright**: the target at the backend reading away from
  cast redexes. `wholeStepValidRNC_of_wholeStepValidR`: it is a restriction of the target.
* `runsRNC_backend`, **proved outright**: its multi-step corollary from sources that never reach
  a cast redex (`NoCastReach`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend_of_refOkBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.openR_backend_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidR_backend_of_refOkBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidR_backend_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsR_backend_of_refOkBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.runsR_backend_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.not_refOkBB_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.not_refOkBB_family

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidRNC_of_wholeStepValidR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidRNC_of_wholeStepValidR

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidRNC_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidRNC_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsRNC_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.runsRNC_backend
