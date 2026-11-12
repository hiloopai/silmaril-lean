module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HPair.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Witness

/-!
# Round 7, `BD`: a position-sensitive invariant for the host-call rules (round 7, pass 2, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HPair`; see `docs/projects/spectec/README.md`. Definitions (`NoPair`, `LFragP`, `stepPairOk`, `EasyP`, `OpenRMRestDP`) are in
`Round7/HPair/Defs.lean`.

* `step_pairOk`: kernel fact (`decide +kernel`) on the fixed wasm-3.0 script.
* `stepInvH_p`, `stepInvBH_p`: `Qp = LhsNoAtoms msAtoms ∧ LhsNoPair` is a `HStep.StepInvH` and a
  `HCasts.StepInvBH`.
* `forwardD_p`, `castsFwdD_p`, `castsBwdD_p`: `forward` and the casts at `BD` at `EasyP` sources;
  `easyP_of_easy`: `EasyP` contains `RMRed.Easy`.
* `wholeStepValidRM_of_restDP`: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDP`.
* `easyP_cfgP`, `not_easy_cfgP`: `nop; CALL_REF` over round 5's host-function store is `EasyP` and
  not `Easy`, so `EasyP` is strictly larger.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.step_pairOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_pairOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.forwardD_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forwardD_p

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.castsFwdD_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms castsFwdD_p

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.castsBwdD_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms castsBwdD_p

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.wholeStepValidRM_of_restDP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDP

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.easyP_cfgP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms easyP_cfgP

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HPair.not_easy_cfgP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_easy_cfgP

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
