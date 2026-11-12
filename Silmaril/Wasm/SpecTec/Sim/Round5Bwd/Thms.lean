module

public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Bwd.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, track bwd: what is proved

* `Round5.Bwd.famBwdV_of_hostSteps`: `Round4Int.FamBwdV` for the concrete builtins from
  `HostStepsV` (the backward `Step` 8 and 9, the host-call rules) alone. Every other rule of
  `FamBwdV` is proved (`fam_pure`, `fam_read`, `fam_step`), without `Bwd.BwdHyps`.
* `Round5.Bwd.hostStepsV_of_hostInv`, `famBwdV_of_hostRespects`: `HostStepsV`, hence
  `FamBwdV`, for hosts that respect the encoding (`Prims.HostRespects`).

* `Round5.Bwd.not_remainingV`, `not_parts`, `not_parts_hyp`: `Round4Read.RemainingV` is
  **false** for every `B` (`array.fill-zero` fires through `otherwise` at a dangling array on
  the empty store, where Core is stuck), so `Round4Int.Parts` is unsatisfiable and
  `Round4Int.wholeStepValid_of_parts` is vacuous.
* `Round5.Bwd.readValidR_of_configOk`, `readValidR_of_bounded`: Core validity gives reference
  liveness, hence `ReadValidR`; `readValidR_ctxClosed`.
* `Round5.Bwd.read_doneR`: `Step_read` 73, 78, 84, 86–89, 94, 95, 99 backward, for the
  concrete builtins (84 under reference liveness).
* `Round5.Bwd.backward_validR`, `oneStep_of_partsR`, `wholeStepValid_of_partsR`: the frozen
  target from the restated `PartsR` (`partsR_of_parts`: no stronger than `Parts`).

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.famBwdV_of_hostSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.famBwdV_of_hostSteps

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.famBwdV_of_hostRespects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.famBwdV_of_hostRespects

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.not_parts_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.not_parts_hyp

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.readValidR_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.readValidR_of_bounded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.read_doneR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.read_doneR

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.wholeStepValid_of_partsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.wholeStepValid_of_partsR

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Bwd.partsR_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Bwd.partsR_of_parts
