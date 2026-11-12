module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Int.Assemble

/-!
# SpecTec ↔ Core 3.0, round 4 integration: what is proved

The frozen target `Round4.Task.wholeStepValid` is **not proved**. Proved here:

* `Round4Int.readValid_of_configOk`, `readValid_of_bounded`: Core validity (with the store
  bounds) gives `ReadValid`, at every depth of the code. So r4-read's 26
  dispatched `Step_read` rules hold from valid sources (`read_doneV_of_configOk`).
* `Round4Int.famBwdV_of_hyps`, `backwardUpToV_of_fam`, `backward_fam`, `backward_valid4`: the
  backward conjunct from the rule-level obligations `FamBwdV` and `RemainingV` (and `PosTyping`),
  without the refuted bundle `Bwd.BwdHyps`.
* `Round4Int.succTyped_of_hostOk`, `oneStep_of_parts`, `wholeStepValid_of_parts`: the frozen
  target from `Parts` (positive typing, typed successors, the forward conjunct, `FamBwdV`,
  `RemainingV`), every field of which is open.

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.readValid_of_configOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.readValid_of_configOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.read_doneV_of_configOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.read_doneV_of_configOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.famBwdV_of_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.famBwdV_of_hyps

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.backward_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.backward_fam

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.backward_valid4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.backward_valid4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.succTyped_of_hostOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.succTyped_of_hostOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Int.wholeStepValid_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Int.wholeStepValid_of_parts
