module

public import Silmaril.Wasm.SpecTec.Sim.Round3.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round3.Assembly
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round3.Refute

/-!
# SpecTec ↔ Core 3.0, round 3 integration: what is proved

* `Round3.wholeStepBounded_of_open`: `Integrate.Task.wholeStepBounded` from `Round3.Open`;
* `Round3.not_open`, `Round3.not_open_hyp`: `Open` is uninhabited, so that reduction is vacuous
  (the typing bundles `TypeTyping` and `AggTypes` are refuted as stated, track configok).

* `Round3.not_wholeStepBounded`: **the target `Integrate.Task.wholeStepBounded` is false**: its
  backward conjunct fails for every `B` at `i32.const 0; memory.grow 0` with no memory
  (`Step/memory.grow-fail` has no premise; Core's `growFail` needs the memory). So are
  `Bwd.Task.wholeStepUpTo` and `Task.wholeStep` (`not_wholeStepUpTo`, `not_wholeStep`).

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.wholeStepBounded_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.wholeStepBounded_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.not_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.not_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.not_open_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.not_open_hyp

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.sliceTotal' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms FwdMem.sliceTotal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.not_wholeStepBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.not_wholeStepBounded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.not_wholeStepUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.not_wholeStepUpTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.not_wholeStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.not_wholeStep

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round3.step_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round3.step_stuck
