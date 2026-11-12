module

public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.CallEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Respect
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Invert
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Generic
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Control
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Decode
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.ReturnCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Block
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Otherwise
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.CallFunc
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Host
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Dispatch

/-!
# SpecTec ↔ Core 3.0, track "backward": what is proved

* `Bwd.backward_upTo`: the **generic SpecTec → Core direction**. From the per-rule obligations
  `BackwardUpTo` (implied by `Backward`, `Backward.upTo`), the decoders `StructDecode` and the
  encoding's `TypingFacts`, every SpecTec step from the image of a typed configuration lands on
  the image of a configuration equivalent to a Core successor. `Step` rules 0–5 are done here
  (`inv_*` read them back; `ctxt-instrs` for every split), by recursion on the size of the active
  code.
* `Bwd.simEnv_backward_upTo`: the dispatch (`backwardUpTo_of`) of every proved per-rule lemma
  (`Step` 0–10, `Step_pure` 0–30 and 50, `Step_read` 0–22) composed with the generic part, for one
  `B`, conditional on `BwdHyps`, `TypingFacts` and the open rules `Remaining`;
  `Bwd.wholeStepUpTo_of` reduces `Bwd.Task.wholeStepUpTo` to these and the forward direction.
* Obstruction 1: `Bwd.step_respects` (Core respects `ConfigEq`), `Bwd.wholeStep_upTo`
  (`Task.wholeStep` implies the restatement), `bwdUpTo_returnCallRefFrameAddr` and
  `fwdUpTo_returnCallRefFrameAddr` (the rule, both directions, up to `ConfigEq`).
* New per-rule lemmas: `Step_pure` 8, 16, 18, 21, 22; `Step_read` 0, 1, 8–11; `Step` 7–9.
* Decoders proved: `retDecode`, `decode_refFuncAddr`, `decode_block`, `decode_loop`,
  `structDecode_of_vals`.

None of `BwdHyps`, `TypingFacts`, `Remaining` is discharged: `Task.wholeStepUpTo` is not proved.
See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim.Bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.backward_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms backward_upTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.simEnv_backward_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms simEnv_backward_upTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.step_respects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_respects

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.wholeStep_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wholeStep_upTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.retDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retDecode

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.bwdUpTo_returnCallRefFrameAddr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms bwdUpTo_returnCallRefFrameAddr

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.fwdUpTo_returnCallRefFrameAddr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms fwdUpTo_returnCallRefFrameAddr

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.bwd_callRefFunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bwd_callRefFunc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Bwd.wholeStepUpTo_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wholeStepUpTo_of
