module

public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Concrete

/-!
# SpecTec ↔ Core 3.0, round 3, track fwd-mem: what is proved

Core → SpecTec (`docs/projects/spectec/README.md`):

* every scalar load and store, `MemoryStep.loadIntVal`, `loadPackVal`, `loadFloatVal`,
  `storeIntVal`, `storePackVal`, `storeFloatOob`, `storeFloatVal` (all widths, packed, `i32` and
  `i64` memories): `fwd_loadIntVal`, `fwd_loadPackVal`, `fwd_loadFloatVal`, `fwd_storeIntVal`,
  `fwd_storePackVal`, `fwd_storeFloatOob`, `fwd_storeFloatVal`, under `BytesFuns` (proved for
  `Prims.builtins`, `bytesFuns_builtins`) and, for the `-val` cases, `SliceTotal` or the
  evaluator's strict slice bound;
* `return_call_ref-frame-addr` in the recursion, up to `Bwd.ConfigEq`, with
  `Bwd.CallRefTyping` proved (`callRefTyping_simEnv`);
* `forward_upTo`, `forward3_concrete` on the wider fragment `Covered3 mem`
  (`covered3_of_covered`), and `wholeStepBounded_of_concrete3`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.forward_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdMem.forward_upTo

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.forward3_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdMem.forward3_concrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.wholeStepBounded_of_concrete3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdMem.wholeStepBounded_of_concrete3

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.bytesFuns_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdMem.bytesFuns_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdMem.callRefTyping_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdMem.callRefTyping_simEnv
