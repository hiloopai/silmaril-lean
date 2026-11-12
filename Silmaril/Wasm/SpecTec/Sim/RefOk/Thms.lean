module

public import Silmaril.Wasm.SpecTec.Sim.RefOk.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.Combine

/-!
# SpecTec ↔ Core 3.0, round 3, track refok: what is proved

For the concrete `B := Prims.builtins prof hn host`, at every profile and host:

* `RefOk.instReftype_simEnv` (for every `B`): `$inst_reftype(m, rt)` evaluates to
  `CT.elemType (m.instRef rt)`, so `Integrate.Residue.instReftype` is discharged;
* `RefOk.growFuns_builtins`: `Memory.GrowFuns`, so `Integrate.Extra.grow` is discharged;
* `RefOk.residue_builtins`, `RefOk.extra_builtins`, `RefOk.wholeStepBounded_of_refok`: the
  round-2 reduction of `Integrate.Task.wholeStepBounded` with what is left of the two bundles
  (`ResidueRest`, `ExtraRest`).

`RefsGC.RefOkBridge` (in `ResidueRest`) is not discharged; see `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.RefOk.instReftype_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefOk.instReftype_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.RefOk.growFuns_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefOk.growFuns_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.RefOk.wholeStepBounded_of_refok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefOk.wholeStepBounded_of_refok

/-- info: 'Silmaril.Wasm.SpecTec.Sim.RefOk.wholeStepBounded_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefOk.wholeStepBounded_of_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim.RefOk.not_residueCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefOk.not_residueCore
