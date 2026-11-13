module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdValid

/-!
# The forward 1.0 half from validation: An earlier step

In `Silmaril.Wasm.SpecTec.Sim10.Valid`.

* **`GSetOk` from Core typing** (`Sim10.GSetCore`, `Sim10.GSetRun`). A V1 configuration is
  `CoreTyped10` when the copied simulation relation (`V1 → Lime1 → Core 3.0`) relates it to a Core
  configuration typed by `ConfigOk`. Then the operand of every active `global.set` has its
  global's type (`globalSet_core`, `gsetOk_of_core`). `CoreTyped10` is invariant along V1 runs from
  a store with no host function (`step_noHost`, `coreTyped10_steps`, through Core's
  `Step.preservation`), so `GSetOk` holds along the run (`gsetOk_steps`).
* **At an invocation** (`Sim10.GSetRun`, `Sim10.FwdValid`): the Core image of a V1 invocation in
  the empty frame is Core's `$invoke` (`toCore_invokeCfg10`), so it is `CoreTyped10` given a valid
  Core image of the store, typed arguments and the simulation's `StoreWF`
  (`coreTyped10_invoke`). A valid store has aligned memories (`memsAligned10_of_storeOk`).
* **The run** (`Sim10.FwdValid`): `Task.wholeRunFwd10C` and `Task.wholeRunFwd10Inv`, proved
  (`wholeRunFwd10C`, `wholeRunFwd10Inv`). an earlier `GSetOk` hypothesis along the run is gone.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.globalSet_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.globalSet_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.gsetOk_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.gsetOk_of_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.step_noHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.step_noHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.gsetOk_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.gsetOk_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.toCore_invokeCfg10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.toCore_invokeCfg10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.coreTyped10_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.memsAligned10_of_storeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.memsAligned10_of_storeOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10C

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10Inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.wholeRunFwd10Inv
