module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreBwd10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.TypOff10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SelCore
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreValid10

/-!
# The 1.0 route, round 5 (track v10): what is proved

See `docs/projects/spectec/README.md`, "v10".

* `StoreBwd10T` (namespace `Sim10.StoreAgree`): a firing `$with_mem` is in bounds
  (`withMem_bound10`), so the two store write rules hold backward in `simEnv10T (bytesB10 P)` at
  `GoodV1` (`bwd10T_storeNumVal`, `bwd10T_storePackVal`); with round 4's trap rules, all four
  store rules hold backward (`bwd10T_store`).
* `TypOff10` (namespace `Sim10.StoreAgree`): `simEnv10` and `simEnv10T` type alike, in both
  directions, at every type off `tbad10`, the thirteen types that reach `instr` or `admininstr`
  (`typsOffB_fixed10`, kernel; `hasTyp_off10T`).
* `SelCore` (namespace `Sim10.Valid`): `SelOk` from Core typing (`selOk_of_coreTyped10`) and
  along V1 runs (`selOk_steps`).
* `StoreValid10` (namespace `Sim10.Valid`): `StoreOk10` from V1 module validation, through V1's
  allocation and segment initialisation (`storeOk10_prepare`), instantiation including the start
  function (`storeOk10_instantiation`) and runs (`storeOk10_steps`); `GoodV1` from validation
  given `ResOkL10` (`goodV1_of_valid`, `goodV1_steps`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.withMem_bound10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.withMem_bound10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.withMem_write10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.withMem_write10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storeNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storeNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storePackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storePackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_store

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typsOffB_fixed10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typsOffB_fixed10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typOff10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typOff10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.hasTyp_off10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.hasTyp_off10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.hasTyp_val10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.hasTyp_val10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.select_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.select_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_of_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_of_coreTyped10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_of_coreTyped10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.selOk_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_prepare

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_empty' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_empty

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_instantiation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.storeOk10_instantiation

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_of_valid

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_steps
