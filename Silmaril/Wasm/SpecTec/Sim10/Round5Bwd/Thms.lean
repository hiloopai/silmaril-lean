module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdRun10T

/-!
# The 1.0 route, an earlier step: the backward half with stores, and `GoodV1` from Core

See `docs/projects/spectec/README.md`, "v10".

* `FiresBack10T` (namespace `Sim10.Whole`): a `simEnv10T` firing of a rule whose quantifiers avoid
  `tbad10` and whose premises are evaluations is a `simEnv10` firing (`fires_back10T`); other
  firings invert with their evaluations and premises read in `simEnv10` (`firesPure10_invT`,
  `firesCfg10_invT`).
* `BwdLeaf10T`, `BwdSpecial10T`: the round 2–4 leaf lemmas re-run over those inversions
  (`bwd10T_*`), with `memory.size` (`lt_of_typed_constI32_10T`) and `call_indirect-trap`
  (`otherwise` in `simEnv10T`) redone.
* `BwdWhole10T`: the backward recursion in `simEnv10T` (`backward10T_of_parts`), every leaf at
  `fwdB10` under `GoodV1` (`bwdParts10T_bytesB10`), and **`wholeStepBwd10S`**.
* `BwdWitness10T`: `GoodV1` at round 4's `labelStoreCfg10` (a storing function in the store,
  untyped in `simEnv10`), the backward half there, and both halves in `simEnv10T`
  (`wholeStep10_bothT`).
* `ResCore10` (namespace `Sim10.Valid`): `ResOkL10` from Core typing (`resOkL10_of_coreTyped10`),
  so `GoodV1` from `CoreTyped10` and `StoreOk10` (`goodV1_of_coreTyped10`, `goodV1_steps'`).
* `BwdRun10T`: the backward half with stores along V1 runs from a Core-typed configuration
  (`bwd10S_steps`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fires_back10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fires_back10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.firesPure10_invT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.firesPure10_invT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.firesCfg10_invT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.firesCfg10_invT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.val10_of_varT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.val10_of_varT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_localSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_localSet

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_callAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_callAddr

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_labelVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_labelVals

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.lt_of_typed_constI32_10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.lt_of_typed_constI32_10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_memorySize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_memorySize

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_callIndirectTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10T_callIndirectTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.backward10T_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.backward10T_of_parts

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwdParts10T_bytesB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwdParts10T_bytesB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10S

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStep10_bothT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStep10_bothT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.goodV1_labelStoreCfg10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.goodV1_labelStoreCfg10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10S_labelStoreCfg_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10S_labelStoreCfg_nonvacuous

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10S_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10S_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_activeF' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_activeF

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.instrRes_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.instrRes_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_core

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_coreTyped10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.resOkL10_of_coreTyped10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_of_coreTyped10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_of_coreTyped10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_steps'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Valid.goodV1_steps'
