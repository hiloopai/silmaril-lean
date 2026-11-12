module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Env
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Derive
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreTop10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreVal10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreCtx10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreNest10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreNest10TEx

/-!
# `simEnv10` against `simEnv10T`, and the 1.0 stores: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim10.StoreAgree`; see `docs/projects/spectec/README.md`, "fwd10
".

* `StoreAgree10Env`: the two environments evaluate alike (`envSame10T`) and typing grows from
  `simEnv10` to `simEnv10T` (`typRepair10T`), through 2.0's generic `EnvSame`/`TypRepair`.
* `StoreAgree10Derive`: the only `otherwise` rule of the whole 1.0 script is `Step_read`'s
  `call_indirect-trap` (`else10_only`, kernel), and its premise moves (`elseAgree10T`), so every
  step of `simEnv10` is one of `simEnv10T` with no hypothesis (`sstepB10T_of_sstepB10`).
* `StoreAgree10Fwd`: the forward theorems of the 1.0 route, concluding in `simEnv10T`.
* `StoreTop10T`, `StoreVal10T`: the four store rules forward in `simEnv10T` from a state typed
  there (the writes at `bytesB10`); the two trap rules backward.
* `StoreCtx10T`, `StoreNest10T`: the structural rules in `simEnv10T`, and stores nested anywhere
  forward (`fwd10T_storeNest`, `wholeStepFwd10T_stores`).
* `StoreNest10TEx`: a store under a label, over a store holding a storing function, untyped in
  `simEnv10` and stepped in `simEnv10T` by the general theorem.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.envSame10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.envSame10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typRepair10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typRepair10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.else10_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.else10_only

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.elseAgree10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.elseAgree10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstepB10T_of_sstepB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstepB10T_of_sstepB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.rtc_sstepB10T_of_sstepB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.rtc_sstepB10T_of_sstepB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typed10T_of_typed10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.typed10T_of_typed10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStepFwd10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStepFwd10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeRunFwd10CT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeRunFwd10CT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeRunFwd10InvT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeRunFwd10InvT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStep10_fwdT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStep10_fwdT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storeNumTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storeNumTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storePackTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storePackTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storeNumTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storeNumTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storePackTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.bwd10T_storePackTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.evalExp_withMem10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.evalExp_withMem10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storeNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storeNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storePackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fires10T_storePackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fwdAt10T_storeLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fwdAt10T_storeLeaf

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fwd10T_storeNest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.fwd10T_storeNest

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStepFwd10T_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.wholeStepFwd10T_stores

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstep10T_memStoreNest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstep10T_memStoreNest

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.not_typed10_labelStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.not_typed10_labelStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstep10T_labelStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreAgree.sstep10T_labelStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_nestT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwd10_nestT
