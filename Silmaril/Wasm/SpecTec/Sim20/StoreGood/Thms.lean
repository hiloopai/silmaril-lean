module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodConcat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodCover
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodRun

/-!
# A storing `Good20C` preserved by steps: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreGood`; see `docs/projects/spectec/README.md`, "fwd20".

* `StoreGoodTyp`: `adminOkS` (round 3's covered code with scalar stores admitted as
  administrative instructions, at any depth of labels and frames), the erasure `eraseA` of those
  stores, and **`typedT_of_erase`**: erased code typed in `simEnv20` is typed in `simEnv20T`
  before erasure (label and frame inversions in `simEnv20`, constructions in `simEnv20T`).
  `typedV_instr_of_admin20T`: `admininstr` and `instr` agree on instructions in `simEnv20T`.
* `StoreGoodConcat`: `br-zero`, `br-succ`, `return-frame`, `return-label` and `trap-vals`
  restated in `simEnv20T`, with every quantifier typed there, so a tail may hold a store.
* `StoreGoodCover`: **`cover20CS`**, the cover lemma that admits stores (into `BaseS`), and
  `adminOkS_step` (covered code with stores, the store's functions and whole pages are kept).
* `StoreGoodNest`: **`fwd_nestS`**, the nested forward theorem in `simEnv20T` with subject
  reduction for the erased typing (`TypS`).
* `StoreGoodRun`: **`Good20CS`**, **`fwd_good20CS`** and **`good20CS_steps`** (preserved by every
  step and run, each step matched in `simEnv20T`), `typed20T_of_good20CS`,
  `good20CS_of_good20C`, `fwd20T_good20CS`, `composite10T20_good20CS`, and round 4's storing
  example by preservation (`good20CS_memStore`, `composite10T20_memStoreCS`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.typedT_of_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_of_erase

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.typedV_instr_of_admin20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_instr_of_admin20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.spureT_brZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spureT_brZero

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.spureT_trapVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spureT_trapVals

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.cover20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.adminOkS_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adminOkS_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.fwd_nestS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_nestS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.fwd_good20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.good20CS_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20CS_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.runT_good20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runT_good20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.typed20T_of_good20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed20T_of_good20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.composite10T20_good20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composite10T20_good20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreGood.composite10T20_memStoreCS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composite10T20_memStoreCS

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
