module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepCover
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepRun

/-!
# Stores inside instruction trees: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreDeep`; see `docs/projects/spectec/README.md`, "fwd20
".

* `StoreDeepTyp`: `ctrlOkD`/`okD` (covered code with scalar stores at every depth of block
  bodies, branches and label continuations), the deep erasure `eD`/`eDA`, and
  **`typedT_of_eDL`**: covered code whose deep erasure is typed in `simEnv20` is typed in
  `simEnv20T` (blocks, loops and `if`s rebuilt there, `typedT_block`, `typedT_loop`, `typedT_if`).
* `StoreDeepRules`: the rules that copy an `instr*`, fired in `simEnv20T` with every quantifier
  typed there: `if-true`/`if-false` (`spureT_ifTrue`, `spureT_ifFalse`), `label-vals`,
  `trap-label`, and `Step_read` `block`/`loop` (`firesT_block`, `firesT_loop`; the premise
  `$blocktype(z, bt)` evaluated in `simEnv20` and moved, `evalT_of_20`).
* `StoreDeepCover`: **`cover20D`** into `Nest20 (BaseD P)` (`Good20M`'s base, round 3's first
  pure fragment and `block`/`loop`), and **`okD_step`**.
* `StoreDeepNest`: **`fwd_nestD`**, the nested forward theorem in `simEnv20T` with subject
  reduction for the deeply erased typing (`TypD`); erasure keeps each base step
  (`erase_pureFrag20D`, `erase_pureFrag20BD`, `erase_block`).
* `StoreDeepRun`: **`Good20D`**, **`fwd_good20D`**, **`good20D_steps`**, `runT_good20D`,
  `typed20T_of_good20D`, **`good20D_of_good20M`**, `good20D_invoke`, `composite10T20_good20D`, and
  a block whose body holds a store, entered by a step of `simEnv20T` (`sstep_blockStoreCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.typedT_of_eDI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_of_eDI

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.typedT_of_eDL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_of_eDL

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.spureT_ifTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spureT_ifTrue

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.spureT_labelVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spureT_labelVals

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.firesT_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_block

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.firesT_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_loop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.cover20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.okD_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms okD_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.fwd_nestD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_nestD

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.fwd_good20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.good20D_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20D_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.runT_good20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runT_good20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.typed20T_of_good20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed20T_of_good20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.good20D_of_good20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20D_of_good20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.composite10T20_good20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composite10T20_good20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreDeep.sstep_blockStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_blockStoreCfg

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
