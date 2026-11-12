module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeLoad
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeRun

/-!
# Packed loads, and one invariant for stores and `call_indirect`: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.GoodMerge`; see `docs/projects/spectec/README.md`, "fwd20
".

* `GoodMergeLoad`: `Step_read` 24 and 25 (`load-pack-trap`, `load-pack-val`) transcribed and
  found by `rfl`, and **`fwdBase20_loadPack`**: V2's packed loads are a forward base at builtins
  answering `$ibytes_` and the float primitives (so `$extend__`), in particular at `storeB`.
* `GoodMergeCode`: `ctrlOkM`/`okA b m` (an earlier two covered codes merged, with packed loads;
  `b` admits administrative stores), `StoreOkM`, **`typedT_of_eraseM`**, the cover lemma
  **`cover20M`** into `Nest20 (BaseM P)`, and **`okA_step`** (what a step keeps).
* `GoodMergeNest`: **`fwd_nestM`**, the nested forward theorem in `simEnv20T` with subject
  reduction for the erased typing (`StoreGood.TypS`).
* `GoodMergeRun`: **`Good20M`**, **`fwd_good20M`**, **`good20M_steps`**, `runT_good20M`,
  `typed20T_of_good20M`, the inclusions **`good20M_of_good20CS`** and **`good20M_of_good20CI`**,
  `good20M_invoke`, `composite10T20_good20M`, and a packed load that traps (`sstep_packCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.GoodMerge

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.fires_loadPackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_loadPackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.fwdBase20_loadPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdBase20_loadPack

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.typedT_of_eraseM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_of_eraseM

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.cover20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.okA_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms okA_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.fwd_nestM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_nestM

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.fwd_good20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.good20M_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20M_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.runT_good20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runT_good20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.typed20T_of_good20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed20T_of_good20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.good20M_of_good20CS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20M_of_good20CS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.good20M_of_good20CI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20M_of_good20CI

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.composite10T20_good20M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composite10T20_good20M

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.GoodMerge.sstep_packCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_packCfg

end Silmaril.Wasm.SpecTec.Sim20.GoodMerge
