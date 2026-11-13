module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodSize
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodTable
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodRun

/-!
# `call_indirect`, `table.size`, `memory.size` and `table.get` inside a covered run: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.CallIndGood`; see `docs/projects/spectec/README.md`, "fwd20".

* `CallIndGoodSize`: `Step_read` 11 and 36 (`table.size`, `memory.size`) forward
  (**`fires_tableSize20`**, **`fires_memorySize20`**) and as a base fragment (`fwdBase20_size`).
* `CallIndGoodTable`: `Step_read` 9 and 10 (`table.get-trap`, `table.get-val`) forward
  (**`fires_tableGetTrap20`**, **`fires_tableGetVal20`**; rule 9 transcribed and checked by
  `rfl`) and as a base fragment (`fwdBase20_tableGet`).
* `CallIndGoodCode`: covered code read in a module (`ctrlOkI`, `adminOkI`: round 3's `ctrlOk`
  plus `call_indirect x y` where the module defines type `y`, plus `table.size`, `memory.size`
  and `table.get`; a frame body in its own frame's module), `StoreOkI` (function bodies covered
  in their own modules), **`cover20CI`** (every V2 step is in `Nest20 (FwdStep20G P)`: both
  `call_indirect` rules, the two size rules and both `table.get` rules) and **`adminOkI_step`**.
* `CallIndGoodRun`: **`Good20CI`**, **`fwd_good20CI`** and **`good20CI_steps`** (preserved by
  every step and run, each step matched in the corrected script), `good20CI_of_good20C`,
  `good20CI_invoke`, a `memory.size` run (`sstep_memSizeCfg`) and a trapping `call_indirect` run
  (`sstep_callIndCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.CallIndGood

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.fires_tableSize20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_tableSize20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.fires_memorySize20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_memorySize20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.sstep_memSizeCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_memSizeCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.fires_tableGetTrap20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_tableGetTrap20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.fires_tableGetVal20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_tableGetVal20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.cover20CI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20CI

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.adminOkI_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adminOkI_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.fwd_good20CI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20CI

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.good20CI_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20CI_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.good20CI_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20CI_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.CallIndGood.sstep_callIndCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_callIndCfg

end Silmaril.Wasm.SpecTec.Sim20.CallIndGood
