module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdBoth

/-!
# Both 1.0 halves at one set of builtins: round 4, pass 2

In `Silmaril.Wasm.SpecTec.Sim10.Whole`.

* **The rules inert at `floatIntB`, backwards at `bytesB10`** (`Sim10.BwdBytes`):
  `load-num-val`, `load-pack-val` and `memory.grow-succeed` are V1 steps
  (`bwd10_loadNumVal`, `bwd10_loadPackVal`, `bwd10_memGrowSucceed`).
* **The backward half at the forward half's builtins** (`Sim10.BwdBoth`): under `GoodT10`
  (`GoodV1` and typed code, an invariant of the recursion, `cfgInv_goodT10`) the two store rules do
  not fire (`not_fires_storeTyped10`), and every other rule is discharged
  (`bwdParts10_bytesB10`). So `Task.wholeStepBwd10B` holds (`wholeStepBwd10B`), and with pass 1's
  forward half both directions hold at `fwdB10 nd r` (`wholeStep10_both`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_loadNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_loadNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_loadPackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_loadPackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_memGrowSucceed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_memGrowSucceed

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.cfgInv_goodT10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.cfgInv_goodT10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_fires_storeTyped10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_fires_storeTyped10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwdParts10_bytesB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwdParts10_bytesB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10B

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStep10_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStep10_both
