module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlTrapVals
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessG10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstErase10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessIter10

/-!
# The 1.0 route, an earlier step (track v10-inst)

See `docs/projects/spectec/README.md`, "v10-inst".

* `CtrlTrapVals` (namespace `Sim10.Whole`): `z; CONST TRAP TRAP` does not step to `z'; TRAP`
  in any environment like `simEnv10` (`not_sstepG_constTrapTrap_trap`), so the unrestricted
  `trap-vals` obligation in V1's `trapValues` form is false in `simEnv10` and `simEnv10T`
  (`not_trapValuesField10`, `not_trapValuesField10T`).
* `InstGlobInit` (namespace `Sim10.InstG`): Lime1 initializer typing with imported globals
  (`constExpr?_typeG`, `globalsTyped_of_importsMatch`).
* `InstGlobRes`: the component work's global-free residue at every store and import list
  (`prepare?_residueG`, `importsMatch_residueG`) and Core `StoreOk` with appended globals
  (`storeOk_appendGlobals`, `storeOk_gstore`).
* `InstGlob10`: **`instantiation_core10G`**, **`wholeRunFwd10InvG`**, `wholeRunFwd10InvGT`,
  `wholeRunFwd10InvG_empty`: an earlier instantiation form of `Task.wholeRunFwd10Inv` with
  `noGlobals` dropped (`InstBoundsG`).
* `InstWitnessG10`: a module with a global instantiated into the empty store, to which it
  applies (`wholeRunFwd10InvG_glob`).
* `InstIter10`: `Task.storeOkErase10` (a valid Core store erasing to the image of a V1 store
  makes the image valid); under it, every store reached by iterated instantiation (`Reach10`) is
  fine (`reach10_ok`) and the forward run holds there (`wholeRunFwd10InvR`, `…RT`).
* `SegFree`: Core 3.0 typing of segment-free code does not read the context's segments
  (`segs_InstrsOk`, `segs_FuncOk`); the image of Lime1 code is segment-free.
* `InstErase10`: **`storeOkErase10`**, so `Task.storeOkErase10` holds, and iterated
  instantiation is covered unconditionally (`reach10_okU`, **`wholeRunFwd10InvRU`**,
  `wholeRunFwd10InvRTU`).
* `InstWitnessIter10`: `addModule0`, then `globModule` into the result; the second store is
  reached and the iterated form applies to its new function (`wholeRunFwd10InvRU_iter`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_constTrapTrap_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstepG_constTrapTrap_trap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapValuesField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapValuesField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapValuesField10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_trapValuesField10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.instantiation_core10G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.instantiation_core10G

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvG

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvGT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvGT

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitnessG10.wholeRunFwd10InvG_glob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitnessG10.wholeRunFwd10InvG_glob

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.storeOk_appendGlobals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.storeOk_appendGlobals

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.reach10_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.reach10_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvR

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.erase_coreStore10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.erase_coreStore10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.storeOkErase10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.storeOkErase10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvRU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvRU

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvRTU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstG.wholeRunFwd10InvRTU

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.SegFree.segs_InstrsOk' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.SegFree.segs_InstrsOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.InstWitnessIter10.wholeRunFwd10InvRU_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.InstWitnessIter10.wholeRunFwd10InvRU_iter
