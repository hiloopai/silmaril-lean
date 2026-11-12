module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdWhole

/-!
# The forward 1.0 half: round 4

In `Silmaril.Wasm.SpecTec.Sim10.Whole`.

* **The successful loads** (`Sim10.FwdLoadVal`): `load-num-val` and `load-pack-val` fire forward
  at `bytesB10` (`fires10_loadNumVal`, `fires10_loadPackVal`), so `FwdLoads10 (bytesB10 P) hn`
  holds (`fwdLoads10_bytesB10`) and the forward half at `bytesB10` has no open obligation
  (`wholeStepFwd10_bytesB10''`).
* **The unrestricted `memory.size` field is false** (`Sim10.MemSizeRefute`): the rule tables of
  1.0 (`pureTags10`, `readTags10`, `stepTags10`, kernel `rfl`); `z; ε` is stuck
  (`not_sstep10_nil`); `z; MEMORY.SIZE` is stuck at a memory that is not page-aligned
  (`not_sstep10_memorySize`, `stuck10_memorySize`); a typed one-byte-memory witness
  (`typed10_memSize`, `typed10_memSize'`). So `MemorySizeField10` and pass 2's `FwdRestQ10` fail at
  every builtins (`not_memorySizeField10`, `not_fwdRestQ10`).
* **The whole step and the run** (`Sim10.FwdWhole`): `Task.wholeStepFwd10` and
  `Task.wholeRunFwd10`, proved (`wholeStepFwd10`, `wholeRunFwd10`); the alignment hypothesis is
  needed (`not_wholeStepFwd10_unaligned`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdLoads10_bytesB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdLoads10_bytesB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10''

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fires10_loadNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fires10_loadNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fires10_loadPackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fires10_loadPackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_nil

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_memorySize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_sstep10_memorySize

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.stuck10_memorySize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.stuck10_memorySize

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_memSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_memSize

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_memSize'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_memSize'

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_memorySizeField10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_memorySizeField10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_fwdRestQ10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_fwdRestQ10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeRunFwd10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeRunFwd10

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.not_wholeStepFwd10_unaligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.not_wholeStepFwd10_unaligned
