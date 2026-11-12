module

public import Silmaril.Wasm.SpecTec.Sim10.FwdInv.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdAlign

/-!
# The forward 1.0 half: pass 3 (round 3)

In `Silmaril.Wasm.SpecTec.Sim10.Whole`.

* **New forward leaves**, at every builtins:
  - `fwdAt10_brTable` (`Sim10.FwdTable`): `br_table-lt` and `br_table-ge`;
  - `fwdAt10_callIndirect`, `fwdAt10_callIndirectBounds`, `fwdAt10_callIndirectNull`,
    `fwdAt10_callIndirectType`: `call_indirect-call`, and `call_indirect-trap` through its
    `otherwise` premise (`otherwise_callIndirectTrap10`);
  - `fwdAt10_invokeWasm` (`Sim10.FwdCallAddr`): `call_addr` of a Wasm function;
  - `fwdAt10_intLoadTrap`, `fwdAt10_floatLoadTrap`, `fwdAt10_memGrowFail` (`Sim10.FwdMem`);
  - `fwdAt10_memorySize`, restated at a page-aligned memory of fewer than `2^32` pages
    (`MemAligned10`).
* **What is left** (`Sim10.FwdRestR`): `FwdRestR10`, three obligations (successful integer and
  float loads, successful `memory.grow`). `wholeStepFwd10_of_restR`: the forward half under
  `Plain10`, `GSetOk` and `MemsAligned10`, at builtins with `NumAgree10`.
* **Builtins that answer bytes and growth** (`Sim10.FwdBytes`): `bytesB10 P`, which is
  `floatIntB P` with `$bytes_`, `$ibytes_` and `$growmemory` answered as V1 does;
  `numAgree10_bytesB10`; `wholeStepFwd10_bytesB10`.
* **Subject reduction for every V1 step** (`Sim10.SubjRedPure`, `Sim10.SubjRedStep`,
  `Sim10.ValTyping`): `valTyped10` (every V1 value is a typed 1.0 `val`, floats included),
  `typed10_step'`; so `wholeStepFwd10_of_restR''` and `wholeStepFwd10_of_restQ'` have no
  successor-typing hypothesis.
* **`memory.grow` that succeeds, at `bytesB10`** (`Sim10.FwdGrow`):
  `fwdAt10_memGrowSucceed_bytesB10`, so at `bytesB10` only the two successful loads remain
  (`FwdLoads10`, `fwdRestR10_bytesB10`, `wholeStepFwd10_bytesB10'`).
* **The alignment invariant** (`Sim10.FwdAlign`): `memsAligned10_steps`, `MemsAligned10` (with
  `NoHost10`) holds along every V1 run from an aligned store with no host function.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_brTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_brTable

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_callIndirectTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_callIndirectTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_invokeWasm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_invokeWasm

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_memorySize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_memorySize

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restR

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.valTyped10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.valTyped10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_step'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.typed10_step'

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restR''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restR''

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restQ'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_of_restQ'

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_memGrowSucceed_bytesB10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.fwdAt10_memGrowSucceed_bytesB10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepFwd10_bytesB10'

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.memsAligned10_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.memsAligned10_steps
