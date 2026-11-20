module

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Engine.Sim.Defs

/-!
# The Core 3.0 engine over a memory representation

`core3 o` (`Engine.Core3`) stores linear memories as `ByteArray`s, the specification's
representation. Every store operation of the engine is generic in a memory representation `R`
(`Execution.MemRep`): instantiation (`Core3.prepareE?`), host allocation, the type and memory
accessors, the status, the internal step (`internalC (stepI o)`) and resumption.

* `core3Impl o R`: those operations over `Store H R`, as the store-dependent part of `core3 o`
  (`CoreEngine.StoreImpl`).
* `core3On o R := (core3 o).withStore (core3Impl o R)`: the engine with `core3 o`'s modules, types,
  addresses and threads and stores `Store H R`. At `ByteArray` it is `core3 o`
  (`core3On_byteArray`, by `rfl`).
* `core3K o := core3On o KMem`: memories are `KBytes` trees, which the kernel evaluates without
  materialising the bytes (`docs/projects/wasm-memrep.md`).
* `core3ExecOn o R`, `core3ExecK o`: the executable stepper, the interpreter step itself.

`Engine.Core3K.Thms` proves that `core3On o R` simulates `core3 o` through `Store.toBytes` at a
lawful `R` (`core3Sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Core3
open Silmaril.Wasm.Execution (MemRep KMem)

/-- The store-dependent part of `core3 o` over memories in `R`. -/
def core3Impl (o : SingleThreaded.GrowOracle) (R : Type) [MemRep R] : (core3 o).StoreImpl where
  Store H := Execution.Core.Store H R
  empty _ := {}
  externType? := externTypeE?
  prepare? := prepareE?
  allocHost := SingleThreaded.allocHost
  funcType? := funcTypeE?
  memAddrType? := SingleThreaded.memAddrType?
  memSize? := SingleThreaded.memSize?
  memRead? := SingleThreaded.memRead?
  memWrite? := SingleThreaded.memWrite?
  tableAddrType? := SingleThreaded.tableAddrType?
  tableFunc? := SingleThreaded.tableFunc?
  status := statusE o
  Internal c c' := SingleThreaded.internalC (SingleThreaded.Exec.stepI o) c = some c'
  resume s t r := SingleThreaded.resume s t (toCR r)

/-- **The Core 3.0 engine over memories in `R`.** -/
def core3On (o : SingleThreaded.GrowOracle) (R : Type) [MemRep R] : CoreEngine :=
  (core3 o).withStore (core3Impl o R)

/-- **The Core 3.0 engine over `KMem` memories.** -/
abbrev core3K (o : SingleThreaded.GrowOracle) : CoreEngine := core3On o KMem

/-- At `ByteArray` the engine is `core3 o`. -/
theorem core3On_byteArray (o : SingleThreaded.GrowOracle) : core3On o ByteArray = core3 o := rfl

/-- Import matching is that of `core3 o`, hence decidable. -/
instance core3On_decExternSub (o : SingleThreaded.GrowOracle) (R : Type) [MemRep R]
    (a b : (core3On o R).ExternType) : Decidable ((core3On o R).ExternSub a b) :=
  core3_decExternSub o a b

/-- The executable stepper: the interpreter step on `Store H R`. -/
def core3ExecOn (o : SingleThreaded.GrowOracle) (R : Type) [MemRep R] : (core3On o R).Exec where
  step? := SingleThreaded.internalC (SingleThreaded.Exec.stepI o)
  step?_sound h := h

/-- The executable stepper of `core3K o`. -/
abbrev core3ExecK (o : SingleThreaded.GrowOracle) : (core3K o).Exec := core3ExecOn o KMem

end Silmaril.Wasm.Component.Engine
