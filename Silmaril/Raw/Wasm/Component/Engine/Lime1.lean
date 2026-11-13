module

public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Defs

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Raw.Wasm.Component.Wasm.Semantics.Laws
public import Silmaril.Raw.Wasm.Component.Wasm.Lime1.Execution.Callout.Progress
public import Silmaril.Wasm.Lime1.Validation.Modules

/-!
# The Lime1 core engine

`lime1 : CoreEngine` instantiates the core-engine interface (`Engine/Interface.lean`) with the Lime1
machine of `Silmaril.Wasm.Lime1.Execution`, through the callout view
(`Lime1/Execution/Callout.lean`):

* modules, validity, stores, addresses, external values and module instances are the Lime1 and
  shared scalar runtime ones (`Lime1.Module`, `Lime1.Validation.ModuleValid`,
  `Lime1.Execution.Store`, `Execution.Runtime.{FuncAddr, MemAddr, TableAddr, GlobalAddr,
  ExternVal, ModuleInst}`); function types are `V1.FuncType` (`ofFlatType := id`) and extern
  types are `CoreExternType`;
* `prepare?` is `Lime1.Execution.prepare?` (allocation and segment initialization), returning the
  start function address instead of the start code `[.invoke a]`;
* `allocHost` appends `.host ft h` to the function list (the address is the old length);
* memory operations are `Execution.Memory.readBytes`/`writeBytes` and `setMemory`; every existing
  Lime1 memory has address type `.i32`; tables are funcref tables of address type `.i32`;
* a `Thread` is a configuration without its store (`frame` and administrative `code`);
  `invoke a args` is the code `values args ++ [.invoke a]` under the empty frame;
* `Internal` is `Lime1.Execution.Internal` (the machine with no host behaviour) on the recombined
  configuration; `status` reports `returned` for final code (`terminal?`), `callout` for the
  host-call redex found by `decompose?`, `running` when `Lime1.Execution.step?` finds a step and
  `stuck` otherwise; `resume s t r` plugs the host result into the context of the callout located
  at `s` (`Lime1.Execution.resume`, whose store component is supplied separately by the caller).

`lime1Exec` is the executable stepper `Lime1.Execution.step?` (sound by `step?_sound`), and
`lime1Complete` its progress (`step?_progress`, `Lime1/Execution/Callout/Progress.lean`).

Import and export types are computed from the module declarations (`Validation.importType?`,
`Validation.exportType?` over `Validation.moduleContext`). Entries whose type index does not
resolve are dropped; this never happens for valid modules. Limits are reported in their unit
(table elements, memory pages); the extern type of an existing memory reports its current size
in pages (`Memory.size`) and of a table its current length.

Not modelled or claimed here: the laws (`Engine/Lime1/Properties.lean` proves `Lawful lime1`
and the bridges to `Lime1.Execution.Steps`, `Diverges` and `Instantiation`); a resumption
progress law (`ResumeLawful`) is not claimed for Lime1 (an ill-typed host result can leave the
resumed thread stuck). No REF function of the canonical ABI is transcribed in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Lime1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Semantics (MemoryView WasmSemantics)

/-! ### The memory accessors are unchanged

`lime1`'s four byte-level memory accessors are now the derived operations of `memoryView`.
These equations, all `rfl`, record that they are *definitionally* the standalone definitions
above, so no downstream statement changes. The `memoryView_*` forms are the ones that rewrite
(their left-hand sides are the shape a goal mentioning `lime1.memRead?` actually elaborates
to); the `lime1_*` forms record the defeq at the engine projection itself. -/

theorem lime1_memAddrType? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) :
    lime1.memAddrType? s m = memAddrType? s m := rfl

theorem lime1_memSize? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) :
    lime1.memSize? s m = memSize? s m := rfl

theorem lime1_memRead? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr)
    (start len : Nat) : lime1.memRead? s m start len = memRead? s m start len := rfl

theorem lime1_memWrite? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr)
    (start : Nat) (bytes : ByteArray) :
    lime1.memWrite? s m start bytes = memWrite? s m start bytes := rfl

theorem memoryView_addrType? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) :
    memoryView.addrType? s m = memAddrType? s m := rfl

theorem memoryView_size? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) :
    memoryView.size? s m = memSize? s m := rfl

theorem memoryView_read? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr)
    (start len : Nat) : memoryView.read? s m start len = memRead? s m start len := rfl

theorem memoryView_write? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr)
    (start : Nat) (bytes : ByteArray) :
    memoryView.write? s m start bytes = memWrite? s m start bytes := rfl

/-- `lime1Exec` finds a step whenever an internal step exists (`step?_progress`). -/
theorem lime1Complete : CoreEngine.ExecComplete lime1Exec where
  progress {H c c'} h := by
    change ((Wasm.Lime1.Execution.step? (toConfig c)).map ofConfig).isSome
    rw [Option.isSome_map]
    exact Wasm.Lime1.Execution.step?_progress h

end Silmaril.Wasm.Component.Engine.Lime1
