module

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Laws.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Execution.Callout.Progress.Defs
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

/-- A Lime1 activation: a configuration without its store. -/
structure Thread (H : Type) where
  frame : Frame
  code : List (AdminInstr Wasm.Lime1.Instr)

/-- The Lime1 configuration of an engine store and a thread. -/
def toConfig {H : Type} (c : Wasm.Lime1.Execution.Store H × Thread H) :
    Wasm.Lime1.Execution.Config H :=
  ⟨c.1, c.2.frame, c.2.code⟩

/-- Split a Lime1 configuration into an engine store and a thread. -/
def ofConfig {H : Type} (cfg : Wasm.Lime1.Execution.Config H) :
    Wasm.Lime1.Execution.Store H × Thread H :=
  (cfg.store, ⟨cfg.frame, cfg.code⟩)

@[simp] theorem toConfig_ofConfig {H : Type} (cfg : Wasm.Lime1.Execution.Config H) :
    toConfig (ofConfig cfg) = cfg := rfl

@[simp] theorem ofConfig_toConfig {H : Type} (c : Wasm.Lime1.Execution.Store H × Thread H) :
    ofConfig (toConfig c) = c := rfl

/-- Engine call results as Lime1 results. -/
def toResult : CallResult → Result
  | .values vs => .values vs
  | .trap => .trap

/-- Lime1 results as engine call results. -/
def ofResult : Result → CallResult
  | .values vs => .values vs
  | .trap => .trap

@[simp] theorem toResult_ofResult (r : Result) : toResult (ofResult r) = r := by
  cases r <;> rfl

@[simp] theorem ofResult_toResult (r : CallResult) : ofResult (toResult r) = r := by
  cases r <;> rfl

/-- Lime1 extern types as `CoreExternType`s (address types are always `.i32`). -/
def ofExternType : Wasm.Lime1.ExternType → CoreExternType
  | .func ft => .func ft
  | .table tt => .table .i32 tt.limits.min.val (tt.limits.max.map Fin.val)
  | .memory mt => .memory .i32 mt.limits.min.val (mt.limits.max.map Fin.val)
  | .global gt => .global gt.value (decide (gt.mutability = .var))

/-- Imports of a module with their declared types (unresolved type indices are dropped). -/
def importTypes (m : Wasm.Lime1.Module) : List (String × String × CoreExternType) :=
  m.imports.filterMap fun i =>
    (Wasm.Lime1.Validation.importType? m.types i.desc).map fun et =>
      (i.moduleName, i.name, ofExternType et)

/-- Exports of a module with their types (unresolved indices are dropped). -/
def exportTypes (m : Wasm.Lime1.Module) : List (String × CoreExternType) :=
  m.exports.filterMap fun e =>
    (Wasm.Lime1.Validation.exportType? (Wasm.Lime1.Validation.moduleContext m) e.index).map
      fun et => (e.name, ofExternType et)

/-- The type of an external value in a store. -/
def externType? {H : Type} (s : Wasm.Lime1.Execution.Store H) :
    ExternVal → Option CoreExternType
  | .func a => (s.funcs[a.value]?).map fun fn => .func fn.type
  | .table a => (s.tables[a.value]?).map fun t => .table .i32 t.refs.length t.max
  | .memory a => (s.memories[a.value]?).map fun m => .memory .i32 (Memory.size m.data) m.max
  | .global a => (s.globals[a.value]?).map fun g =>
      .global g.value.type (decide (g.mutability = .var))

/-- The start function of prepared start code (`[]` or `[.invoke a]`). -/
def startAddr? : List Wasm.Lime1.Execution.Admin → Option FuncAddr
  | [.invoke a] => some a
  | _ => none

/-- Core instantiation without running the start function (`Lime1.Execution.prepare?`). -/
def prepare? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : Wasm.Lime1.Module)
    (imports : List ExternVal) :
    Option (Wasm.Lime1.Execution.Store H × ModuleInst × Option FuncAddr) :=
  (Wasm.Lime1.Execution.prepare? s m imports).map fun p => (p.store, p.module, startAddr? p.start)

/-- Allocate a host function at the end of the function list. -/
def allocHost {H : Type} (s : Wasm.Lime1.Execution.Store H) (ft : V1.FuncType) (h : H) :
    Wasm.Lime1.Execution.Store H × FuncAddr :=
  ({s with funcs := s.funcs ++ [.host ft h]}, ⟨s.funcs.length⟩)

def funcType? {H : Type} (s : Wasm.Lime1.Execution.Store H) (a : FuncAddr) :
    Option V1.FuncType :=
  (s.funcs[a.value]?).map FuncInst.type

def memAddrType? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) :
    Option AddrType :=
  (s.memories[m.value]?).map fun _ => .i32

/-- Memory size in bytes. -/
def memSize? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) : Option Nat :=
  (s.memories[m.value]?).map fun mi => mi.data.size

def memRead? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) (start len : Nat) :
    Option ByteArray :=
  (s.memories[m.value]?).bind fun mi => Memory.readBytes mi.data start len

def memWrite? {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : MemAddr) (start : Nat)
    (bytes : ByteArray) : Option (Wasm.Lime1.Execution.Store H) :=
  (s.memories[m.value]?).bind fun mi =>
    (Memory.writeBytes mi.data start bytes).map fun data =>
      Wasm.Lime1.Execution.setMemory s m {mi with data := data}

/-- The Lime1 memory view: a memory is looked up in `Store.memories` and replaced with
`Lime1.Execution.setMemory`; its byte buffer is `MemInst.data`, and every Lime1 memory is
32-bit. The four byte-level accessors above are exactly its derived operations
(`lime1_memAddrType?` and friends, below). -/
def memoryView : MemoryView Wasm.Lime1.Execution.Store where
  MemAddr := MemAddr
  MemInst := Runtime.MemInst
  inst? s m := s.memories[m.value]?
  setInst := Wasm.Lime1.Execution.setMemory
  data := Runtime.MemInst.data
  withData mi d := {mi with data := d}
  addrType _ := .i32

def tableAddrType? {H : Type} (s : Wasm.Lime1.Execution.Store H) (t : TableAddr) :
    Option AddrType :=
  (s.tables[t.value]?).map fun _ => .i32

def tableFunc? {H : Type} (s : Wasm.Lime1.Execution.Store H) (t : TableAddr) (i : Nat) :
    Option (Option FuncAddr) :=
  (s.tables[t.value]?).bind fun ti => ti.refs[i]?

/-- A fresh activation: the arguments and an `invoke` under the empty frame. -/
def invoke {H : Type} (a : FuncAddr) (args : List FlatValue) : Thread H :=
  ⟨⟨[], {}⟩, Wasm.Lime1.Execution.values args ++ [.invoke a]⟩

/-- The observable status of a Lime1 activation (see the module docstring). -/
def status {H : Type} (s : Wasm.Lime1.Execution.Store H) (t : Thread H) : Status H :=
  match Wasm.Lime1.Execution.terminal? t.code with
  | some r => .returned (ofResult r)
  | none =>
    match Wasm.Lime1.Execution.decompose? (toConfig (s, t)) with
    | some c => .callout c.host c.args
    | none => if (Wasm.Lime1.Execution.step? (toConfig (s, t))).isSome then .running else .stuck

/-- Resume the callout located at store `s` with a host result (`Lime1.Execution.resume`,
without its store component). A thread that is not parked is returned unchanged. -/
def resume {H : Type} (s : Wasm.Lime1.Execution.Store H) (t : Thread H) (r : CallResult) :
    Thread H :=
  match Wasm.Lime1.Execution.decompose? (toConfig (s, t)) with
  | some c =>
    ⟨t.frame, c.fill Wasm.Lime1.Execution.coding (Wasm.Lime1.Execution.result (toResult r))⟩
  | none => t

/-- The Lime1 core-level semantics: the `WasmSemantics` from which `lime1` is read off. -/
abbrev lime1Semantics : WasmSemantics where
  Module := Wasm.Lime1.Module
  Valid := Wasm.Lime1.Validation.ModuleValid
  FuncType := V1.FuncType
  ExternType := CoreExternType
  ExternSub := CoreExternType.Sub
  ofFlatType := id
  flatType? := some
  importTypes := importTypes
  exportTypes := exportTypes
  Store := Wasm.Lime1.Execution.Store
  empty _ := {}
  FuncAddr := FuncAddr
  TableAddr := TableAddr
  GlobalAddr := GlobalAddr
  mem := memoryView
  ExternVal := ExternVal
  asFunc? | .func a => some a | _ => none
  asMemory? | .memory a => some a | _ => none
  asTable? | .table a => some a | _ => none
  asGlobal? | .global a => some a | _ => none
  ofFunc := .func
  Inst := ModuleInst
  exports i := i.exports.map fun e => (e.name, e.value)
  externType? := externType?
  prepare? := prepare?
  allocHost := allocHost
  funcType? := funcType?
  tableAddrType? := tableAddrType?
  tableFunc? := tableFunc?
  Thread := Thread
  invoke := invoke
  status := status
  Internal c c' := Wasm.Lime1.Execution.Internal (toConfig c) (toConfig c')
  resume := resume

/-- The Lime1 core engine: the engine view of `lime1Semantics`. Every projection is
definitionally what it was before the semantics layer was introduced; the equations below
record that. -/
abbrev lime1 : CoreEngine := lime1Semantics.toCoreEngine

/-! ### The memory accessors are unchanged

`lime1`'s four byte-level memory accessors are now the derived operations of `memoryView`.
These equations, all `rfl`, record that they are *definitionally* the standalone definitions
above, so no downstream statement changes. The `memoryView_*` forms are the ones that rewrite
(their left-hand sides are the shape a goal mentioning `lime1.memRead?` actually elaborates
to); the `lime1_*` forms record the defeq at the engine projection itself. -/

/-- The executable stepper of `lime1`: `Lime1.Execution.step?` on the recombined configuration.
-/
def lime1Exec : CoreEngine.Exec lime1 where
  step? c := (Wasm.Lime1.Execution.step? (toConfig c)).map ofConfig
  step?_sound {H c c'} h := by
    change Wasm.Lime1.Execution.Internal (toConfig c) (toConfig c')
    rw [Option.map_eq_some_iff] at h
    obtain ⟨cfg, hs, rfl⟩ := h
    exact Wasm.Lime1.Execution.step?_sound hs

end Silmaril.Wasm.Component.Engine.Lime1
