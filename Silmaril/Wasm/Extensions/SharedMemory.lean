module

public import Silmaril.Wasm.Modules

/-! # Syntax for modules with shared linear memories

This is an additive representation of the shared-memory type flag used by the
WebAssembly threads proposal. It deliberately reuses Core instructions: atomic
instructions and a concurrent operational semantics are outside this slice.

`coreShape` erases syntax metadata. It is not a semantics-preserving translation.
`toCore?` is the checked boundary: it succeeds only when no memory is shared.
Existing Core types and APIs are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.Extensions.SharedMemory

structure MemoryType where
  core : Wasm.MemoryType
  shared : Bool := false
  deriving DecidableEq, Repr

def MemoryType.toCore? (m : MemoryType) : Option Wasm.MemoryType :=
  if m.shared then none else some m.core

inductive ExternType where
  | func (type : TypeIdx)
  | table (type : TableType)
  | memory (type : MemoryType)
  | global (type : GlobalType)
  | tag (type : TagType)
  deriving DecidableEq, Repr

def ExternType.coreShape : ExternType → Wasm.ExternType
  | .func t => .func t
  | .table t => .table t
  | .memory t => .memory t.core
  | .global t => .global t
  | .tag t => .tag t

def ExternType.ofCore : Wasm.ExternType → ExternType
  | .func t => .func t
  | .table t => .table t
  | .memory t => .memory ⟨t, false⟩
  | .global t => .global t
  | .tag t => .tag t

def ExternType.isShared : ExternType → Bool
  | .memory t => t.shared
  | _ => false

structure Import where
  moduleName : String
  name : String
  type : ExternType
  deriving DecidableEq, Repr

def Import.coreShape (i : Import) : Wasm.Import :=
  ⟨i.moduleName, i.name, i.type.coreShape⟩

def Import.ofCore (i : Wasm.Import) : Import :=
  ⟨i.moduleName, i.name, .ofCore i.type⟩

/-- Core declaration shapes, with explicit shared-memory import/definition types.
No duplicate Core module is stored, so annotations cannot disagree with it. -/
structure Module where
  types : List RecType := []
  imports : List Import := []
  funcs : List Func := []
  tables : List Table := []
  memories : List MemoryType := []
  globals : List Global := []
  tags : List TagType := []
  elems : List Elem := []
  data : List Data := []
  start : Option FuncIdx := none
  exports : List Export := []
  deriving Repr

/-- Erase only the shared flag, for reusing syntax utilities. This function
does not assert that the resulting Core module has the same behavior. -/
def Module.coreShape (m : Module) : Wasm.Module :=
  { types := m.types, imports := m.imports.map Import.coreShape,
    funcs := m.funcs, tables := m.tables, memories := m.memories.map MemoryType.core,
    globals := m.globals, tags := m.tags, elems := m.elems, data := m.data,
    start := m.start, exports := m.exports }

def Module.ofCore (m : Wasm.Module) : Module :=
  { types := m.types, imports := m.imports.map Import.ofCore,
    funcs := m.funcs, tables := m.tables, memories := m.memories.map (⟨·, false⟩),
    globals := m.globals, tags := m.tags, elems := m.elems, data := m.data,
    start := m.start, exports := m.exports }

/-- A projection to the existing Core representation only for non-shared modules. -/
def Module.toCore? (m : Module) : Option Wasm.Module :=
  if m.imports.any (fun i => i.type.isShared) || m.memories.any MemoryType.shared then none
  else some m.coreShape

theorem Module.toCore?_ofCore (m : Wasm.Module) : (ofCore m).toCore? = some m := by
  have hi : ∀ i : Wasm.Import, (Import.ofCore i).type.isShared = false := by
    intro i; cases i with | mk mn n t => cases t <;> rfl
  have he : ∀ i : Wasm.Import, Import.coreShape (Import.ofCore i) = i := by
    intro i; cases i with | mk mn n t => cases t <;> rfl
  simp [toCore?, ofCore, coreShape, List.map_map, Function.comp_def, hi, he]


end Silmaril.Wasm.Extensions.SharedMemory
