module

public import Silmaril.Wasm.V1.ToCore.Instructions

/-!
# Module injection from WebAssembly 1.0 into Core 3

Function types become singleton final recursive groups, so type indices do not
shift. Tables use the canonical nullable-function initializer; active element
segments become lists of `ref.func` expressions. The decoder is a retraction
on this exact source image. These are syntax theorems, not an assertion of
operational correspondence with a complete Core 3 execution relation.
-/

@[expose] public section

namespace Silmaril.Wasm.V1

def Func.toCore (f : Func) : Wasm.Func :=
  ⟨f.type, f.locals.map ValType.toCore, Expr.toCore f.body⟩

def Func.ofCore? (f : Wasm.Func) : Option Func := do
  return ⟨f.type, ← f.locals.mapM ValType.ofCore?, ← Expr.ofCore? f.body⟩

@[simp] theorem Func.ofCore?_toCore (f : Func) : ofCore? f.toCore = some f := by
  cases f
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

def Global.toCore (g : Global) : Wasm.Global := ⟨g.type.toCore, Expr.toCore g.init⟩

def Global.ofCore? (g : Wasm.Global) : Option Global := do
  return ⟨← GlobalType.ofCore? g.type, ← Expr.ofCore? g.init⟩

@[simp] theorem Global.ofCore?_toCore (g : Global) : ofCore? g.toCore = some g := by
  cases g
  simp [toCore, ofCore?]

/-- Original tables implicitly initialize every slot to a null function reference. -/
def TableType.toCoreTable (t : TableType) : Wasm.Table :=
  ⟨t.toCore, [.refNull (.abstract .func)]⟩

def TableType.ofCoreTable? (t : Wasm.Table) : Option TableType :=
  match t.init with
  | [.refNull (.abstract .func)] => ofCore? t.type
  | _ => none

@[simp] theorem TableType.ofCoreTable?_toCoreTable (t : TableType) :
    ofCoreTable? t.toCoreTable = some t := by simp [toCoreTable, ofCoreTable?]

def Elem.toCore (e : Elem) : Wasm.Elem where
  type := funcref
  init := e.init.map fun f => [.refFunc f]
  mode := .active e.table (Expr.toCore e.offset)

/-- Accepts both `funcref` (the type `toCore` assigns) and the non-null `(ref func)`
(the type Core 3.0 decodes the legacy segment form `0:u32 e y*` to, 5.4:101), so that
it also retracts the binary-faithful embedding `toCoreBinary` (a separate cross-version binary-agreement development (not included in this package)). -/
def Elem.ofCore? (e : Wasm.Elem) : Option Elem := do
  if e.type ≠ funcref ∧ e.type ≠ ⟨false, .abstract .func⟩ then none else
    match e.mode with
    | .active table offset =>
        return ⟨table, ← Expr.ofCore? offset,
          ← e.init.mapM (fun | [.refFunc f] => some f | _ => none)⟩
    | _ => none

@[simp] theorem Elem.ofCore?_toCore (e : Elem) : ofCore? e.toCore = some e := by
  cases e
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

def Data.toCore (d : Data) : Wasm.Data :=
  ⟨d.bytes, .active d.memory (Expr.toCore d.offset)⟩

def Data.ofCore? (d : Wasm.Data) : Option Data := do
  match d.mode with
  | .active memory offset => return ⟨memory, ← Expr.ofCore? offset, d.bytes⟩
  | .passive => none

@[simp] theorem Data.ofCore?_toCore (d : Data) : ofCore? d.toCore = some d := by
  cases d
  simp [toCore, ofCore?]

def Module.toCore (m : Module) : Wasm.Module where
  types := m.types.map FuncType.toCoreRec
  imports := m.imports.map Import.toCore
  funcs := m.funcs.map Func.toCore
  globals := m.globals.map Global.toCore
  tables := m.tables.map TableType.toCoreTable
  memories := m.memories.map MemoryType.toCore
  elems := m.elems.map Elem.toCore
  data := m.data.map Data.toCore
  start := m.start
  exports := m.exports.map Export.toCore

def Module.ofCore? (m : Wasm.Module) : Option Module := do
  if !m.tags.isEmpty then none else
    return {
      types := ← m.types.mapM FuncType.ofCoreRec?
      imports := ← m.imports.mapM Import.ofCore?
      funcs := ← m.funcs.mapM Func.ofCore?
      globals := ← m.globals.mapM Global.ofCore?
      tables := ← m.tables.mapM TableType.ofCoreTable?
      memories := ← m.memories.mapM MemoryType.ofCore?
      elems := ← m.elems.mapM Elem.ofCore?
      data := ← m.data.mapM Data.ofCore?
      start := m.start
      exports := ← m.exports.mapM Export.ofCore?
    }

@[simp] theorem Module.ofCore?_toCore (m : Module) : ofCore? m.toCore = some m := by
  cases m
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

theorem Module.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

/-- Type indices are unchanged because every original type contributes exactly one member. -/
@[simp] theorem Module.toCore_typeDefinitions_length (m : Module) :
    m.toCore.typeDefinitions.length = m.types.length := by
  simp [toCore, Wasm.Module.typeDefinitions, FuncType.toCoreRec, Function.comp_def]

end Silmaril.Wasm.V1
