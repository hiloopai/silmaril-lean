module

public import Silmaril.Wasm.Lime1.ToCore.Instructions

/-! # Module injection and canonical-image retraction

Function types become singleton final recursive groups; tables receive their
implicit null initializer, and legacy function-index element segments become
`ref.func` initializers. The retraction retains every source module field.
-/

@[expose] public section
namespace Silmaril.Wasm.Lime1

def Func.toCore (f : Func) : Wasm.Func :=
  ⟨f.type, f.locals.map V1.ValType.toCore, Expr.toCore f.body⟩

def Func.ofCore? (f : Wasm.Func) : Option Func := do
  return ⟨f.type, ← f.locals.mapM V1.ValType.ofCore?, ← Expr.ofCore? f.body⟩

@[simp] theorem Func.ofCore?_toCore (f : Func) : ofCore? f.toCore = some f := by
  cases f
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

def Global.toCore (g : Global) : Wasm.Global := ⟨g.type.toCore, Expr.toCore g.init⟩

def Global.ofCore? (g : Wasm.Global) : Option Global := do
  return ⟨← V1.GlobalType.ofCore? g.type, ← Expr.ofCore? g.init⟩

@[simp] theorem Global.ofCore?_toCore (g : Global) : ofCore? g.toCore = some g := by
  cases g
  simp [toCore, ofCore?]

/-- The only table initializer in this profile is the implicit function null. -/
def tableToCore (t : TableType) : Wasm.Table := ⟨t.toCore, [.refNull (.abstract .func)]⟩

def tableOfCore? (t : Wasm.Table) : Option TableType :=
  match t.init with
  | [.refNull (.abstract .func)] => V1.TableType.ofCore? t.type
  | _ => none

@[simp] theorem tableOfCore?_toCore (t : TableType) : tableOfCore? (tableToCore t) = some t := by
  simp [tableOfCore?, tableToCore]

def funcRef (f : FuncIdx) : Wasm.Expr := [.refFunc f]

def funcRef? : Wasm.Expr → Option FuncIdx
  | [.refFunc f] => some f
  | _ => none

@[simp] theorem funcRef?_funcRef (f : FuncIdx) : funcRef? (funcRef f) = some f := rfl

def Elem.toCore (e : Elem) : Wasm.Elem :=
  ⟨V1.funcref, e.init.map funcRef, .active e.table (Expr.toCore e.offset)⟩

/-- Accepts both `funcref` (the type `toCore` assigns) and the non-null `(ref func)`
(the type Core 3.0 decodes the legacy segment form `0:u32 e y*` to, 5.4:101), so that
it also retracts the binary-faithful embedding `toCoreBinary` (a separate cross-version binary-agreement development (not included in this package)). -/
def Elem.ofCore? (e : Wasm.Elem) : Option Elem := do
  if e.type ≠ V1.funcref ∧ e.type ≠ ⟨false, .abstract .func⟩ then none else
    match e.mode with
    | .active table offset => return ⟨table, ← Expr.ofCore? offset, ← e.init.mapM funcRef?⟩
    | _ => none

@[simp] theorem Elem.ofCore?_toCore (e : Elem) : ofCore? e.toCore = some e := by
  cases e
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

def Data.toCore (d : Data) : Wasm.Data := ⟨d.bytes, .active d.memory (Expr.toCore d.offset)⟩

def Data.ofCore? (d : Wasm.Data) : Option Data :=
  match d.mode with
  | .active memory offset => do return ⟨memory, ← Expr.ofCore? offset, d.bytes⟩
  | .passive => none

@[simp] theorem Data.ofCore?_toCore (d : Data) : ofCore? d.toCore = some d := by
  cases d
  simp [toCore, ofCore?]

def Module.toCore (m : Module) : Wasm.Module where
  types := m.types.map V1.FuncType.toCoreRec
  imports := m.imports.map V1.Import.toCore
  tags := []
  globals := m.globals.map Global.toCore
  memories := m.memories.map V1.MemoryType.toCore
  tables := m.tables.map tableToCore
  funcs := m.funcs.map Func.toCore
  data := m.data.map Data.toCore
  elems := m.elems.map Elem.toCore
  start := m.start
  exports := m.exports.map V1.Export.toCore

def Module.ofCore? (m : Wasm.Module) : Option Module := do
  if !m.tags.isEmpty then none else
    return {
      types := ← m.types.mapM V1.FuncType.ofCoreRec?
      imports := ← m.imports.mapM V1.Import.ofCore?
      funcs := ← m.funcs.mapM Func.ofCore?
      globals := ← m.globals.mapM Global.ofCore?
      tables := ← m.tables.mapM tableOfCore?
      memories := ← m.memories.mapM V1.MemoryType.ofCore?
      elems := ← m.elems.mapM Elem.ofCore?
      data := ← m.data.mapM Data.ofCore?
      start := m.start
      exports := ← m.exports.mapM V1.Export.ofCore? }

@[simp] theorem Module.ofCore?_toCore (m : Module) : ofCore? m.toCore = some m := by
  cases m
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

theorem Func.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

theorem Global.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

theorem Elem.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

theorem Data.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

theorem Module.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

end Silmaril.Wasm.Lime1
