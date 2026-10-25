module

public import Silmaril.Wasm.V1.Declarations

/-! # Scalar module index spaces and expression maps

Imported declarations precede definitions in each independent index space.
Function type indices are retained even when unresolved; validation decides
whether those references exist and whether each body has the declared type.
-/

@[expose] public section
namespace Silmaril.Wasm.Scalar.Module

variable {E F G : Type}

def importedFunctions (m : Module E) : List TypeIdx :=
  m.imports.filterMap fun i => match i.desc with | .func t => some t | _ => none

def importedGlobals (m : Module E) : List V1.GlobalType :=
  m.imports.filterMap fun i => match i.desc with | .global t => some t | _ => none

def importedTables (m : Module E) : List V1.TableType :=
  m.imports.filterMap fun i => match i.desc with | .table t => some t | _ => none

def importedMemories (m : Module E) : List V1.MemoryType :=
  m.imports.filterMap fun i => match i.desc with | .memory t => some t | _ => none

def functionTypes (m : Module E) : List TypeIdx :=
  m.importedFunctions ++ m.funcs.map Declaration.Func.type

def globalTypes (m : Module E) : List V1.GlobalType :=
  m.importedGlobals ++ m.globals.map Declaration.Global.type

def tableTypes (m : Module E) : List V1.TableType := m.importedTables ++ m.tables

def memoryTypes (m : Module E) : List V1.MemoryType := m.importedMemories ++ m.memories

/-- A lookup composes the function and type index spaces. -/
def functionType? (m : Module E) (i : FuncIdx) : Option V1.FuncType := do
  let t ← m.functionTypes[i.toNat]?
  m.types[t.toNat]?

/-- The declaration shape relevant for resolving an export. -/
def exportExists (m : Module E) : V1.ExternIdx → Bool
  | .func i => i.toNat < m.functionTypes.length
  | .global i => i.toNat < m.globalTypes.length
  | .table i => i.toNat < m.tableTypes.length
  | .memory i => i.toNat < m.memoryTypes.length

@[simp] theorem functionTypes_length (m : Module E) :
    m.functionTypes.length = m.importedFunctions.length + m.funcs.length := by
  simp [functionTypes]

/-- Existing type indices remain references to the same signature when the type
section is extended. -/
theorem type_lookup_append (types extra : List V1.FuncType) (i : TypeIdx)
    (h : i.toNat < types.length) :
    (types ++ extra)[i.toNat]? = types[i.toNat]? := List.getElem?_append_left h

/-- Change the expression language in every body, initializer and active offset.
Names, bytes, type declarations and all indices are preserved. -/
def mapExpr (f : E → F) (m : Module E) : Module F where
  types := m.types
  imports := m.imports
  funcs := m.funcs.map (Declaration.Func.mapBody f)
  globals := m.globals.map (Declaration.Global.mapInit f)
  tables := m.tables
  memories := m.memories
  elems := m.elems.map fun e => ⟨e.table, f e.offset, e.init⟩
  data := m.data.map fun d => ⟨d.memory, f d.offset, d.bytes⟩
  start := m.start
  exports := m.exports

@[simp] theorem mapExpr_id (m : Module E) : m.mapExpr id = m := by
  have hf : Declaration.Func.mapBody (V := V1.ValType) (E := E) id = id :=
    funext Declaration.Func.mapBody_id
  have hg : Declaration.Global.mapInit (T := V1.GlobalType) (E := E) id = id :=
    funext Declaration.Global.mapInit_id
  cases m
  simp [mapExpr, hf, hg]

@[simp] theorem mapExpr_comp (f : E → F) (g : F → G) (m : Module E) :
    (m.mapExpr f).mapExpr g = m.mapExpr (g ∘ f) := by
  cases m
  simp [mapExpr, List.map_map, Function.comp_def, Declaration.Func.mapBody,
    Declaration.Global.mapInit]

@[simp] theorem mapExpr_functionTypes (f : E → F) (m : Module E) :
    (m.mapExpr f).functionTypes = m.functionTypes := by
  simp [mapExpr, functionTypes, importedFunctions, List.map_map, Declaration.Func.mapBody]

@[simp] theorem mapExpr_functionType? (f : E → F) (m : Module E) (i : FuncIdx) :
    (m.mapExpr f).functionType? i = m.functionType? i := by
  simp only [functionType?, mapExpr_functionTypes]
  rfl

end Silmaril.Wasm.Scalar.Module
