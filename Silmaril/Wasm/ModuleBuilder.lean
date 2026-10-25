module

public import Silmaril.Wasm.Scalar.Module
public import Silmaril.Wasm.TypeUse

/-! # Checked scalar module construction

The operations return the allocated index and an updated source module. They
reject overflow, unresolved type uses, late imports and duplicate or unresolved
exports. Imports must precede all index-bearing definitions and uses, so adding
one cannot silently shift an index already returned by this API. Explicit type
declarations may be collected first; inline signatures then reuse that table.

This is a construction API, not a validator: body typing, constant expressions,
limit bounds and profile restrictions still require `Validation.ModuleValid`.
-/

@[expose] public section
namespace Silmaril.Wasm.Scalar.Module

variable {E : Type}

/-- A single defined function with an optional export. Its signature and body
remain subject to the chosen profile’s separate validator. -/
def ofFunction (signature : V1.FuncType) (locals : List V1.ValType) (body : E)
    (exportName : Option String := none) : Module E where
  types := [signature]
  funcs := [⟨⟨0⟩, locals, body⟩]
  exports := exportName.toList.map fun name => ⟨name, .func ⟨0⟩⟩

@[simp] theorem ofFunction_type (signature : V1.FuncType) (locals : List V1.ValType) (body : E)
    (exportName : Option String) :
    (ofFunction signature locals body exportName).functionType? ⟨0⟩ = some signature := rfl

/-- Import insertion is closed once declarations or index-bearing uses exist. -/
def importsOpen (m : Module E) : Bool :=
  m.funcs.isEmpty && m.globals.isEmpty && m.tables.isEmpty && m.memories.isEmpty &&
    m.elems.isEmpty && m.data.isEmpty && m.start.isNone && m.exports.isEmpty

def addType (m : Module E) (signature : V1.FuncType) :
    Except BuildError (TypeIdx × Module E) := do
  let (i, types) ← TypeTable.append m.types signature
  return (i, {m with types})

/-- Add an import after resolving its function type, if applicable. -/
def addImport (m : Module E) (entry : V1.Import) :
    Except BuildError (V1.ExternIdx × Module E) := do
  if !m.importsOpen then throw .lateImport
  let index ← match entry.desc with
    | .func t => do
      let _ ← (TypeUse.index t).resolve m.types
      let (i, _) ← IndexSpace.append .func 0 m.importedFunctions t
      pure (.func i)
    | .global t => do
      let (i, _) ← IndexSpace.append .global 0 m.importedGlobals t
      pure (.global i)
    | .table t => do
      let (i, _) ← IndexSpace.append .table 0 m.importedTables t
      pure (.table i)
    | .memory t => do
      let (i, _) ← IndexSpace.append .memory 0 m.importedMemories t
      pure (.memory i)
  return (index, {m with imports := m.imports ++ [entry]})

/-- Parameters are part of `use`; `locals` lists only additional locals. -/
def addFunc (m : Module E) (use : TypeUse V1.FuncType) (locals : List V1.ValType) (body : E) :
    Except BuildError (FuncIdx × Module E) :=
  match use.resolve m.types with
  | .error e => .error e
  | .ok (t, types) =>
    match IndexSpace.append .func m.importedFunctions.length m.funcs ⟨t, locals, body⟩ with
    | .error e => .error e
    | .ok (i, funcs) => .ok (i, {m with types, funcs})

def addGlobal (m : Module E) (type : V1.GlobalType) (init : E) :
    Except BuildError (GlobalIdx × Module E) := do
  let (i, globals) ← IndexSpace.append .global m.importedGlobals.length m.globals ⟨type, init⟩
  return (i, {m with globals})

def addTable (m : Module E) (type : V1.TableType) :
    Except BuildError (TableIdx × Module E) := do
  let (i, tables) ← IndexSpace.append .table m.importedTables.length m.tables type
  return (i, {m with tables})

def addMemory (m : Module E) (type : V1.MemoryType) :
    Except BuildError (MemIdx × Module E) := do
  let (i, memories) ← IndexSpace.append .memory m.importedMemories.length m.memories type
  return (i, {m with memories})

def addElem (m : Module E) (entry : Declaration.ActiveElem E) :
    Except BuildError (ElemIdx × Module E) := do
  let (i, elems) ← IndexSpace.append .elem 0 m.elems entry
  return (i, {m with elems})

def addData (m : Module E) (entry : Declaration.ActiveData E) :
    Except BuildError (DataIdx × Module E) := do
  let (i, data) ← IndexSpace.append .data 0 m.data entry
  return (i, {m with data})

def addExport (m : Module E) (name : String) (index : V1.ExternIdx) : Except BuildError (Module E) := do
  if m.exports.any (·.name == name) then throw (.duplicateExport name)
  if !m.exportExists index then
    throw (match index with
      | .func i => .unknownExport .func i.toNat
      | .global i => .unknownExport .global i.toNat
      | .table i => .unknownExport .table i.toNat
      | .memory i => .unknownExport .memory i.toNat)
  return {m with exports := m.exports ++ [⟨name, index⟩]}

/-- Start functions have no parameters or results in both scalar profiles. -/
def setStart (m : Module E) (i : FuncIdx) : Except BuildError (Module E) :=
  if m.functionType? i = some ⟨[], []⟩ then .ok {m with start := some i}
  else .error (.invalidStart i)

theorem addFunc_spec {m m' : Module E} {use : TypeUse V1.FuncType}
    {locals : List V1.ValType} {body : E} {i : FuncIdx}
    (h : m.addFunc use locals body = .ok (i, m')) :
    ∃ t types, use.resolve m.types = .ok (t, types) ∧
      i.toNat = m.importedFunctions.length + m.funcs.length ∧
      m' = {m with types, funcs := m.funcs ++ [⟨t, locals, body⟩]} := by
  cases hr : use.resolve m.types with
  | error e => simp [addFunc, hr] at h
  | ok result =>
    obtain ⟨t, types⟩ := result
    cases ha : IndexSpace.append .func m.importedFunctions.length m.funcs ⟨t, locals, body⟩ with
    | error e => simp [addFunc, hr, ha] at h
    | ok result =>
      obtain ⟨j, funcs⟩ := result
      simp [addFunc, hr, ha] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hi, rfl⟩ := (IndexSpace.append_eq_ok_iff _ _ _ _ _).mp ha
      exact ⟨t, types, rfl, hi, rfl⟩

/-- Adding a definition appends to the function space; prior function indices do
not change, and its type section only grows at the end. -/
theorem addFunc_index_spaces {m m' : Module E} {use : TypeUse V1.FuncType}
    {locals : List V1.ValType} {body : E} {i : FuncIdx}
    (h : m.addFunc use locals body = .ok (i, m')) :
    i.toNat = m.functionTypes.length ∧ m.types <+: m'.types ∧
      ∃ t, m'.functionTypes = m.functionTypes ++ [t] ∧
        ∃ signature, m'.types[t.toNat]? = some signature := by
  obtain ⟨t, types, hr, hi, rfl⟩ := addFunc_spec h
  refine ⟨by simpa using hi, TypeUse.resolve_prefix hr, t, ?_, TypeUse.resolve_exists hr⟩
  simp [functionTypes, importedFunctions, List.append_assoc]

theorem addFunc_lookup {m m' : Module E} {use : TypeUse V1.FuncType}
    {locals : List V1.ValType} {body : E} {i : FuncIdx}
    (h : m.addFunc use locals body = .ok (i, m')) :
    ∃ signature, m'.functionType? i = some signature := by
  obtain ⟨hi, _, t, ht, signature, hs⟩ := addFunc_index_spaces h
  refine ⟨signature, ?_⟩
  simp [functionType?, ht, hi, hs]

/-- The extra locals do not change the function's declared parameter types. -/
theorem addFunc_declaration {m m' : Module E} {use : TypeUse V1.FuncType}
    {locals : List V1.ValType} {body : E} {i : FuncIdx}
    (h : m.addFunc use locals body = .ok (i, m')) :
    ∃ t, m'.funcs[m.funcs.length]? = some ⟨t, locals, body⟩ := by
  obtain ⟨t, types, _, _, rfl⟩ := addFunc_spec h
  exact ⟨t, by simp⟩

theorem addExport_spec {m m' : Module E} {name : String} {index : V1.ExternIdx}
    (h : m.addExport name index = .ok m') :
    name ∉ m.exports.map V1.Export.name ∧ m.exportExists index = true ∧
      m' = {m with exports := m.exports ++ [⟨name, index⟩]} := by
  simp only [addExport] at h
  split at h
  · contradiction
  · rename_i fresh
    split at h
    · contradiction
    · rename_i present
      cases h
      exact ⟨by simpa using fresh, by simpa using present, rfl⟩

theorem addExport_unique {m m' : Module E} {name : String} {index : V1.ExternIdx}
    (unique : (m.exports.map V1.Export.name).Nodup)
    (h : m.addExport name index = .ok m') : (m'.exports.map V1.Export.name).Nodup := by
  obtain ⟨fresh, _, rfl⟩ := addExport_spec h
  simpa [List.nodup_append] using And.intro unique fresh

@[simp] theorem setStart_eq_ok_iff (m m' : Module E) (i : FuncIdx) :
    m.setStart i = .ok m' ↔
      m.functionType? i = some ⟨[], []⟩ ∧ m' = {m with start := some i} := by
  simp only [setStart]
  split <;> simp_all [eq_comm]

end Silmaril.Wasm.Scalar.Module
