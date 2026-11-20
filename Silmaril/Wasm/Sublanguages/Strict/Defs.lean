module

public import Silmaril.Wasm.Sublanguages.Link.Defs

/-! The strict functional syntax admits function imports, not imported
resources. Its closed variant has no import field at all. The earlier
`Profiles.Strict` is unchanged. -/

@[expose] public section

namespace Silmaril.Wasm.Sublanguages

/-- A source function import, with no constructor for a memory, table,
global or tag import. Type uses are resolved by Core validation. -/
structure FunctionImport where
  moduleName : String
  name : String
  type : TypeIdx
  deriving DecidableEq, Repr

def FunctionImport.toCore (entry : FunctionImport) : Import :=
  ⟨entry.moduleName, entry.name, .func entry.type⟩

def FunctionImport.ofCore? (entry : Import) : Option FunctionImport :=
  match entry.type with
  | .func type => some ⟨entry.moduleName, entry.name, type⟩
  | _ => none

structure FunctionExport where
  name : String
  index : FuncIdx
  deriving DecidableEq, Repr

def FunctionExport.toCore (entry : FunctionExport) : Export := ⟨entry.name, .func entry.index⟩

def FunctionExport.ofCore? (entry : Export) : Option FunctionExport :=
  match entry.index with
  | .func index => some ⟨entry.name, index⟩
  | _ => none

/-- Local section data, not a validated standalone module. Bodies, exports
and the start index can refer to functions from the accompanying imports. -/
structure LocalSections where
  types : List RecType := []
  funcs : List Func := []
  start : Option FuncIdx := none
  exports : List FunctionExport := []
  deriving Repr

def LocalSections.assemble (sections : LocalSections) (imports : List FunctionImport) : Wasm.Module :=
  { types := sections.types, imports := imports.map FunctionImport.toCore,
    funcs := sections.funcs, start := sections.start, exports := sections.exports.map FunctionExport.toCore }

/-- Module shape with only function imports and exports, and no local
resources or segments. The raw bodies still need a feature and typing check. -/
structure FunctionModule where
  sections : LocalSections := {}
  imports : List FunctionImport := []
  deriving Repr

def FunctionModule.toCore (mod : FunctionModule) : Wasm.Module := mod.sections.assemble mod.imports

/-- The sections absent from `FunctionModule`. This guard says nothing about
the kinds of imports and exports, which are checked independently. -/
def FunctionModule.noResourceSections (mod : Wasm.Module) : Bool :=
  mod.tags.isEmpty && mod.globals.isEmpty && mod.memories.isEmpty && mod.tables.isEmpty &&
    mod.data.isEmpty && mod.elems.isEmpty

def FunctionModule.ofCore? (mod : Wasm.Module) : Option FunctionModule := do
  if !noResourceSections mod then none else
    let imports ← mod.imports.mapM FunctionImport.ofCore?
    let exports ← mod.exports.mapM FunctionExport.ofCore?
    some ⟨⟨mod.types, mod.funcs, mod.start, exports⟩, imports⟩

/-- The type uses in the exact Core function index order. No type groups
are reordered or deduplicated. -/
def FunctionModule.functionTypes (mod : FunctionModule) : List TypeIdx :=
  mod.imports.map FunctionImport.type ++ mod.sections.funcs.map Func.type

/-- Source signature lookup, not a validation judgment or a closed type. -/
def FunctionModule.functionSignature? (mod : FunctionModule) (index : FuncIdx) : Option FuncType := do
  let type ← mod.functionTypes[index.toNat]?
  match (mod.sections.types.flatMap RecType.types)[type.toNat]? with
  | some ⟨_, _, .func signature⟩ => some signature
  | _ => none

def strictCaps : Models.FeatureSet := Profiles.FunctionalCore.features .immutable .disabled

/-- Immutable-GC, no-memory, no-exception syntax, with function imports.
The feature witness is not a validation proof or a purity guarantee. -/
abbrev Strict := { mod : FunctionModule // Models.Module.InFeat strictCaps mod.toCore }

def Strict.toCore (mod : Strict) : Wasm.Module := mod.val.toCore

def Strict.ofCore? (mod : Wasm.Module) : Option Strict := do
  let candidate ← FunctionModule.ofCore? mod
  if admitted : Models.Module.InFeat strictCaps candidate.toCore then some ⟨candidate, admitted⟩ else none

/-- A strict module with no import field. Existing closed-profile theorems
do not automatically apply to the import-bearing `Strict` syntax. -/
abbrev Ultrastrict := { sections : LocalSections // Models.Module.InFeat strictCaps (sections.assemble []) }

def Ultrastrict.toStrict (mod : Ultrastrict) : Strict := ⟨⟨mod.val, []⟩, mod.property⟩

def Ultrastrict.toCore (mod : Ultrastrict) : Wasm.Module := mod.toStrict.toCore

def Ultrastrict.ofCore? (mod : Wasm.Module) : Option Ultrastrict := do
  let candidate ← Strict.ofCore? mod
  if closed : candidate.val.imports = [] then
    some ⟨candidate.val.sections, closed ▸ candidate.property⟩
  else none

/-- The actual Core module judgment at its closed import/export interface. -/
abbrev Strict.Checked (iface : Validation.CModuleType) :=
  { mod : Strict // Validation.ModuleOk mod.toCore iface }

def Strict.Checked.toCore {iface : Validation.CModuleType} (mod : Strict.Checked iface) :
    Profiles.CheckedModule Profiles.Wasm3 iface := ⟨mod.val.toCore, mod.property⟩

/-- Check the complete assembled module, including all import type uses and
calls, with the existing Core validator. -/
def Strict.validate? (mod : Strict) : Option (Σ iface, Strict.Checked iface) :=
  match checked : Validation.validate? mod.toCore with
  | none => none
  | some iface => some ⟨iface, mod, Validation.validate?_sound checked⟩

end Silmaril.Wasm.Sublanguages
