module

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Lime1.ToCore.Modules
public import Silmaril.Wasm.Validation.Types

/-!
# Structural view of Core 3.0 modules

Syntax-level helpers about Core 3.0 modules (`Silmaril.Wasm.Module`), in the namespace
`Engine.Core3`. They depend only on the module syntax and on `Validation/Types.lean`, not on
Core 3.0 instruction typing or execution, so they can be imported without the Core 3.0 machine
(`Engine/Core3.lean`). The component validator's Core 3.0 profile does not use them: it types
core modules with `validate?` over closed extern types (`Validation/Defs.lean`).

* Index spaces (imports first, then definitions) and the extern type of an index
  (`externTypeOf?`); import types `importTypes` and export types `exportTypes?` read off the
  syntax. Type indices inside these `Wasm.ExternType`s stay relative to the module.
* `funcTypeAt?`: the function type named by a type index (Core 3.0 requires `C.types[x]` to
  expand to a function type for function and tag types).
* `StructurallyValid` (decidable, `checkStructure`): structure of the recursive groups
  (`RecType.checkStructure`); every entry of every index space is structurally valid, with
  function and tag type indices naming a `func` composite type; resolvable exports with
  distinct names; a start function of type `[] -> []`. Instruction bodies, initializers,
  segments and declared sub-type matching are NOT checked. Hence all import and export types
  are structurally valid (`StructurallyValid.import_valid`, `StructurallyValid.export_valid`).
* Flat canon signatures as numeric Core 3.0 function types (`ofFlatType`, partial inverse
  `flatType?`, `flatType?_eq_some_iff`) and the flat signature of a function export
  (`exportFuncType?`, `exportFlatType?`), as compared by a component-level `canon lift`.
* `ImportsMatch E s vs m`: positional import matching in an engine store, the check the
  component instantiator performs with `ExternSub` against `externType?`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace Core3

/-! ## Structural typing of Core 3.0 modules -/

/-- Flat canon signatures as numeric Core 3.0 function types. -/
abbrev ofFlatType (ft : V1.FuncType) : Wasm.FuncType := V1.FuncType.toCore ft

/-- The flat numeric signature of a Core 3.0 function type, if all its types are numeric. -/
abbrev flatType? (t : Wasm.FuncType) : Option V1.FuncType := V1.FuncType.ofCore? t

theorem flatType?_ofFlatType (ft : V1.FuncType) : flatType? (ofFlatType ft) = some ft :=
  V1.FuncType.ofCore?_toCore ft

/-- Import types of a module, in positional order. -/
def importTypes (m : Wasm.Module) : List (String × String × Wasm.ExternType) :=
  m.imports.map fun i => (i.moduleName, i.name, i.type)

/-- Imported tags. -/
def importedTags (m : Wasm.Module) : List TagType :=
  m.imports.filterMap fun i => match i.type with
    | .tag t => some t
    | _ => none

/-- Imported globals. -/
def importedGlobals (m : Wasm.Module) : List GlobalType :=
  m.imports.filterMap fun i => match i.type with
    | .global t => some t
    | _ => none

/-- Imported memories. -/
def importedMemories (m : Wasm.Module) : List MemoryType :=
  m.imports.filterMap fun i => match i.type with
    | .memory t => some t
    | _ => none

/-- Imported tables. -/
def importedTables (m : Wasm.Module) : List TableType :=
  m.imports.filterMap fun i => match i.type with
    | .table t => some t
    | _ => none

/-- The tag index space: imports first, then definitions. -/
def tagTypes (m : Wasm.Module) : List TagType := importedTags m ++ m.tags

/-- The global index space. -/
def globalTypes (m : Wasm.Module) : List GlobalType :=
  importedGlobals m ++ m.globals.map Global.type

/-- The memory index space. -/
def memoryTypes (m : Wasm.Module) : List MemoryType := importedMemories m ++ m.memories

/-- The table index space. -/
def tableTypes (m : Wasm.Module) : List TableType := importedTables m ++ m.tables.map (·.type)

/-- The extern type of an index into one of the module's index spaces. -/
def externTypeOf? (m : Wasm.Module) : ExternIdx → Option Wasm.ExternType
  | .tag i => (tagTypes m)[i.toNat]?.map .tag
  | .global i => (globalTypes m)[i.toNat]?.map .global
  | .memory i => (memoryTypes m)[i.toNat]?.map .memory
  | .table i => (tableTypes m)[i.toNat]?.map .table
  | .func i => m.functionTypes[i.toNat]?.map .func

/-- Export types of a module, `none` if some export index does not resolve. -/
def exportTypes? (m : Wasm.Module) : Option (List (String × Wasm.ExternType)) :=
  m.exports.mapM fun e => (externTypeOf? m e.index).map (e.name, ·)

/-- The function type named by a type index: `some ft` exactly when the index is in range and
its sub type has composite type `func ft` (Core 3.0 requires `C.types[x]` to expand to a
function type for function and tag types). Type indices inside `ft` stay module-relative. -/
def funcTypeAt? (types : List SubType) (i : TypeIdx) : Option Wasm.FuncType :=
  match types[i.toNat]? with
  | some ⟨_, _, .func ft⟩ => some ft
  | _ => none

/-- Structural validity of an extern type in a module with type definitions `types`:
function and tag types must name a `func` composite type; limits must be ordered and within
the address-space bound; value types must be in scope. -/
def externTypeValid (types : List SubType) : Wasm.ExternType → Bool
  | .tag i => (funcTypeAt? types i).isSome
  | .global g => decide (g.Valid types.length)
  | .memory t => decide t.Valid
  | .table t => decide (t.Valid types.length)
  | .func i => (funcTypeAt? types i).isSome

/-- Every entry of every index space (imports first, then local definitions), as extern
types. Every import and every export type is one of these. -/
def allExternTypes (m : Wasm.Module) : List Wasm.ExternType :=
  (tagTypes m).map .tag ++ (globalTypes m).map .global ++ (memoryTypes m).map .memory ++
    (tableTypes m).map .table ++ m.functionTypes.map .func

/-- The function type of a function index, resolved through the type definitions. -/
def funcTypeOfIdx? (m : Wasm.Module) (i : FuncIdx) : Option Wasm.FuncType :=
  m.functionTypes[i.toNat]?.bind (funcTypeAt? m.typeDefinitions)

/-- The start function, if any, resolves to a function of type `[] -> []`. -/
def startValid (m : Wasm.Module) : Bool :=
  match m.start with
  | none => true
  | some i => decide (funcTypeOfIdx? m i = some ⟨[], []⟩)

/-- Sequential structural check of the recursive groups (`RecType.checkStructure`). -/
def recGroupsValid : List SubType → List RecType → Bool
  | _, [] => true
  | prev, g :: gs => g.checkStructure prev && recGroupsValid (prev ++ g.types) gs

/-- The executable structural check of a Core 3.0 module: structure of the recursive groups;
validity of every index-space entry (imported and locally defined tags, globals, memories,
tables and function type indices, via `externTypeValid`); resolvable exports with distinct
names; a start function of type `[] -> []`. It does NOT check instruction bodies,
initializers, segments or sub-type matching: the repository has no Core 3.0 instruction
typing and no closed recursive-type matching. -/
def checkStructure (m : Wasm.Module) : Bool :=
  recGroupsValid [] m.types &&
    (allExternTypes m).all (externTypeValid m.typeDefinitions) &&
    (exportTypes? m).isSome &&
    decide (m.exports.map (·.name)).Nodup &&
    startValid m

/-- Structural validity of a Core 3.0 module (decidable; see `checkStructure`). -/
def StructurallyValid (m : Wasm.Module) : Prop := checkStructure m = true

instance (m : Wasm.Module) : Decidable (StructurallyValid m) :=
  inferInstanceAs (Decidable (checkStructure m = true))

/-- The function type of a `func` extern type, resolved through the module's types. -/
def externFuncType? (m : Wasm.Module) : Wasm.ExternType → Option Wasm.FuncType
  | .func i => funcTypeAt? m.typeDefinitions i
  | _ => none

/-- The resolved function type of the export `name` (`none` if it is missing, not a function,
or does not resolve). This is what a component-level `canon lift` of a Core 3.0 export
compares against its flattened signature (REF `canon_lift`, `flatten_functype`). -/
def exportFuncType? (m : Wasm.Module) (name : String) : Option Wasm.FuncType :=
  (exportTypes? m).bind fun es => (es.lookup name).bind (externFuncType? m)

/-- The flat numeric signature of the export `name`, if it is a function with one. -/
def exportFlatType? (m : Wasm.Module) (name : String) : Option V1.FuncType :=
  (exportFuncType? m name).bind flatType?

/-- Positional import matching in an engine store (the check the component instantiator
performs with `ExternSub` against `externType?`): every provided value has a type that is a
subtype of the corresponding declared import type. -/
def ImportsMatch (E : CoreEngine) {H : Type} (s : E.Store H) (vs : List E.ExternVal)
    (m : E.Module) : Prop :=
  List.Forall₂ (fun v ι => ∃ τ, E.externType? s v = some τ ∧ E.ExternSub τ ι.2.2) vs
    (E.importTypes m)

end Core3

end Silmaril.Wasm.Component.Engine
