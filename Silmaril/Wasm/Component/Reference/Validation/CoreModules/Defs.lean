module

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.ModuleBuilder

/-!
# Core module types of V1 and Lime1 modules

The component-level validator types a `core module` definition by its index-free
`Types.CoreModuleType X` (`Explainer.md` §Type Checking): the imports in declaration order keyed by
`(module, name)` with their extern types, and the exports keyed by name with the extern type of the
exported definition.

Provided:

* `scalarModuleType` over the shared scalar module record `Scalar.Module E` (V1 and Lime1
  share imports, exports, types, tables, memories and globals; only bodies differ), with
  `lime1ModuleType` and `v1ModuleType` as its two instances. Import function types are
  resolved through the type section; exports are resolved through the combined
  (imports-first) index spaces to function types, funcref tables, i32 memories and globals
  (`Engine.CoreExternType`). A module whose import type index or export index is out of
  range has no module type (`none`).
* the total lists `lime1ImportTypes` / `lime1ExportTypes` (shape of the engine fields
  `Engine.CoreEngine.importTypes` / `exportTypes`), the predicate
  `CoreModuleTypeAgrees E mt` stated only with `Engine/Interface.lean` definitions, and
  `lime1ModuleType_importTypes`: whenever `lime1ModuleType m = some t`, the imports and
  exports of `t` are exactly `lime1ImportTypes m` and `lime1ExportTypes m`.
* `v1ModuleType_toLime : lime1ModuleType m.toLime = v1ModuleType m`.
* Core 3.0 modules (`Silmaril.Wasm.Module`) are typed by the Core 3.0 validator `validate?`,
  over closed extern types (`core3ModuleType?`, `Validation/Defs.lean`).

NOT modelled or claimed: core module validity (`V1.Validation.ModuleValid`, the Lime1
validation judgment; `Validation/Defs.lean` conjoins it), duplicate export names, and the
statement for the concrete `Engine.Lime1.lime1` engine: `CoreModuleTypeAgrees lime1
lime1ModuleType` follows from `lime1ModuleType_importTypes` once `lime1.importTypes` /
`exportTypes` are (propositionally) `lime1ImportTypes` / `lime1ExportTypes`; that lemma needs the
engine definition and is not stated here.

Global mutability is `mutable := true` exactly for `Mutability.var`. V1/Lime1 tables and
memories always have address type `.i32`; limits are the 32-bit bounds as `Nat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Engine (CoreExternType CoreEngine)

/-! ## Scalar (V1 / Lime1) modules -/

/-- The core extern type of a V1/Lime1 global type. -/
def scalarGlobalType (g : V1.GlobalType) : CoreExternType :=
  .global g.value (decide (g.mutability = .var))

/-- The core extern type of a V1/Lime1 (funcref, i32) table type. -/
def scalarTableType (t : V1.TableType) : CoreExternType :=
  .table .i32 t.limits.min.val (t.limits.max.map Fin.val)

/-- The core extern type of a V1/Lime1 (i32) memory type. -/
def scalarMemoryType (t : V1.MemoryType) : CoreExternType :=
  .memory .i32 t.limits.min.val (t.limits.max.map Fin.val)

/-- The extern type of an import descriptor; a function import resolves its type index in
the type section `types` (`none` when out of range). -/
def scalarImportType? (types : List V1.FuncType) : V1.ImportDesc → Option CoreExternType
  | .func t => (types[t.toNat]?).map .func
  | .table t => some (scalarTableType t)
  | .memory t => some (scalarMemoryType t)
  | .global t => some (scalarGlobalType t)

variable {E : Type}

/-- The extern type of an export index, resolved through the imports-first index spaces. -/
def scalarExportType? (m : Scalar.Module E) : V1.ExternIdx → Option CoreExternType
  | .func i => (m.functionType? i).map .func
  | .table i => (m.tableTypes[i.toNat]?).map scalarTableType
  | .memory i => (m.memoryTypes[i.toNat]?).map scalarMemoryType
  | .global i => (m.globalTypes[i.toNat]?).map scalarGlobalType

/-- One typed import entry. -/
def scalarImportEntry? (m : Scalar.Module E) (i : V1.Import) :
    Option ((String × String) × CoreExternType) :=
  (scalarImportType? m.types i.desc).map fun x => ((i.moduleName, i.name), x)

/-- One typed export entry. -/
def scalarExportEntry? (m : Scalar.Module E) (e : V1.Export) :
    Option (String × CoreExternType) :=
  (scalarExportType? m e.index).map fun x => (e.name, x)

/-- The core module type of a scalar (V1 or Lime1) module: imports in declaration order and
exports with resolved types; `none` if any import or export fails to resolve. -/
def scalarModuleType (m : Scalar.Module E) : Option (Types.CoreModuleType CoreExternType) := do
  let imports ← m.imports.mapM (scalarImportEntry? m)
  let exports ← m.exports.mapM (scalarExportEntry? m)
  pure ⟨imports, exports⟩

/-- The core module type of a Lime1 module. -/
def lime1ModuleType (m : Lime1.Module) : Option (Types.CoreModuleType CoreExternType) :=
  scalarModuleType m

/-- The core module type of a WebAssembly 1.0 module. -/
def v1ModuleType (m : V1.Module) : Option (Types.CoreModuleType CoreExternType) :=
  scalarModuleType m

/-- Total import list in the shape of `CoreEngine.importTypes` (unresolvable entries are
dropped; they cannot occur when `lime1ModuleType m` is defined). -/
def lime1ImportTypes (m : Lime1.Module) : List (String × String × CoreExternType) :=
  m.imports.filterMap fun i => (scalarImportEntry? m i).map fun p => (p.1.1, p.1.2, p.2)

/-- Total export list in the shape of `CoreEngine.exportTypes`. -/
def lime1ExportTypes (m : Lime1.Module) : List (String × CoreExternType) :=
  m.exports.filterMap (scalarExportEntry? m)

/-- Agreement of a module-type function with an engine's `importTypes`/`exportTypes`
(stated with `Engine/Interface.lean` definitions only). -/
def CoreModuleTypeAgrees (Eng : CoreEngine)
    (mt : Eng.Module → Option (Types.CoreModuleType Eng.ExternType)) : Prop :=
  ∀ m t, mt m = some t →
    t.imports.map (fun p => (p.1.1, p.1.2, p.2)) = Eng.importTypes m ∧
      t.exports = Eng.exportTypes m

/-! ## Tests -/

/-- A copy of `V1.Validation.Examples.addModule` (same builder call, type, body and export),
inlined so that this library file does not import an examples module. -/
def CoreModules.addModule : V1.Module :=
  Scalar.Module.ofFunction ⟨[.int .i32, .int .i32], [.int .i32]⟩ []
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add] (some "add")

end Silmaril.Wasm.Component.Validation
