module

public import Silmaril.Wasm.Component.Reference.Validation.CoreModules.Defs

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Raw.Wasm.Component.Types.Basic
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

variable {E : Type}

private theorem mapM_eq_filterMap {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r = l.filterMap f
  | [], r, h => by simp_all
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some r' =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [hfa, mapM_eq_filterMap f l r' hl]

/-- `lime1ModuleType` agrees with the total import/export lists `lime1ImportTypes` and
`lime1ExportTypes` (the engine-field shapes of `CoreEngine.importTypes`/`exportTypes`). -/
theorem lime1ModuleType_importTypes (m : Lime1.Module) (t : Types.CoreModuleType CoreExternType)
    (h : lime1ModuleType m = some t) :
    t.imports.map (fun p => (p.1.1, p.1.2, p.2)) = lime1ImportTypes m ∧
      t.exports = lime1ExportTypes m := by
  simp only [lime1ModuleType, scalarModuleType, Option.bind_eq_bind, Option.pure_def] at h
  cases hi : m.imports.mapM (scalarImportEntry? m) with
  | none => simp [hi] at h
  | some is =>
    cases he : m.exports.mapM (scalarExportEntry? m) with
    | none => simp [hi, he] at h
    | some es =>
      simp only [hi, he, Option.bind_some, Option.some.injEq] at h
      subst h
      refine ⟨?_, mapM_eq_filterMap _ _ _ he⟩
      rw [mapM_eq_filterMap _ _ _ hi, lime1ImportTypes, List.map_filterMap]

/-- Any engine whose import/export fields are `lime1ImportTypes`/`lime1ExportTypes` on Lime1
modules agrees with `lime1ModuleType`. -/
theorem coreModuleTypeAgrees_of_lime1 (Eng : CoreEngine) (hM : Eng.Module = Lime1.Module)
    (hX : Eng.ExternType = CoreExternType)
    (himp : ∀ m, Eng.importTypes m = hX ▸ lime1ImportTypes (hM ▸ m))
    (hexp : ∀ m, Eng.exportTypes m = hX ▸ lime1ExportTypes (hM ▸ m)) :
    CoreModuleTypeAgrees Eng (fun m => hX ▸ lime1ModuleType (hM ▸ m)) := by
  cases Eng with
  | mk Module Valid FuncType _ ExternType ExternSub ofFlatType flatType? importTypes
      exportTypes =>
    cases hM; cases hX
    intro m t h
    simp only at himp hexp h ⊢
    rw [himp, hexp]
    exact lime1ModuleType_importTypes m t h

/-- The V1-to-Lime1 injection preserves module types. -/
theorem v1ModuleType_toLime (m : V1.Module) : lime1ModuleType m.toLime = v1ModuleType m := by
  have hfun : (Scalar.Module.functionTypes m.toLime) = Scalar.Module.functionTypes m := by
    simp [Scalar.Module.functionTypes, V1.Module.toLime, Scalar.Module.importedFunctions,
      List.map_map, Function.comp_def, V1.Func.toLime]
  have hglob : (Scalar.Module.globalTypes m.toLime) = Scalar.Module.globalTypes m := by
    simp [Scalar.Module.globalTypes, V1.Module.toLime, Scalar.Module.importedGlobals,
      List.map_map, Function.comp_def, V1.Global.toLime]
  have hexp : ∀ x, scalarExportType? m.toLime x = scalarExportType? m x := by
    intro x
    cases x with
    | func i => simp only [scalarExportType?, Scalar.Module.functionType?, hfun]; rfl
    | global i => simp only [scalarExportType?, hglob]
    | table i => rfl
    | memory i => rfl
  have himpE : scalarImportEntry? m.toLime = scalarImportEntry? m := by
    funext i; simp [scalarImportEntry?, V1.Module.toLime]
  have hexpE : scalarExportEntry? m.toLime = scalarExportEntry? m := by
    funext e; simp [scalarExportEntry?, hexp]
  simp only [lime1ModuleType, v1ModuleType, scalarModuleType, himpE, hexpE]
  simp [V1.Module.toLime]

/-! ## Tests -/

/-- The V1 adder module has no imports and one export `add : [i32, i32] -> [i32]`. -/
theorem v1ModuleType_addModule :
    v1ModuleType CoreModules.addModule =
      some ⟨[], [("add", .func ⟨[.int .i32, .int .i32], [.int .i32]⟩)]⟩ := rfl

/-- The same through the V1-to-Lime1 injection. -/
theorem lime1ModuleType_addModule :
    lime1ModuleType CoreModules.addModule.toLime =
      some ⟨[], [("add", .func ⟨[.int .i32, .int .i32], [.int .i32]⟩)]⟩ := rfl

/-- A small scalar module with a function import, a global, a memory and re-exports. -/
private def importModule : V1.Module where
  types := [⟨[.int .i32], []⟩]
  imports := [⟨"env", "log", .func ⟨0⟩⟩, ⟨"env", "g", .global ⟨.var, .int .i64⟩⟩]
  memories := [⟨⟨1, some 2⟩⟩]
  exports := [⟨"log", .func ⟨0⟩⟩, ⟨"mem", .memory ⟨0⟩⟩, ⟨"g", .global ⟨0⟩⟩]

example : v1ModuleType importModule = some
    ⟨[(("env", "log"), .func ⟨[.int .i32], []⟩), (("env", "g"), .global (.int .i64) true)],
     [("log", .func ⟨[.int .i32], []⟩), ("mem", .memory .i32 1 (some 2)),
      ("g", .global (.int .i64) true)]⟩ := rfl

/-- An out-of-range export index has no module type. -/
example : v1ModuleType { importModule with exports := [⟨"t", .table ⟨0⟩⟩] } = none := rfl

end Silmaril.Wasm.Component.Validation
