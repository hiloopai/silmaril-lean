module

public import Silmaril.Wasm.Component.Reference.Validation.Defs
public import Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Defs
public import Silmaril.Wasm.Component.Reference.Validation.CoreModules.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Structural.Defs
public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Subtyping.Decide
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Thms
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# `Validation.Defs`: laws of the component reference

Theorems of the component reference copy `Validation.Defs`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.Defs`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType CoreEngine)

section Core3

open Wasm.Validation (CExternType ExternTypeOk DefType CValType)

theorem core3Ext?_val {τ : CExternType} {x : Core3Extern} (h : core3Ext? τ = some x) :
    x.1 = τ := by
  unfold core3Ext? at h
  split at h
  · cases h; rfl
  · cases h

/-- A `mapM` of `core3Ext?` keeps the extern types. -/
theorem mapM_core3Ext?_map {α K : Type} {key : α → K} :
    ∀ {l : List (α × CExternType)} {r : List (K × Core3Extern)},
      l.mapM (fun p => (core3Ext? p.2).map (key p.1, ·)) = some r →
        r.map (fun p => (p.1, p.2.1)) = l.map (fun p => (key p.1, p.2))
  | [], r, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : core3Ext? a.2 with
    | none => simp [ha] at h
    | some x =>
      cases hl : l.mapM (fun p => (core3Ext? p.2).map (key p.1, ·)) with
      | none => simp [ha, hl] at h
      | some r' =>
        simp only [ha, hl, Option.map_some, Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.map_cons, core3Ext?_val ha, mapM_core3Ext?_map hl]

/-- The Core 3.0 module type is `validate?`'s, named positionally by the module's imports and
exports. -/
theorem core3ModuleType?_spec {m : Wasm.Module} {t : CoreModuleType Core3Extern}
    (h : core3ModuleType? m = some t) :
    ∃ mt, Wasm.Validation.validate? m = some mt ∧
      t.imports.map (fun p => (p.1, p.2.1)) =
        (m.imports.zip mt.imports).map (fun p => ((p.1.moduleName, p.1.name), p.2)) ∧
      t.exports.map (fun p => (p.1, p.2.1)) =
        (m.exports.zip mt.exports).map (fun p => (p.1.name, p.2)) := by
  simp only [core3ModuleType?, Option.bind_eq_bind, Option.pure_def] at h
  cases hv : Wasm.Validation.validate? m with
  | none => simp [hv] at h
  | some mt =>
    refine ⟨mt, rfl, ?_⟩
    simp only [hv, Option.bind_some] at h
    cases hi : (m.imports.zip mt.imports).mapM
        (fun p => (core3Ext? p.2).map ((p.1.moduleName, p.1.name), ·)) with
    | none => simp [hi] at h
    | some is =>
      cases he : (m.exports.zip mt.exports).mapM (fun p => (core3Ext? p.2).map (p.1.name, ·)) with
      | none => simp [hi, he] at h
      | some es =>
        simp only [hi, he, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨mapM_core3Ext?_map (key := fun i : Wasm.Import => (i.moduleName, i.name)) hi,
          mapM_core3Ext?_map (key := Wasm.Export.name) he⟩

/-- A core module typed by the Core 3.0 profile is a valid Core 3.0 module. -/
theorem core3ModuleType?_valid {m : Wasm.Module} {t : CoreModuleType Core3Extern}
    (h : core3ModuleType? m = some t) : Wasm.Validation.ModuleValid m := by
  obtain ⟨mt, hv, -⟩ := core3ModuleType?_spec h
  exact ⟨mt, Wasm.Validation.validate?_sound hv⟩

end Core3

section Properties

variable {X : Type} {M N : Type} {feat : Features} {P : DefProfile X}

mutual
  /-- Every core module of a valid definition (nested components included) is typed by the
  core validator. -/
  theorem ValidDef.coreModules_typed {validCore : M → Option (CoreModuleType X)}
      {sc : Scopes X} {s s' : DefState X} {d : Syntax.Definition M}
      (h : ValidDef feat P validCore sc s d s') :
      ∀ m ∈ d.coreModules, ∃ mt, validCore m = some mt := by
    cases h with
    | @coreModule _ _ m mt hm =>
      intro m' hm'
      simp only [Syntax.Definition.coreModules, List.mem_singleton] at hm'
      exact hm' ▸ ⟨mt, hm⟩
    | component h _ => exact ValidDefs.coreModules_typed h
    | _ => intro m hm; simp [Syntax.Definition.coreModules] at hm

  /-- `ValidDef.coreModules_typed` for definition lists. -/
  theorem ValidDefs.coreModules_typed {validCore : M → Option (CoreModuleType X)}
      {sc : Scopes X} {s s' : DefState X} {ds : List (Syntax.Definition M)}
      (h : ValidDefs feat P validCore sc s ds s') :
      ∀ m ∈ Syntax.Definition.coreModulesList ds, ∃ mt, validCore m = some mt := by
    cases h with
    | nil => intro m hm; simp [Syntax.Definition.coreModulesList] at hm
    | cons h hs =>
      intro m hm
      simp only [Syntax.Definition.coreModulesList, List.mem_append] at hm
      rcases hm with hm | hm
      · exact ValidDef.coreModules_typed h m hm
      · exact ValidDefs.coreModules_typed hs m hm
end

/-- Every core module of a valid component is typed by the core validator. -/
theorem ValidComponent.coreModules_typed {validCore : M → Option (CoreModuleType X)}
    {c : Syntax.Component M} {ct : ComponentType Nat X}
    (h : ValidComponent feat P validCore c ct) :
    ∀ m ∈ c.coreModules, ∃ mt, validCore m = some mt :=
  let ⟨_, hs, _⟩ := h
  ValidDefs.coreModules_typed hs

end Properties

/-- A component valid in the Core 3.0 profile has only valid Core 3.0 core modules: the core
module rule types each of them with `validate?`. -/
theorem ValidComponent.core3_moduleValid {feat : Features} {c : Syntax.Component Wasm.Module}
    {ct : ComponentType Nat Core3Extern}
    (h : ValidComponent feat core3Profile core3ModuleType? c ct) :
    ∀ m ∈ c.coreModules, Wasm.Validation.ModuleValid m := fun m hm =>
  let ⟨_, ht⟩ := h.coreModules_typed m hm
  core3ModuleType?_valid ht

/-- `ValidComponentCore3` is the Core 3.0 profile's `ValidComponent`: its `ModuleValid`
conjunct is implied. -/
theorem validComponentCore3_iff {feat : Features} {c : Syntax.Component Wasm.Module}
    {ct : ComponentType Nat Core3Extern} :
    ValidComponentCore3 feat c ct ↔ ValidComponent feat core3Profile core3ModuleType? c ct :=
  ⟨fun h => h.1, fun h => ⟨h, h.core3_moduleValid⟩⟩

end Silmaril.Wasm.Component.Validation
