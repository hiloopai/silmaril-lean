module

public import Silmaril.Raw.Wasm.Component.Validation.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# The Core 3.0 component profile agrees with the Core 3.0 engine

The Core 3.0 profile of component validation (`core3Profile`, `core3ModuleType?`,
`Validation/Defs.lean`) and the concrete Core 3.0 engine (`Engine.core3 o`,
`Engine/Core3/Defs.lean`) share their carrier of core extern types,
`{τ : CExternType // ExternTypeOk {} τ}`. This file shows that they also agree on everything
validation reads from the engine interface:

* module types: a module has a Core 3.0 module type iff it is a valid Core 3.0 module
  (`core3ModuleType?_isSome_iff`), and the module type is the engine's import and export
  types (`core3ModuleType?_eq_engine`, `coreModuleTypeAgrees_core3`, the condition of
  `Validation/CoreModules.lean` stated for every engine);
* core extern subtyping: the profile's Boolean check is the engine's decision procedure
  `ExternSub.decideEmpty` for its import matching `ExternSub {}` (`core3Profile_extSub_eq_decide`,
  `core3Profile_XSub_iff_engine`);
* flat signatures: the profile's flat view of a function type is the engine's `flatType?`, and
  the core function type of a flat signature is the engine's `ofFlatType`
  (`core3Profile_funcType?_eq`, `core3Profile_ofFlat_eq`);
* core types: a core type space of recursion groups closes them to the defined types that the
  runtime's `$alloctypes` allocates (`defTypes_foldl_ofRec`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Engine
open Wasm.Validation (CExternType ExternTypeOk)

/-- On valid extern types `core3Ext?` succeeds (`ExternTypeOk.check_complete`). -/
theorem core3Ext?_of_ok {τ : CExternType} (h : ExternTypeOk {} τ) :
    core3Ext? τ = some ⟨τ, h⟩ := by
  have hc : Wasm.Validation.ExternTypeOk.check {} τ = true :=
    Wasm.Validation.ExternTypeOk.check_complete
      (Wasm.Validation.TyOk.check_complete Wasm.Validation.TypeCtx.ok_empty rfl) h
  simp [core3Ext?, hc]

/-- On a list of valid extern types, the `mapM` of `core3Ext?` attaches their validity. -/
theorem mapM_core3Ext?_zip {α K : Type} (key : α → K) :
    ∀ (l : List α) (l' : List CExternType) (H : ∀ τ ∈ l', ExternTypeOk {} τ),
      (l.zip l').mapM (fun p => (core3Ext? p.2).map (key p.1, ·)) =
        some ((l.zip (l'.attachWith _ H)).map fun p => (key p.1, p.2))
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: l', H => by
    simp only [List.zip_cons_cons, List.attachWith_cons, List.mapM_cons, List.map_cons,
      core3Ext?_of_ok (H b (List.mem_cons_self ..)), Option.map_some, Option.bind_eq_bind,
      Option.bind_some, mapM_core3Ext?_zip key l l' (fun τ hτ => H τ (List.mem_cons_of_mem _ hτ)),
      Option.pure_def]

/-- On a module accepted by `validate?`, the Core 3.0 module type is the engine's import and
export types. -/
theorem core3ModuleType?_eq_engine {m : Wasm.Module} {mt : Wasm.Validation.CModuleType}
    (h : Wasm.Validation.validate? m = some mt) :
    core3ModuleType? m =
      some ⟨(Core3.importTypesE m).map fun p => ((p.1, p.2.1), p.2.2), Core3.exportTypesE m⟩ := by
  have hi := mapM_core3Ext?_zip (fun i : Wasm.Import => (i.moduleName, i.name)) m.imports
    mt.imports (Core3.validate?_imports_externTypeOk h)
  have he := mapM_core3Ext?_zip Wasm.Export.name m.exports mt.exports
    (Core3.validate?_exports_externTypeOk h)
  simp only [core3ModuleType?, h, Option.bind_eq_bind, Option.bind_some, hi, he,
    Option.pure_def]
  unfold Core3.importTypesE Core3.exportTypesE
  split
  · rename_i mt' h'
    rw [h] at h'
    cases h'
    simp [List.map_map, Function.comp_def]
  · rename_i h'
    rw [h] at h'
    cases h'

/-- A module has a Core 3.0 module type iff it is a valid Core 3.0 module. -/
theorem core3ModuleType?_isSome_iff {m : Wasm.Module} :
    (core3ModuleType? m).isSome ↔ Wasm.Validation.ModuleValid m := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact core3ModuleType?_valid ht
  · intro h
    obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp (Wasm.Validation.validate?_isSome_iff.mpr h)
    rw [core3ModuleType?_eq_engine hmt]
    rfl

/-- The Core 3.0 module types are the concrete engine's import and export types. -/
theorem coreModuleTypeAgrees_core3 (o : SingleThreaded.GrowOracle) :
    CoreModuleTypeAgrees (core3 o) core3ModuleType? := by
  show ∀ (m : Wasm.Module) (t : Types.CoreModuleType Core3Extern),
    core3ModuleType? m = some t →
      t.imports.map (fun p => (p.1.1, p.1.2, p.2)) = Core3.importTypesE m ∧
        t.exports = Core3.exportTypesE m
  intro m t ht
  obtain ⟨mt, hv, -⟩ := core3ModuleType?_spec ht
  rw [core3ModuleType?_eq_engine hv, Option.some.injEq] at ht
  subst ht
  exact ⟨by simp [List.map_map, Function.comp_def], rfl⟩

/-- The profile's core extern subtyping is the engine's decision procedure for import matching
(`ExternSub.decideEmpty`). -/
theorem core3Profile_extSub_eq_decide (o : SingleThreaded.GrowOracle)
    (a b : (core3 o).ExternType) :
    core3Profile.extSub a b = decide ((core3 o).ExternSub a b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact core3Profile_XSub_iff

/-- The profile's core extern subtyping is the engine's import matching. -/
theorem core3Profile_XSub_iff_engine (o : SingleThreaded.GrowOracle)
    {a b : (core3 o).ExternType} : core3Profile.XSub a b ↔ (core3 o).ExternSub a b :=
  core3Profile_XSub_iff

/-- The profile's flat signatures are the engine's (`SingleThreaded.flatType?`). -/
theorem core3FlatType?_eq : core3FlatType? = SingleThreaded.flatType? := by
  have hn : core3NumOf? = SingleThreaded.numOf? := by
    funext t
    cases t <;> rfl
  funext d
  simp only [core3FlatType?, SingleThreaded.flatType?, hn]

/-- The flat signature `canon lift` reads from a core function type is the engine's. -/
theorem core3Profile_funcType?_eq (o : SingleThreaded.GrowOracle) {x : Core3Extern}
    {d : Wasm.Validation.DefType} (hx : x.1 = .func d) :
    core3Profile.view.core.funcType? x = (core3 o).flatType? d := by
  obtain ⟨τ, hτ⟩ := x
  simp only at hx
  subst hx
  show core3FlatType? d = SingleThreaded.flatType? d
  rw [core3FlatType?_eq]

/-- The core function type of a flat signature (`canon lower`, builtins) is the engine's
`ofFlatType`. -/
theorem core3Profile_ofFlat_eq (o : SingleThreaded.GrowOracle) (ft : V1.FuncType) :
    (core3Profile.view.core.ofFlat ft).1 = .func ((core3 o).ofFlatType ft) :=
  rfl

/-- A core type space built from recursion groups alone (the component-level `core rec`
definitions, `Ctx.pushCoreRec`) carries exactly the defined types that `$alloctypes`
(`Execution.Core.allocTypes`) allocates for them. -/
theorem defTypes_foldl_ofRec {X : Type} (rts : List Wasm.RecType) :
    CoreTypeSlot.defTypes
        (rts.foldl (fun (ts : List (CoreTypeSlot X)) r => ts ++ CoreTypeSlot.ofRec ts r) []) =
      Execution.Core.allocTypes rts := by
  suffices h : ∀ (ts : List (CoreTypeSlot X)),
      CoreTypeSlot.defTypes (rts.foldl (fun ts r => ts ++ CoreTypeSlot.ofRec ts r) ts) =
        rts.foldl (fun acc rt => acc ++ (Wasm.Validation.rolldt acc.length
          (Wasm.Validation.liftRec rt)).map (·.substAll (acc.map .dt))) (CoreTypeSlot.defTypes ts)
    from h []
  induction rts with
  | nil => intro ts; rfl
  | cons r rts ih =>
    intro ts
    simp only [List.foldl_cons]
    rw [ih, CoreTypeSlot.defTypes_append, CoreTypeSlot.defTypes_ofRec]
    rfl

end Silmaril.Wasm.Component.Validation
