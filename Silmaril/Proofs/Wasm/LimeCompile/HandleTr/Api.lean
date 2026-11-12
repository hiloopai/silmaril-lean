module

public import Silmaril.Wasm.LimeCompile.HandleTr.Defs
public import Silmaril.Wasm.LimeCompile.Handle.Thms
public import Silmaril.Wasm.LimeCompile.Preserve.Thms

/-!
# The handle compiler: the export API is translated by `handleApi`

* `rwApi`: the handle rewrite of a resolved export type;
* `exportApi_hModule`: with handle-free imports, the export API of `hModule M` is the pointwise
  `rwApi` image of the API of `M`;
* `handleTy_of_rw`: where the image is a Lime type, `Handle.handleTy` is that image;
* `compile0_api`, `compile_api`: a successful compilation has the `handleApi` translation of the
  source API.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy ApiLime limeVal)
open Silmaril.Wasm.LimeCompile.Preserve.Module (exportApi resolve typeAt impTables impMems
  impGlobals impTags)
open Silmaril.Wasm.LimeCompile.Handle (handleRef handleVal handleTy handleEntry handleApi)
open Silmaril.Wasm.LimeCompile.HandleTr

/-- The handle rewrite of a resolved export type. -/
def rwApi : ApiTy → ApiTy
  | .func st => .func (hSub st)
  | .global t => .global { t with value := hv t.value }
  | .tag st => .tag (hSub st)
  | t => t

theorem typeAt_hModule (M : Module) (x : TypeIdx) :
    typeAt (hModule M) x = (typeAt M x).map hSub := by
  simp only [typeAt, Module.typeDefinitions, hModule, hRec, List.flatMap_map]
  rw [← List.getElem?_map, List.map_flatMap]

theorem functionTypes_hModule (M : Module) : (hModule M).functionTypes = M.functionTypes := by
  simp [Module.functionTypes, Module.importedFunctions, hModule, hFunc, List.map_map,
    Function.comp_def]

theorem impGlobals_handleFree {M : Module} (h : importsHandleFree M = true) :
    ∀ t ∈ impGlobals M, handleRef t.value = false := by
  intro t ht
  simp only [impGlobals, List.mem_filterMap] at ht
  obtain ⟨i, hi, hit⟩ := ht
  have hf := List.all_eq_true.mp h i hi
  unfold importHandleFree at hf
  split at hit <;> simp_all

/-- The rewrite of a global type. -/
def hvG (t : GlobalType) : GlobalType := { t with value := hv t.value }

theorem globals_hModule {M : Module} (h : importsHandleFree M = true) :
    impGlobals M ++ (M.globals.map hGlobal).map Global.type =
      (impGlobals M ++ M.globals.map Global.type).map hvG := by
  have hI : (impGlobals M).map hvG = impGlobals M := by
    conv => rhs; rw [← List.map_id (impGlobals M)]
    apply List.map_congr_left
    intro t ht
    simp [hvG, hv, impGlobals_handleFree h t ht]
  rw [List.map_append, hI, List.map_map, List.map_map]
  rfl

theorem resolve_hModule {M : Module} (h : importsHandleFree M = true) (x : ExternIdx) :
    resolve (hModule M) x = (resolve M x).map rwApi := by
  cases x with
  | func i =>
    simp only [resolve, functionTypes_hModule, typeAt_hModule, Option.map_bind, Option.map_map]
    congr 1
    funext y
    simp only [Function.comp_apply, Option.map_map]
    cases typeAt M y <;> rfl
  | table i =>
    simp only [resolve, impTables, hModule]
    rw [Option.map_map]
    congr 1
  | memory i =>
    simp only [resolve, impMems, hModule]
    rw [Option.map_map]
    congr 1
  | global i =>
    show resolve (hModule M) (.global i) = (resolve M (.global i)).map rwApi
    have hg : impGlobals M ++ (M.globals.map hGlobal).map Global.type =
        (impGlobals M ++ M.globals.map Global.type).map hvG := globals_hModule h
    have hr : resolve (hModule M) (.global i) =
        ((impGlobals M ++ (M.globals.map hGlobal).map Global.type)[i.value.val]?).map .global :=
      rfl
    have hr' : resolve M (.global i) =
        ((impGlobals M ++ M.globals.map Global.type)[i.value.val]?).map .global := rfl
    rw [hr, hr', hg, List.getElem?_map, Option.map_map, Option.map_map]
    rfl
  | tag i =>
    have ht : impTags (hModule M) ++ (hModule M).tags = impTags M ++ M.tags := rfl
    simp only [resolve, ht, typeAt_hModule, Option.map_bind, Option.map_map]
    congr 1
    funext y
    simp only [Function.comp_apply, Option.map_map]
    cases typeAt M y <;> rfl

/-- **The export API of the rewrite** (handle-free imports). -/
theorem exportApi_hModule {M : Module} (h : importsHandleFree M = true) :
    exportApi (hModule M) = (exportApi M).map fun p => (p.1, p.2.map rwApi) := by
  simp only [exportApi, List.map_map, Function.comp_def, resolve_hModule h]
  rfl

theorem hv_lime {t : ValType} (h : limeVal (hv t) = true) : handleVal t = some (hv t) := by
  unfold hv at h ⊢
  unfold handleVal
  by_cases hr : handleRef t = true
  · simp only [hr, ↓reduceIte] at h ⊢
    cases t with
    | num _ => cases hr
    | vec _ => cases hr
    | ref _ => rfl
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp [h]

theorem mapM_hv : ∀ {l : List ValType}, (l.map hv).all limeVal = true →
    l.mapM handleVal = some (l.map hv)
  | [], _ => rfl
  | t :: l, h => by
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.mapM_cons, hv_lime h.1, mapM_hv h.2, List.map_cons, Option.bind_eq_bind,
      Option.pure_def, Option.bind_some]

/-- Where the rewritten type is a Lime type, `handleTy` is the rewrite. -/
theorem handleTy_of_rw {t : ApiTy} (h : (rwApi t).lime = true) : handleTy t = some (rwApi t) := by
  cases t with
  | func st =>
    obtain ⟨fin, sups, body⟩ := st
    cases body with
    | func ft =>
      cases fin <;> cases sups <;>
        simp only [rwApi, hSub, hComp, hFT, ApiTy.lime, Bool.false_eq_true] at h
      simp only [Bool.and_eq_true] at h
      simp only [handleTy, mapM_hv h.1, mapM_hv h.2, rwApi, hSub, hComp, hFT]
    | struct _ => simp [rwApi, hSub, hComp, ApiTy.lime] at h
    | array _ => simp [rwApi, hSub, hComp, ApiTy.lime] at h
  | table t => simp [rwApi, handleTy, show (ApiTy.table t).lime = true from h]
  | memory t => simp [rwApi, handleTy, show (ApiTy.memory t).lime = true from h]
  | global t =>
    simp only [rwApi, ApiTy.lime] at h
    simp [handleTy, hv_lime h, rwApi]
  | tag st => simp [rwApi, ApiTy.lime] at h

theorem handleApi_of_rw : ∀ {A : List (String × Option ApiTy)},
    ApiLime (A.map fun p => (p.1, p.2.map rwApi)) →
      handleApi A = some (A.map fun p => (p.1, p.2.map rwApi))
  | [], _ => rfl
  | (n, o) :: A, h => by
    have hA := handleApi_of_rw (A := A) fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp : handleEntry (n, o) = some (n, o.map rwApi) := by
      cases o with
      | none => rfl
      | some t =>
        show (handleTy t).map (fun t' => (n, some t')) = some (n, some (rwApi t))
        rw [handleTy_of_rw (h _ List.mem_cons_self (rwApi t) rfl)]
        rfl
    unfold handleApi at hA ⊢
    simp only [List.mapM_cons, hp, hA, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
      List.map_cons]

/-- **The API of a compiled module** (non-Lime branch). -/
theorem compile0_api {M : Module} {l : Lime1.Module} (h : compile0 M = some l) :
    handleApi (exportApi M) = some (exportApi l.toCore) := by
  unfold compile0 at h
  split at h
  · rename_i hi
    have he : exportApi l.toCore = (exportApi M).map fun p => (p.1, p.2.map rwApi) := by
      rw [Silmaril.Wasm.LimeCompile.Direct.compile_toCore h, Silmaril.Proofs.Wasm.LimeCompile.Handle.exportApi_lowerModule,
        exportApi_hModule hi]
    rw [he]
    exact handleApi_of_rw (he ▸ Silmaril.Wasm.LimeCompile.Preserve.apiLime_toCore l)
  · cases h

/-- **The API of a compiled module.** -/
theorem compile_api {M : Module} {l : Lime1.Module} (h : compile M = some l) :
    handleApi (exportApi M) = some (exportApi l.toCore) := by
  unfold compile Silmaril.Wasm.LimeCompile.Preserve.limePres at h
  cases hv : Silmaril.Wasm.LimeCompile.Preserve.limeView M with
  | some l' =>
    rw [hv] at h
    cases h
    have hM : l.toCore = M := Silmaril.Wasm.LimeCompile.Preserve.limeView_eq_some_iff.mp hv
    subst hM
    exact Silmaril.Proofs.Wasm.LimeCompile.Handle.handleApi_of_apiLime
      (Silmaril.Wasm.LimeCompile.Preserve.apiLime_toCore l)
  | none =>
    rw [hv] at h
    exact compile0_api h

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
