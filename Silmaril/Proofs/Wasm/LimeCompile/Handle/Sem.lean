module

public import Silmaril.Proofs.Wasm.LimeCompile.Handle.Basic
public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.LimeCompile.Select.Defs

/-!
# Handle translation: scripts, sessions and exact equivalence

* `paramsOf_lime`: a Lime API has no handle parameter;
* `scriptRel_eq`: so a script related to a source script at a Lime API is that script;
* `equivUpTo_of_exportEquiv`: exact export equivalence at a Lime source API is equivalence up to
  the handle translation, for every handle table;
* `exportApi_mapFuncs`: rewriting function bodies (keeping their type indices) keeps the export
  API (`exportApi_lowerModule`, `exportApi_selM`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Handle

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ExportEquiv SessionRel Call)
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy limeVal ApiLime)
open Silmaril.Wasm.LimeCompile.Handle

theorem handleRef_of_lime {t : ValType} (h : limeVal t = true) : handleRef t = false := by
  cases t with
  | num _ => rfl
  | vec _ => cases h
  | ref _ => cases h

/-- A Lime API has no handle parameter. -/
theorem paramsOf_lime {A : List (String × Option ApiTy)} (hA : ApiLime A) {x : String}
    {ps : List ValType} (h : paramsOf A x = some ps) : ∀ t ∈ ps, handleRef t = false := by
  unfold paramsOf at h
  split at h
  · rename_i n fin sup ft hfind
    cases h
    have hl := hA _ (List.mem_of_find?_eq_some hfind) _ rfl
    intro t ht
    apply handleRef_of_lime
    cases fin <;> cases sup <;> simp_all [ApiTy.lime]
  · cases h

theorem forall₂_zip_eq {σ : List Val} :
    ∀ {ps : List ValType} {ws vs : List Val}, vs.length = ps.length →
      (∀ t ∈ ps, handleRef t = false) →
      List.Forall₂ (fun w tv => ArgRel σ tv.1 w tv.2) ws (ps.zip vs) → ws = vs
  | [], ws, [], _, _, h => by
    cases h
    rfl
  | t :: ps, ws, v :: vs, hl, hp, h => by
    rw [List.zip_cons_cons] at h
    cases h with
    | cons ha t' =>
      have hv : _ := forall₂_zip_eq (by simpa using hl)
        (fun u hu => hp u (List.mem_cons_of_mem t hu)) t'
      subst hv
      rcases ha with ⟨-, rfl⟩ | ⟨ht, -⟩
      · rfl
      · rw [hp t List.mem_cons_self] at ht
        cases ht

theorem argsRel_eq {σ : List Val} {ps : List ValType} {ws vs : List Val}
    (hp : ∀ t ∈ ps, handleRef t = false) (h : ArgsRel σ ps ws vs) : ws = vs := by
  unfold ArgsRel at h
  split at h
  · rename_i hl
    exact forall₂_zip_eq hl hp h
  · exact h

/-- At a Lime source API, a related script is the source script. -/
theorem scriptRel_eq {σ : List Val} {A : List (String × Option ApiTy)} (hA : ApiLime A) :
    ∀ {sc' sc : List Call}, ScriptRel σ A sc' sc → sc' = sc
  | _, _, .nil => rfl
  | ⟨x', ws⟩ :: _, ⟨x, vs⟩ :: _, .cons hc ht => by
    obtain ⟨hx, hc⟩ := hc
    have hw : ws = vs := by
      revert hc
      dsimp only
      split
      · rename_i ps hps
        exact argsRel_eq (paramsOf_lime hA hps)
      · exact id
    cases hx
    rw [hw, scriptRel_eq hA ht]

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Exact equivalence at a Lime source API is equivalence up to handles.** -/
theorem equivUpTo_of_exportEquiv {σ : List Val} {m' m : Module}
    (hA : ApiLime (Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi m))
    (he : ExportEquiv (· = ·) P host m' m) : EquivUpTo σ P host m' m := by
  refine ⟨⟨he.1.instantiates, ?_⟩, ⟨he.2.instantiates, ?_⟩⟩
  · intro s xas sc' sc hs hsc bs hbs
    obtain rfl := scriptRel_eq hA hsc
    obtain ⟨bs', hbs', hr⟩ := he.1.obs s xas sc' hs bs hbs
    exact ⟨bs', hbs', hr.mono fun _ _ h => Or.inl h⟩
  · intro s xas sc' sc hs hsc bs' hbs'
    obtain rfl := scriptRel_eq hA hsc
    obtain ⟨bs, hbs, hr⟩ := he.2.obs s xas sc' hs bs' hbs'
    exact ⟨bs, hbs, hr.mono fun _ _ h => Or.inl h⟩

/-- Rewriting function bodies, keeping type indices, keeps the export API. -/
theorem exportApi_mapFuncs (M : Module) (f : Func → Func) (hf : ∀ x, (f x).type = x.type) :
    Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi { M with funcs := M.funcs.map f } =
      Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi M := by
  have hft : Module.functionTypes { M with funcs := M.funcs.map f } = M.functionTypes := by
    simp [Module.functionTypes, Module.importedFunctions, List.map_map, Function.comp_def, hf]
  have hr : Silmaril.Wasm.LimeCompile.Preserve.Module.resolve { M with funcs := M.funcs.map f } =
      Silmaril.Wasm.LimeCompile.Preserve.Module.resolve M := by
    funext i
    cases i <;> simp only [Silmaril.Wasm.LimeCompile.Preserve.Module.resolve, hft] <;> rfl
  unfold Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi
  rw [hr]

theorem exportApi_lowerModule (M : Module) :
    Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi (Silmaril.Wasm.LimeCompile.Direct.lowerModule M) =
      Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi M :=
  exportApi_mapFuncs M _ fun _ => rfl

theorem exportApi_selM (M : Module) :
    Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi (Silmaril.Wasm.LimeCompile.Select.selM M) =
      Silmaril.Wasm.LimeCompile.Preserve.Module.exportApi M :=
  exportApi_mapFuncs M _ fun _ => rfl

end Silmaril.Proofs.Wasm.LimeCompile.Handle
