module

public import Silmaril.Wasm.Link.Recipe

/-! # Resolved imports name real provider definitions

Import resolution returns an export's index. Provider validation and its
import-free profile establish that the index names a source definition, rather
than an imported function or an index outside the function section.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Resolution

open Silmaril.Wasm.Validation

theorem exported_function_bound {provider : Module} {mt : CModuleType}
    {exported : Export} {type : DefType} {f : FuncIdx}
    (hv : validate? provider = some mt) (hp : provider.imports = [])
    (he : (exported, .func type) ∈ provider.exports.zip mt.exports)
    (hx : exported.index = .func f) : f.toNat < provider.funcs.length := by
  cases validate?_sound hv with
  | mk _ hi hC' hC _ _ _ _ hf _ _ _ hexports _ =>
    have hI := hi.length_eq
    rw [hp] at hI
    have hI' := List.length_eq_zero_iff.mp hI.symm
    have hxok := List.forall₂_zip hexports he
    change ExternIdxOk _ exported.index (.func type) at hxok
    rw [hx] at hxok
    cases hxok with
    | func hl =>
      have hb := (List.getElem?_eq_some_iff.mp hl).1
      rw [hC, hC'] at hb
      simp only [hI', CExternType.funcs, List.nil_append] at hb
      rwa [← hf.length_eq] at hb

/-- An index returned by actual resolution is within the provider's source
function section; it can safely be turned into a prepared store address. -/
theorem import_target_bound {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    {i : Nat} {entry : Import} {expected : DefType}
    (hi : consumer.imports[i]? = some entry)
    (ht : w.consumerType.imports[i]? = some (.func expected)) :
    ∃ f, w.imports[i]? = some f ∧ f.toNat < provider.funcs.length := by
  obtain ⟨f, _, exported, _, hf, _, _, he, hx, _⟩ := w.import_lookup hi ht
  exact ⟨f, hf, exported_function_bound w.providerValidation w.providerImports
    (List.mem_of_find?_eq_some he) hx⟩

/-- All indices produced by a successful import-resolution run name provider
definitions. This follows from the actual resolver and provider validator. -/
theorem resolveImports?_bounds {namespaceName : String} {provider consumer : Module}
    {providerType consumerType : CModuleType} {resolved : List FuncIdx}
    (hv : validate? provider = some providerType) (hp : provider.imports = [])
    (h : resolveImports? namespaceName provider consumer providerType consumerType = some resolved) :
    ∀ f ∈ resolved, f.toNat < provider.funcs.length := by
  unfold resolveImports? at h
  have hr : List.Forall₂ (fun _ f => f.toNat < provider.funcs.length)
      (consumer.imports.zip consumerType.imports) resolved := by
    apply List.mapM_some_forall₂ (as := consumer.imports.zip consumerType.imports) _ h
    intro ⟨entry, expected⟩ f he
    dsimp only at he
    split at he
    · cases he
    · cases hx : entry.type <;> simp only [hx] at he
      all_goals try contradiction
      cases ht : expected <;> simp only [ht] at he
      all_goals try contradiction
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨exported, actualType⟩, hfind, he⟩ := he
      cases hx : exported.index <;> simp only [hx] at he
      all_goals try contradiction
      cases hd : actualType <;> simp only [hd] at he
      all_goals try contradiction
      split at he
      · cases he
        have hmem := List.mem_of_find?_eq_some hfind
        rw [hd] at hmem
        exact exported_function_bound hv hp hmem hx
      · split at he
        · cases he
          have hmem := List.mem_of_find?_eq_some hfind
          rw [hd] at hmem
          exact exported_function_bound hv hp hmem hx
        · cases he
  clear h
  generalize hx : consumer.imports.zip consumerType.imports = xs at hr
  clear hx
  induction hr with
  | nil => simp
  | cons hab _ ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hab
    · exact ih f hf

theorem assembly_imports_bounded {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    ∀ f ∈ w.imports, f.toNat < provider.funcs.length :=
  resolveImports?_bounds w.providerValidation w.providerImports w.resolved

end Silmaril.Wasm.Link.GC.Resolution
