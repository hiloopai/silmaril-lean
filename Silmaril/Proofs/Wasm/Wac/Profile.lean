module

public import Silmaril.Wasm.Wac.Profile.Defs
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# WAC composition profile: proofs

* `secOk_merge`: merging two adjacent sections keeps the profile;
* `all_group`: grouping keeps the profile;
* `all_normSection`: splitting a section into its normal form keeps the profile;
* `profile_norm`: the normal form of a profile component is in the profile.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Wat

theorem secOk_merge {s t u : Section} (h : R.merge s t = some u) :
    secOk u = (secOk s && secOk t) := by
  cases s <;> cases t <;> simp [R.merge] at h <;> subst h <;> simp [secOk, List.all_append]

theorem all_group : ∀ l : List Section, l.all secOk = true → (R.group l).all secOk = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := all_group ss h.2
    unfold R.group
    split
    · simp [h.1]
    · rename_i t ts heq
      rw [heq] at ih
      simp only [List.all_cons, Bool.and_eq_true] at ih
      split
      · rename_i u hu
        simp [secOk_merge hu, h.1, ih.1, ih.2]
      · simp [h.1, ih.1, ih.2]

theorem instOk_normInstance (x : InstanceExpr) : instOk (normInstance x) = instOk x := by
  cases x <;> rfl

theorem all_normSection (s : Section) (h : secOk s = true) : (normSection s).all secOk = true := by
  cases s with
  | instances xs =>
    simp only [secOk, List.all_eq_true] at h
    simpa [normSection, secOk, instOk_normInstance] using h
  | aliases xs =>
    simp only [secOk, List.all_eq_true] at h
    simpa [normSection, secOk] using h
  | types xs => simp [normSection, secOk]
  | imports xs => simp [normSection, secOk]
  | exports xs => simp [normSection, secOk]
  | custom n d => simp [normSection, secOk]
  | component c => simp [normSection, secOk]
  | _ => simp [secOk] at h

theorem all_normSections : ∀ ss : List Section, ss.all secOk = true →
    (normSections ss).all secOk = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [normSections, List.all_append, Bool.and_eq_true]
    exact ⟨all_normSection s h.1, all_normSections ss h.2⟩

/-- The normal form of a profile component is in the profile. -/
theorem profile_norm {c : Ast} (h : Profile c) : Profile (norm c) := by
  cases c with
  | mk ss =>
    unfold Profile isProfile at *
    simp only [norm, Ast.sections] at h ⊢
    exact all_group _ (all_normSections ss h)

end Silmaril.Wasm.Wac
