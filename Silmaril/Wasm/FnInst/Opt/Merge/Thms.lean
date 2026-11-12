module

public import Silmaril.Wasm.FnInst.Opt.Merge.Defs

@[expose] public section

/-! # wasm-merge as amalgamation: the amalgamation property and generic merge correctness

* `amalgam_reduct_left`, `amalgam_reduct_right`: the amalgam of two models that agree on the
  shared names `X₁ ∩ X₂` has the given reducts;
* `amalgam_unique`: it is the only such model of `X₁ ∪ X₂` (the pushout square of named
  contexts has the amalgamation property, with uniqueness);
* `merge_sat`: generic merge correctness: sentences of each side satisfied by its model are
  satisfied, translated along the pushout inclusions, by the amalgam. Only the satisfaction
  condition of `namedInst` is used.
-/

namespace Silmaril.Wasm.FnInst.Opt.Merge

open Silmaril.Wasm.FnInst.Opt CategoryTheory
open scoped Classical

variable {X₁ X₂ : Set String}

/-- Two models agree on the shared names. -/
def Agree (M₁ : NModel X₁) (M₂ : NModel X₂) : Prop := ∀ f, f ∈ X₁ → f ∈ X₂ → M₁.1 f = M₂.1 f

theorem amalgam_val (M₁ : NModel X₁) (M₂ : NModel X₂) (f : String) :
    (NModel.amalgam M₁ M₂).1 f = if f ∈ X₁ then M₁.1 f else M₂.1 f := by
  show (if f ∈ X₁ then M₁.1 f else M₂.1 f) = _
  congr

theorem amalgam_reduct_left (M₁ : NModel X₁) (M₂ : NModel X₂) :
    NModel.reduct (inl X₁ X₂) (NModel.amalgam M₁ M₂) = M₁ := by
  apply Subtype.ext
  funext f
  rw [NModel.reduct_val, amalgam_val]
  by_cases h₁ : f ∈ X₁
  · rw [ite_eq_left h₁, ite_eq_left h₁]
  · rw [ite_eq_right h₁, M₁.2 f h₁]

theorem amalgam_reduct_right (M₁ : NModel X₁) (M₂ : NModel X₂) (hag : Agree M₁ M₂) :
    NModel.reduct (inr X₁ X₂) (NModel.amalgam M₁ M₂) = M₂ := by
  apply Subtype.ext
  funext f
  rw [NModel.reduct_val, amalgam_val]
  by_cases h₂ : f ∈ X₂
  · rw [ite_eq_left h₂]
    by_cases h₁ : f ∈ X₁
    · rw [ite_eq_left h₁, hag f h₁ h₂]
    · rw [ite_eq_right h₁]
  · rw [ite_eq_right h₂, M₂.2 f h₂]

/-- **Amalgamation, uniqueness.** A model of the union is determined by its two reducts. -/
theorem amalgam_unique (M₁ : NModel X₁) (M₂ : NModel X₂) (M : NModel (X₁ ∪ X₂))
    (h₁ : NModel.reduct (inl X₁ X₂) M = M₁) (h₂ : NModel.reduct (inr X₁ X₂) M = M₂) :
    M = NModel.amalgam M₁ M₂ := by
  apply Subtype.ext
  funext f
  rw [amalgam_val]
  have e₁ := congrFun (congrArg Subtype.val h₁) f
  have e₂ := congrFun (congrArg Subtype.val h₂) f
  rw [NModel.reduct_val] at e₁ e₂
  by_cases hf₁ : f ∈ X₁
  · rw [ite_eq_left hf₁] at e₁ ⊢
    exact e₁
  · rw [ite_eq_right hf₁]
    by_cases hf₂ : f ∈ X₂
    · rw [ite_eq_left hf₂] at e₂
      exact e₂
    · rw [ite_eq_right hf₂] at e₂
      rw [← e₂]
      exact M.2 f (fun h => h.elim hf₁ hf₂)

/-- **Generic merge correctness.** If each side's model satisfies a sentence, the amalgam
satisfies both translated sentences. -/
theorem merge_sat (M₁ : NModel X₁) (M₂ : NModel X₂) (hag : Agree M₁ M₂)
    (φ₁ : namedPlain.Sen X₁) (φ₂ : namedPlain.Sen X₂)
    (h₁ : namedPlain.Sat M₁ φ₁) (h₂ : namedPlain.Sat M₂ φ₂) :
    namedPlain.Sat (NModel.amalgam M₁ M₂) (namedPlain.map (inl X₁ X₂) φ₁) ∧
      namedPlain.Sat (NModel.amalgam M₁ M₂) (namedPlain.map (inr X₁ X₂) φ₂) := by
  refine ⟨(namedPlain.sat_map _ _ _).2 ?_, (namedPlain.sat_map _ _ _).2 ?_⟩
  · show namedPlain.Sat (NModel.reduct (inl X₁ X₂) (NModel.amalgam M₁ M₂)) φ₁
    rw [amalgam_reduct_left]
    exact h₁
  · show namedPlain.Sat (NModel.reduct (inr X₁ X₂) (NModel.amalgam M₁ M₂)) φ₂
    rw [amalgam_reduct_right M₁ M₂ hag]
    exact h₂

end Silmaril.Wasm.FnInst.Opt.Merge
