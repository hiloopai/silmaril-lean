module

public import Silmaril.Logic.Arithmetic.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.Arithmetic

open Silmaril.Logic.Arithmetic

variable {n : ℕ} {Γ : Context n} {ψ : Formula n}
variable {Ax : {n : ℕ} → Formula n → Type}

/-- Soundness with assumptions, including the eigenvariable cases. -/
theorem derivation_sound (hAx : ∀ {n} {φ : Formula n}, Ax φ → Valid φ)
    (d : Derivation Ax Γ ψ) (e : Assignment n) (hΓ : Satisfies e Γ) : ψ.eval e := by
  induction d with
  | hyp h => exact hΓ _ h
  | ax h => exact hAx h e
  | weaken h _ ih => exact ih e (fun φ hφ => hΓ φ (h φ hφ))
  | impIntro _ ih =>
    intro hφ
    exact ih e (by
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hφ
      · exact hΓ _ hχ)
  | impElim _ _ ih₁ ih₂ => exact ih₁ e hΓ (ih₂ e hΓ)
  | botElim _ ih => exact (ih e hΓ).elim
  | classical _ ih => exact Classical.byContradiction (ih e hΓ)
  | conjIntro _ _ ih₁ ih₂ => exact ⟨ih₁ e hΓ, ih₂ e hΓ⟩
  | conjLeft _ ih => exact (ih e hΓ).1
  | conjRight _ ih => exact (ih e hΓ).2
  | disjLeft _ ih => exact Or.inl (ih e hΓ)
  | disjRight _ ih => exact Or.inr (ih e hΓ)
  | disjElim _ _ _ ih₁ ih₂ ih₃ =>
    rcases ih₁ e hΓ with hφ | hψ
    · exact ih₂ e (by
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hφ
      · exact hΓ _ hχ)
    · exact ih₃ e (by
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hψ
      · exact hΓ _ hχ)
  | allIntro _ ih =>
    intro x
    apply ih (extend e x)
    rintro χ hχ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hχ
    exact (Formula.eval_shift φ e x).2 (hΓ φ hφ)
  | allElim _ t ih => exact (Formula.eval_inst _ t e).2 (ih e hΓ (t.eval e))
  | exIntro t _ ih => exact ⟨t.eval e, (Formula.eval_inst _ t e).1 (ih e hΓ)⟩
  | exElim _ _ ih₁ ih₂ =>
    obtain ⟨x, hx⟩ := ih₁ e hΓ
    apply (Formula.eval_shift _ e x).1
    apply ih₂ (extend e x)
    intro χ hχ
    rcases List.mem_cons.1 hχ with rfl | hχ
    · exact hx
    · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hχ
      exact (Formula.eval_shift φ e x).2 (hΓ φ hφ)
  | eqRefl => rfl
  | eqElim φ _ _ ih₁ ih₂ =>
    apply (Formula.eval_inst φ _ e).2
    have h := (Formula.eval_inst φ _ e).1 (ih₂ e hΓ)
    have heq := ih₁ e hΓ
    change _ = _ at heq
    rwa [heq] at h


end Silmaril.Proofs.Logic.Arithmetic
