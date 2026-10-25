module

public import Silmaril.Logic.Arithmetic.Peano
public import Silmaril.Logic.Arithmetic.Completeness.QuantifierFree

@[expose] public section

/-! Soundness and proof reconstruction for first-order arithmetic. The model
here is Lean's natural numbers; `QProof` and `PAProof` retain finite derivation
trees. See `docs/projects/logic.md` for the syntax and the available fragments. -/

namespace Silmaril.Logic.Arithmetic.Theorems

variable {n : ℕ} {Γ : Context n} {φ : Formula n}

/-- Every Q derivation is valid in the standard natural-number interpretation. -/
theorem q_sound (d : QProof Γ φ) (e : Assignment n) (hΓ : Satisfies e Γ) : φ.eval e :=
  qSound d e hΓ

/-- PA's induction schema is sound for every formula and every finite context. -/
theorem pa_sound (d : PAProof Γ φ) (e : Assignment n) (hΓ : Satisfies e Γ) : φ.eval e :=
  paSound d e hΓ

/-- The Q-to-PA translation maps actual proof trees, including the predecessor axiom. -/
theorem q_provable_in_pa (d : QProof Γ φ) : Nonempty (PAProof Γ φ) := ⟨qToPA d⟩

/-- Relative to Lean's natural-number model, Q has no closed proof of falsehood. -/
theorem q_consistent : ¬ Nonempty (QProof [] (.bot : Sentence)) := by
  rintro ⟨d⟩
  exact qSound d Fin.elim0 (by simp [Satisfies])

/-- The same standard-model argument applies to PA. -/
theorem pa_consistent : ¬ Nonempty (PAProof [] (.bot : Sentence)) := by
  rintro ⟨d⟩
  exact paSound d Fin.elim0 (by simp [Satisfies])

/-- Closed quantifier-free truth is reconstructed as a Q proof. -/
theorem quantifier_free_complete {p : Sentence} (hp : Completeness.QuantifierFree p) :
    Nonempty (QProof [] p) ↔ p.eval Fin.elim0 := Completeness.quantifierFree_complete hp

/-- Existential quantifier-free truth is reconstructed using an explicit numeral witness. -/
theorem existential_quantifier_free_complete (p : Formula 1)
    (hp : Completeness.QuantifierFree p) :
    Nonempty (QProof [] (.ex p)) ↔ ∃ k, p.eval (extend Fin.elim0 k) :=
  Completeness.existentialQuantifierFree_complete p hp

end Silmaril.Logic.Arithmetic.Theorems
