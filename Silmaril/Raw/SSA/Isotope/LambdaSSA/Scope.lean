module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-!
# Positional expression scope

An expression scoped at `n` may refer to any of its `n` ambient variables.
Each local binder increases that bound; no type or effect information is needed.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Tm

variable {Φ : Type u}

/-- Every variable index is in range at the point where it occurs. -/
def Scoped (n : Nat) : Tm Φ → Prop
  | .var i => i < n
  | .op _ a => Scoped n a
  | .let₁ a b => Scoped n a ∧ Scoped (n + 1) b
  | .pair a b => Scoped n a ∧ Scoped n b
  | .unit => True
  | .let₂ a b => Scoped n a ∧ Scoped (n + 2) b
  | .inl a => Scoped n a
  | .inr a => Scoped n a
  | .case e l r => Scoped n e ∧ Scoped (n + 1) l ∧ Scoped (n + 1) r
  | .abort a => Scoped n a

instance scopedDecidable (n : Nat) (t : Tm Φ) : Decidable (Scoped n t) :=
  match t with
  | .var i => inferInstanceAs (Decidable (i < n))
  | .op _ a | .inl a | .inr a | .abort a => scopedDecidable n a
  | .unit => isTrue True.intro
  | .let₁ a b =>
      letI := scopedDecidable n a
      letI := scopedDecidable (n + 1) b
      inferInstanceAs (Decidable (_ ∧ _))
  | .pair a b =>
      letI := scopedDecidable n a
      letI := scopedDecidable n b
      inferInstanceAs (Decidable (_ ∧ _))
  | .let₂ a b =>
      letI := scopedDecidable n a
      letI := scopedDecidable (n + 2) b
      inferInstanceAs (Decidable (_ ∧ _))
  | .case e l r =>
      letI := scopedDecidable n e
      letI := scopedDecidable (n + 1) l
      letI := scopedDecidable (n + 1) r
      inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Computable scope check. -/
def checkScope (n : Nat) (t : Tm Φ) : Bool := decide (Scoped n t)

@[simp] theorem checkScope_eq_true (n : Nat) (t : Tm Φ) :
    checkScope n t = true ↔ Scoped n t := by simp [checkScope]

/-- Every exactly typed expression is scoped by the length of its value context. -/
theorem HasType.scoped {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} (h : HasType Γ t A) : Scoped Γ.length t := by
  induction h with
  | var h =>
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
      exact hi
  | op _ ih | inl _ ih | inr _ ih | abort _ ih => exact ih
  | let₁ _ _ iha ihb => exact ⟨iha, ihb⟩
  | pair _ _ iha ihb => exact ⟨iha, ihb⟩
  | unit => trivial
  | let₂ _ _ iha ihb => exact ⟨iha, ihb⟩
  | case _ _ _ ihe ihl ihr => exact ⟨ihe, ihl, ihr⟩

end Silmaril.Isotope.LambdaSSA.Tm
