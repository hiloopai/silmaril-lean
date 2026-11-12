module

public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Function

/-! Extensional agreement lets equations between function interpretations be
used directly as equations between interpretations in the identity monad. -/

@[expose] public section

universe u v w q

open Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetCase.LocallyNameless.Derivation

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  (M : InstructionModel D Φ Id)

/-- Agreement as an equality of functions on both environments. -/
theorem denoteFunction_eq_denote_id {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) :
    d.denoteFunction D M = d.denote (m := Id) D M := by
  funext γ ρ
  exact denoteFunction_eq_denote D M d γ ρ

/-- The two interpretations induce the same semantic equality on open terms. -/
theorem denoteFunction_eq_iff_denote_id_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t₁ t₂ : Tm ν Φ n} {A : τ} (d₁ : Derivation Φ Γ β t₁ A)
    (d₂ : Derivation Φ Γ β t₂ A) :
    d₁.denoteFunction D M = d₂.denoteFunction D M ↔
      d₁.denote (m := Id) D M = d₂.denote (m := Id) D M := by
  rw [denoteFunction_eq_denote_id, denoteFunction_eq_denote_id]

/-- The same transfer applies to equality of closed program results. -/
theorem denoteFunctionClosed_eq_iff_denoteClosed_id_eq {t₁ t₂ : Tm Empty Φ 0} {A : τ}
    (d₁ : Derivation Φ (.nil : Ctx Empty τ) .nil t₁ A)
    (d₂ : Derivation Φ (.nil : Ctx Empty τ) .nil t₂ A) :
    d₁.denoteFunctionClosed D M = d₂.denoteFunctionClosed D M ↔
      d₁.denoteClosed (m := Id) D M = d₂.denoteClosed (m := Id) D M := by
  rw [denoteFunctionClosed_eq_denoteClosed, denoteFunctionClosed_eq_denoteClosed]

/-- Case analysis on a left injection agrees with binding its payload. -/
example {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (da : Derivation Φ Γ β a A) (dl : Derivation Φ Γ (.snoc β A) l C)
    (dr : Derivation Φ Γ (.snoc β B) r C) :
    (Derivation.case (.inl da) dl dr).denote (m := Id) D M =
      (Derivation.let₁ da dl).denote (m := Id) D M := by
  apply (denoteFunction_eq_iff_denote_id_eq D M _ _).mp
  funext γ ρ
  simp [denoteFunction]

end Silmaril.Isotope.LetCase.LocallyNameless.Derivation
