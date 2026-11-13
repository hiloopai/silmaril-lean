module

public import Silmaril.Raw.SSA.Isotope.Refinement.Typing

@[expose] public section

noncomputable section

/-! # Quantitative substitution judgments

These are the three rules of Figure `expr-subst` in the written refinement
calculus.  A substitution has one term for every variable of its target
context.  In particular, a zero-usage slot may contain an ill-typed term;
replacing this rule with pointwise typing would strengthen the presentation.
-/

namespace Silmaril.Isotope.Refinement

universe u v w
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

set_option autoImplicit true in
/-- Native quantity- and effect-aware substitutions from the paper.
The source context is split between the older substitution and the newest
entry.  Context linearity controls reuse; commutation controls effects. -/
inductive Substitution (F : Fragment) : {n m : Nat} →
    QCtx τ m → ε → (Fin n → Term Φ m) → QCtx τ n → Type (max u v w)
  | nil {Γ : QCtx τ m} {e : ε} (discard : Γ.Discardable) :
      Substitution F Γ e Fin.elim0 QCtx.nil
  | zero {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
      (hσ : Substitution F Γ e σ Δ) (a : Term Φ m) (A : τ) :
      Substitution F Γ e (Fin.cases a σ) (Δ.snoc A .zero)
  | cons {Γ Γl Γr : QCtx τ m} {Δ : QCtx τ n} {e el er : ε}
      {σ : Fin n → Term Φ m} {a : Term Φ m} {A : τ} {q : Quantity}
      (split : Γ.Split Γl Γr) (hσ : Substitution F Γl el σ Δ)
      (ha : HasType F Γr er a A) (usage : q ≤ Γr.linearity)
      (commute : EffectSystem.commutes el er) (leftEffect : el ≤ e) (rightEffect : er ≤ e) :
      Substitution F Γ e (Fin.cases a σ) (Δ.snoc A (.used q))

namespace Substitution

variable {F G : Fragment} {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
variable {e e' : ε} {σ : Fin n → Term Φ m}

/-- A larger aggregate effect bound does not change entry effects or the
commutation obligation in a quantitative substitution. -/
def effectMono (h : Substitution F Γ e σ Δ) (he : e ≤ e') :
    Substitution F Γ e' σ Δ := by
  induction h with
  | nil h => exact .nil h
  | zero _ a A ih => exact .zero (ih he) a A
  | cons split hσ ha q comm hl hr =>
    exact .cons split hσ ha q comm (hl.trans he) (hr.trans he)

/-- Fragment inclusions act on every retained entry derivation. -/
def embed (h : Substitution F Γ e σ Δ) (hFG : F.Includes G) :
    Substitution G Γ e σ Δ := by
  induction h with
  | nil h => exact .nil h
  | zero _ a A ih => exact .zero ih a A
  | cons split _ ha q comm hl hr ih =>
    exact .cons split ih (ha.embed hFG) q comm hl hr

end Substitution
end Silmaril.Isotope.Refinement
