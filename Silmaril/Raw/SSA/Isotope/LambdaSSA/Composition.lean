module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

/-!
# Single-exit region composition

This specializes mathematical continuation substitution. As with `lsubst`,
semantic use requires pure branch arguments. The continuation receives the
first region's result followed by its original captured context.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type u} {τ : Type v}
open Silmaril.DeBruijn

/-- Replace a region's exits by the same continuation. Exact typing below
restricts the first region to a single result type. -/
def seq (r k : Region Φ) : Region Φ := r.lsubst (fun _ => k)

@[simp] theorem seq_br (ℓ : Nat) (a : Tm Φ) (k : Region Φ) :
    (.br ℓ a : Region Φ).seq k = k.substVars (Tm.singleSubst a) := rfl

/-- The second continuation gains the first result as a captured variable. -/
theorem seq_assoc (r s t : Region Φ) :
    (r.seq s).seq t = r.seq (s.seq (t.renameVars (lift Nat.succ))) := by
  exact lsubst_comp r (fun _ => s) (fun _ => t)

theorem substVars_seq (r k : Region Φ) (θ : Nat → Tm Φ) :
    (r.seq k).substVars θ = (r.substVars θ).seq (k.substVars (Tm.liftSubst θ)) := by
  exact substVars_lsubst r (fun _ => k) θ

theorem renameVars_seq (r k : Region Φ) (ρ : Nat → Nat) :
    (r.seq k).renameVars ρ = (r.renameVars ρ).seq (k.renameVars (lift ρ)) := by
  exact renameVars_lsubst r (fun _ => k) ρ

theorem renameLabels_seq (r k : Region Φ) (ρ : Nat → Nat) :
    (r.seq k).renameLabels ρ = r.seq (k.renameLabels ρ) := by
  exact renameLabels_lsubst r (fun _ => k) ρ

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.seq {Γ : VCtx τ} {L : LCtx τ} {r k : Region Φ} {A : τ}
    (hr : HasType Γ r [A]) (hk : HasType (A :: Γ) k L) : HasType Γ (r.seq k) L := by
  apply hr.lsubst
  intro ℓ B h
  cases ℓ with
  | zero =>
      have hAB : A = B := Option.some.inj h
      subst B
      exact hk
  | succ ℓ => simp [At] at h

end Silmaril.Isotope.LambdaSSA.Region
