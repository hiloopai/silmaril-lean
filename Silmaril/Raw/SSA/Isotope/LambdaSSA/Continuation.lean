module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Substitution

/-!
# Mathematical continuation substitution

A label replacement is a region under one argument binder and the surrounding
captured values. Substitution instantiates that argument syntactically. Its
semantic use requires pure branch arguments: an effectful argument might be
duplicated or discarded. Compilers can first bind a computation and branch on
the resulting variable.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {τ : Type v}
open Silmaril.DeBruijn

namespace Tm

/-- Extend a substitution by its newest variable. -/
def consSubst (a : Tm Φ) (σ : Nat → Tm Φ) : Nat → Tm Φ
  | 0 => a
  | i + 1 => σ i

/-- Instantiate the newest variable and leave the older variables unchanged. -/
abbrev singleSubst (a : Tm Φ) : Nat → Tm Φ := consSubst a var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem Subst.HasType.cons {Γ Δ : VCtx τ} {σ : Nat → Tm Φ} {a : Tm Φ} {A : τ}
    (hσ : Subst.HasType Γ Δ σ) (ha : Tm.HasType Δ a A) :
    Subst.HasType (A :: Γ) Δ (consSubst a σ) := by
  intro i B hi
  cases i with
  | zero =>
      have h : A = B := Option.some.inj hi
      subst B
      exact ha
  | succ i => exact hσ hi

theorem Subst.HasType.single {Γ : VCtx τ} {a : Tm Φ} {A : τ} (ha : Tm.HasType Γ a A) :
    Subst.HasType (A :: Γ) Γ (singleSubst a) := (Subst.HasType.id Γ).cons ha

end Tm

namespace Region

/-- Identity continuation: pass its argument to the corresponding label. -/
def labelId (ℓ : Nat) : Region Φ := .br ℓ (.var 0)

/-- Lift captured values past a new value binder, keeping the argument at zero. -/
def liftLSubstVars (σ : Nat → Region Φ) (ℓ : Nat) : Region Φ :=
  (σ ℓ).renameVars (lift Nat.succ)

/-- Preserve a new local label and shift the old label replacements. -/
def liftLSubst (σ : Nat → Region Φ) : Nat → Region Φ
  | 0 => labelId 0
  | ℓ + 1 => (σ ℓ).renameLabels Nat.succ

/-- Lift label replacements past a prefix of local labels. -/
def liftLSubstN : Nat → (Nat → Region Φ) → Nat → Region Φ
  | 0, σ => σ
  | n + 1, σ => liftLSubst (liftLSubstN n σ)

/-- Simultaneously replace free labels by regions under one argument binder. -/
def lsubst (σ : Nat → Region Φ) : Region Φ → Region Φ
  | .br ℓ a => (σ ℓ).substVars (Tm.singleSubst a)
  | .case a l r => .case a (l.lsubst (liftLSubstVars σ)) (r.lsubst (liftLSubstVars σ))
  | .let₁ a r => .let₁ a (r.lsubst (liftLSubstVars σ))
  | .let₂ a r => .let₂ a (r.lsubst (liftLSubstVars (liftLSubstVars σ)))
  | .cfg e n bs => .cfg (e.lsubst (liftLSubstN n σ)) n
      (fun i => (bs i).lsubst (liftLSubstVars (liftLSubstN n σ)))

@[simp] theorem liftLSubstVars_labelId : liftLSubstVars (labelId : Nat → Region Φ) = labelId := rfl

@[simp] theorem liftLSubst_labelId : liftLSubst (labelId : Nat → Region Φ) = labelId := by
  funext ℓ
  cases ℓ <;> rfl

@[simp] theorem liftLSubstN_labelId (n : Nat) :
    liftLSubstN n (labelId : Nat → Region Φ) = labelId := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, ih, liftLSubst_labelId]

@[simp] theorem lsubst_labelId (r : Region Φ) : r.lsubst labelId = r := by
  induction r <;> simp_all [lsubst, labelId, substVars, Tm.subst, Tm.consSubst]

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

/-- A typed continuation substitution changes the label context while retaining
captured values. Each replacement has the source label's argument type. -/
def LSubst.HasType (Γ : VCtx τ) (L K : LCtx τ) (σ : Nat → Region Φ) : Prop :=
  ∀ ⦃ℓ A⦄, At L ℓ A → Region.HasType (A :: Γ) (σ ℓ) K

namespace LSubst.HasType

theorem id (Γ : VCtx τ) (L : LCtx τ) : HasType (Φ := Φ) Γ L L labelId := by
  intro ℓ A h
  exact .br h (.var rfl)

theorem liftVars {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : HasType Γ L K σ) (B : τ) : HasType (B :: Γ) L K (liftLSubstVars σ) := by
  intro ℓ A h
  exact (hσ h).renameVars ((SSA.Ren.wk Γ B).lift A)

theorem lift {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : HasType Γ L K σ) (B : τ) : HasType Γ (B :: L) (B :: K) (liftLSubst σ) := by
  intro ℓ A h
  cases ℓ with
  | zero =>
      have hBA : B = A := Option.some.inj h
      subst A
      exact .br rfl (.var rfl)
  | succ ℓ => exact (hσ h).renameLabels (SSA.Ren.wk K B)

theorem append {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : HasType Γ L K σ) (Ξ : LCtx τ) :
    HasType Γ (Ξ ++ L) (Ξ ++ K) (liftLSubstN Ξ.length σ) := by
  induction Ξ with
  | nil => exact hσ
  | cons A Ξ ih => exact ih.lift A

end LSubst.HasType

/-- Continuation substitution preserves exact region typing. -/
theorem HasType.lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) (hr : HasType Γ r L) :
    HasType Γ (r.lsubst σ) K := by
  induction hr generalizing K σ with
  | br hl ha => exact (hσ hl).substVars (Tm.Subst.HasType.single ha)
  | case he hl hr ihl ihr => exact .case he (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | let₁ ha hr ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha hr ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | cfg R he hb ihe ihb =>
      have hlabels := hσ.append (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      exact .cfg R (ihe hlabels) (fun i => ihb i (hlabels.liftVars _))

end Region
end Silmaril.Isotope.LambdaSSA
