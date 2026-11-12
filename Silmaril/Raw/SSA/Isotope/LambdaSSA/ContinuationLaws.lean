module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation

/-! # Algebra of value and continuation substitution -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {τ : Type v}
open Silmaril.DeBruijn

namespace Tm

theorem singleSubst_comp (a : Tm Φ) (θ : Nat → Tm Φ) :
    (fun i => (singleSubst a i).subst θ) =
      fun i => (liftSubst θ i).subst (singleSubst (a.subst θ)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [singleSubst, consSubst, liftSubst, subst_rename, Function.comp_def, subst]

theorem liftSubst_comp_lift_succ (θ : Nat → Tm Φ) :
    liftSubst (liftSubst θ) ∘ lift Nat.succ =
      fun i => (liftSubst θ i).rename (lift Nat.succ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [Function.comp_apply, lift, liftSubst, rename_comp]; rfl

end Tm

namespace Region

/-- Substitute the captured values of every continuation, preserving its argument. -/
def mapLSubstVars (θ : Nat → Tm Φ) (σ : Nat → Region Φ) (ℓ : Nat) : Region Φ :=
  (σ ℓ).substVars (Tm.liftSubst θ)

@[simp] theorem mapLSubstVars_var (σ : Nat → Region Φ) : mapLSubstVars Tm.var σ = σ := by
  funext ℓ
  simp [mapLSubstVars]

theorem mapLSubstVars_comp (σ : Nat → Region Φ) (θ υ : Nat → Tm Φ) :
    mapLSubstVars υ (mapLSubstVars θ σ) = mapLSubstVars (fun i => (θ i).subst υ) σ := by
  funext ℓ
  simp [mapLSubstVars, substVars_comp, Tm.liftSubst_comp]

theorem mapLSubstVars_liftVars (σ : Nat → Region Φ) (θ : Nat → Tm Φ) :
    mapLSubstVars (Tm.liftSubst θ) (liftLSubstVars σ) =
      liftLSubstVars (mapLSubstVars θ σ) := by
  funext ℓ
  simp only [mapLSubstVars, liftLSubstVars, substVars_renameVars,
    renameVars_substVars, Tm.liftSubst_comp_lift_succ]

theorem mapLSubstVars_lift (σ : Nat → Region Φ) (θ : Nat → Tm Φ) :
    mapLSubstVars θ (liftLSubst σ) = liftLSubst (mapLSubstVars θ σ) := by
  funext ℓ
  cases ℓ <;> simp [mapLSubstVars, liftLSubst, labelId, substVars, Tm.subst,
    Tm.liftSubst, substVars_renameLabels]

theorem mapLSubstVars_liftN (n : Nat) (σ : Nat → Region Φ) (θ : Nat → Tm Φ) :
    mapLSubstVars θ (liftLSubstN n σ) = liftLSubstN n (mapLSubstVars θ σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, mapLSubstVars_lift, ih]

/-- Value substitution acts on both a region and the values captured by its
replacement continuations. -/
theorem substVars_lsubst (r : Region Φ) (σ : Nat → Region Φ) (θ : Nat → Tm Φ) :
    (r.lsubst σ).substVars θ = (r.substVars θ).lsubst (mapLSubstVars θ σ) := by
  induction r generalizing σ θ with
  | br ℓ a => simp only [lsubst, substVars, mapLSubstVars, substVars_comp, Tm.singleSubst_comp]
  | case a l r ihl ihr =>
      simp only [lsubst, substVars, ihl, ihr, mapLSubstVars_liftVars]
  | let₁ a r ih => simp only [lsubst, substVars, ih, mapLSubstVars_liftVars]
  | let₂ a r ih =>
      simp only [lsubst, substVars, ih, Tm.liftSubstN, mapLSubstVars_liftVars]
  | cfg e n bs ihe ihbs =>
      simp only [lsubst, substVars, ihe, ihbs, mapLSubstVars_liftVars, mapLSubstVars_liftN]

/-- Rename the exits of all replacement continuations. -/
def mapLSubstLabels (ρ : Nat → Nat) (σ : Nat → Region Φ) (ℓ : Nat) : Region Φ :=
  (σ ℓ).renameLabels ρ

theorem liftLSubst_comp_rename (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    liftLSubst (σ ∘ ρ) = liftLSubst σ ∘ lift ρ := by
  funext ℓ
  cases ℓ <;> rfl

theorem liftLSubstN_comp_rename (n : Nat) (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    liftLSubstN n (σ ∘ ρ) = liftLSubstN n σ ∘ liftN n ρ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, liftN, ih, liftLSubst_comp_rename]

theorem liftLSubstVars_comp_rename (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    liftLSubstVars (σ ∘ ρ) = liftLSubstVars σ ∘ ρ := rfl

theorem lsubst_renameLabels (r : Region Φ) (ρ : Nat → Nat) (σ : Nat → Region Φ) :
    (r.renameLabels ρ).lsubst σ = r.lsubst (σ ∘ ρ) := by
  induction r generalizing ρ σ <;>
    simp_all only [renameLabels, lsubst, liftLSubstN_comp_rename, liftLSubstVars_comp_rename]
  rfl

theorem mapLSubstLabels_liftVars (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    mapLSubstLabels ρ (liftLSubstVars σ) = liftLSubstVars (mapLSubstLabels ρ σ) := by
  funext ℓ
  simp only [mapLSubstLabels, liftLSubstVars, renameVars_renameLabels]

theorem mapLSubstLabels_lift (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    mapLSubstLabels (lift ρ) (liftLSubst σ) = liftLSubst (mapLSubstLabels ρ σ) := by
  funext ℓ
  cases ℓ with
  | zero => rfl
  | succ ℓ => simp only [mapLSubstLabels, liftLSubst, renameLabels_comp]; rfl

theorem mapLSubstLabels_liftN (n : Nat) (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    mapLSubstLabels (liftN n ρ) (liftLSubstN n σ) = liftLSubstN n (mapLSubstLabels ρ σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, liftN, mapLSubstLabels_lift, ih]

theorem renameLabels_lsubst (r : Region Φ) (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    (r.lsubst σ).renameLabels ρ = r.lsubst (mapLSubstLabels ρ σ) := by
  induction r generalizing ρ σ with
  | br ℓ a => simp only [lsubst, mapLSubstLabels, substVars_renameLabels]
  | case a l r ihl ihr =>
      simp only [lsubst, renameLabels, ihl, ihr, mapLSubstLabels_liftVars]
  | let₁ a r ih => simp only [lsubst, renameLabels, ih, mapLSubstLabels_liftVars]
  | let₂ a r ih => simp only [lsubst, renameLabels, ih, mapLSubstLabels_liftVars]
  | cfg e n bs ihe ihbs =>
      simp only [lsubst, renameLabels, ihe, ihbs, mapLSubstLabels_liftVars, mapLSubstLabels_liftN]

theorem mapLSubstVars_rename (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    mapLSubstVars (Tm.var ∘ ρ) σ = fun ℓ => (σ ℓ).renameVars (lift ρ) := by
  funext ℓ
  simp only [mapLSubstVars, Tm.liftSubst_comp_rename, Tm.liftSubst_var,
    ← renameVars_eq_substVars]

theorem renameVars_lsubst (r : Region Φ) (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    (r.lsubst σ).renameVars ρ =
      (r.renameVars ρ).lsubst (fun ℓ => (σ ℓ).renameVars (lift ρ)) := by
  simpa only [mapLSubstVars_rename, ← renameVars_eq_substVars] using substVars_lsubst r σ (Tm.var ∘ ρ)

@[simp] theorem mapLSubstVars_single_liftVars (a : Tm Φ) (σ : Nat → Region Φ) :
    mapLSubstVars (Tm.singleSubst a) (liftLSubstVars σ) = σ := by
  have h : Tm.liftSubst (Tm.singleSubst a) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  funext ℓ
  simp only [mapLSubstVars, liftLSubstVars, substVars_renameVars, h, substVars_var]

theorem lsubst_single (r : Region Φ) (a : Tm Φ) (σ : Nat → Region Φ) :
    (r.substVars (Tm.singleSubst a)).lsubst σ =
      (r.lsubst (liftLSubstVars σ)).substVars (Tm.singleSubst a) := by
  simpa only [mapLSubstVars_single_liftVars] using
    (substVars_lsubst r (liftLSubstVars σ) (Tm.singleSubst a)).symm

/-- Compose label replacements, retaining the first continuation's argument
as a captured value while applying the second substitution. -/
def compLSubst (σ υ : Nat → Region Φ) (ℓ : Nat) : Region Φ :=
  (σ ℓ).lsubst (liftLSubstVars υ)

theorem compLSubst_liftVars (σ υ : Nat → Region Φ) :
    compLSubst (liftLSubstVars σ) (liftLSubstVars υ) =
      liftLSubstVars (compLSubst σ υ) := by
  funext ℓ
  simp only [compLSubst, liftLSubstVars, renameVars_lsubst]
  congr 1
  funext i
  simp only [liftLSubstVars, renameVars_comp]
  congr 1
  funext j
  cases j <;> rfl

theorem compLSubst_lift (σ υ : Nat → Region Φ) :
    compLSubst (liftLSubst σ) (liftLSubst υ) = liftLSubst (compLSubst σ υ) := by
  funext ℓ
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
      simp only [compLSubst, liftLSubst, lsubst_renameLabels, renameLabels_lsubst]
      congr 1
      funext i
      simp only [Function.comp_apply, liftLSubstVars, liftLSubst,
        mapLSubstLabels, renameVars_renameLabels]

theorem compLSubst_liftN (n : Nat) (σ υ : Nat → Region Φ) :
    compLSubst (liftLSubstN n σ) (liftLSubstN n υ) = liftLSubstN n (compLSubst σ υ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, compLSubst_lift, ih]

/-- Continuation substitution is associative, with capture-avoiding composition. -/
theorem lsubst_comp (r : Region Φ) (σ υ : Nat → Region Φ) :
    (r.lsubst σ).lsubst υ = r.lsubst (compLSubst σ υ) := by
  induction r generalizing σ υ with
  | br ℓ a => exact lsubst_single (σ ℓ) a υ
  | case a l r ihl ihr =>
      simp only [lsubst, ihl, ihr, compLSubst_liftVars]
  | let₁ a r ih => simp only [lsubst, ih, compLSubst_liftVars]
  | let₂ a r ih => simp only [lsubst, ih, compLSubst_liftVars]
  | cfg e n bs ihe ihbs =>
      simp only [lsubst, ihe, ihbs, compLSubst_liftVars, compLSubst_liftN]

@[simp] theorem compLSubst_id_right (σ : Nat → Region Φ) : compLSubst σ labelId = σ := by
  funext ℓ
  simp [compLSubst]

@[simp] theorem compLSubst_id_left (σ : Nat → Region Φ) : compLSubst labelId σ = σ := by
  have h : Tm.singleSubst (Tm.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  funext ℓ
  change ((σ ℓ).renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = σ ℓ
  simp only [substVars_renameVars, h, substVars_var]

theorem compLSubst_assoc (σ υ ω : Nat → Region Φ) :
    compLSubst (compLSubst σ υ) ω = compLSubst σ (compLSubst υ ω) := by
  funext ℓ
  change ((σ ℓ).lsubst (liftLSubstVars υ)).lsubst (liftLSubstVars ω) =
    (σ ℓ).lsubst (liftLSubstVars (compLSubst υ ω))
  rw [lsubst_comp, compLSubst_liftVars]

theorem renameLabels_eq_lsubst (r : Region Φ) (ρ : Nat → Nat) :
    r.renameLabels ρ = r.lsubst (labelId ∘ ρ) := by
  simpa only [lsubst_labelId] using lsubst_renameLabels r ρ labelId

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

namespace LSubst.HasType

theorem mapVars {Γ Δ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {θ : Nat → Tm Φ} (hσ : HasType Γ L K σ) (hθ : Tm.Subst.HasType Γ Δ θ) :
    HasType Δ L K (mapLSubstVars θ σ) := by
  intro ℓ A h
  exact (hσ h).substVars (hθ.lift A)

theorem mapLabels {Γ : VCtx τ} {L K J : LCtx τ} {σ : Nat → Region Φ}
    {ρ : Nat → Nat} (hσ : HasType Γ L K σ) (hρ : Ren K J ρ) :
    HasType Γ L J (mapLSubstLabels ρ σ) := by
  intro ℓ A h
  exact (hσ h).renameLabels hρ

theorem comp {Γ : VCtx τ} {L K J : LCtx τ} {σ υ : Nat → Region Φ}
    (hσ : HasType Γ L K σ) (hυ : HasType Γ K J υ) :
    HasType Γ L J (compLSubst σ υ) := by
  intro ℓ A h
  exact (hσ h).lsubst (hυ.liftVars A)

end LSubst.HasType

end Region
end Silmaril.Isotope.LambdaSSA
