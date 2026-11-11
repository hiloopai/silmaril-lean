module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-!
# Lambda-SSA typing: structural laws

Renaming of value variables and labels preserves typing; terms are also closed
under weakening and typed simultaneous substitution. The renaming functions
compose and have the identity as unit.
-/

@[expose] public section

/-!
# SSA structural metatheory
-/


universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {τ : Type v}

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

namespace Tm

@[simp] theorem rename_id (a : Tm Φ) : a.rename id = a := by
  induction a <;> simp [rename, *]

/-- Typing is stable under type-preserving renaming. -/
theorem HasType.rename {Γ Δ : VCtx τ} {a : Tm Φ} {A : τ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (ha : HasType Γ a A) : HasType Δ (a.rename ρ) A := by
  induction ha generalizing Δ ρ with
  | var h => exact .var (hρ h)
  | op ha ih => exact .op (ih hρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hρ) (ihb (hρ.lift _))
  | pair ha hb iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ ha hb iha ihb =>
      exact .let₂ (iha hρ) (ihb ((hρ.lift _).lift _))
  | inl ha ih => exact .inl (ih hρ)
  | inr hb ih => exact .inr (ih hρ)
  | case ha hl hr iha ihl ihr =>
      exact .case (iha hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))
  | abort ha ih => exact .abort (ih hρ)

theorem HasType.weaken {Γ : VCtx τ} {a : Tm Φ} {A : τ} (B : τ)
    (ha : HasType Γ a A) : HasType (B :: Γ) (a.rename Nat.succ) A :=
  ha.rename (Ren.wk Γ B)

/-- Typing criterion for simultaneous substitutions. -/
def Subst.HasType (Γ Δ : VCtx τ) (σ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → Tm.HasType Δ (σ i) A

namespace Subst.HasType

theorem lift {Γ Δ : VCtx τ} {σ : Nat → Tm Φ} (hσ : Subst.HasType Γ Δ σ) (A : τ) :
    Subst.HasType (A :: Γ) (A :: Δ) (Tm.liftSubst σ) := by
  intro i B hi
  cases i with
  | zero => exact .var (by simpa [At] using hi)
  | succ i =>
      exact (hσ (by simpa [At] using hi)).weaken A

end Subst.HasType

/-- Typing is stable under simultaneous substitution. -/
theorem HasType.subst {Γ Δ : VCtx τ} {a : Tm Φ} {A : τ} {σ : Nat → Tm Φ}
    (hσ : Subst.HasType Γ Δ σ) (ha : HasType Γ a A) : HasType Δ (a.subst σ) A := by
  induction ha generalizing Δ σ with
  | var h => exact hσ h
  | op ha ih => exact .op (ih hσ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hσ) (ihb (hσ.lift _))
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | unit => exact .unit
  | let₂ ha hb iha ihb => exact .let₂ (iha hσ) (ihb ((hσ.lift _).lift _))
  | inl ha ih => exact .inl (ih hσ)
  | inr hb ih => exact .inr (ih hσ)
  | case ha hl hr iha ihl ihr =>
      exact .case (iha hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))
  | abort ha ih => exact .abort (ih hσ)

end Tm

namespace Terminator

theorem HasType.renameVars {Γ Δ : VCtx τ} {t : Terminator Φ} {L : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) (ht : HasType Γ t L) :
    HasType Δ (t.renameVars ρ) L := by
  induction ht generalizing Δ ρ with
  | br hL ha => exact .br hL (ha.rename hρ)
  | case ha hl hr ihl ihr =>
      exact .case (ha.rename hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))

theorem HasType.renameLabels {Γ : VCtx τ} {t : Terminator Φ} {L K : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren L K ρ) (ht : HasType Γ t L) :
    HasType Γ (t.renameLabels ρ) K := by
  induction ht with
  | br hL ha => exact .br (hρ hL) ha
  | case ha hl hr ihl ihr => exact .case ha (ihl hρ) (ihr hρ)

end Terminator

end Silmaril.Isotope.LambdaSSA

end

@[expose] public section

/-! # Structural laws for lambda-SSA regions -/



namespace Silmaril.Isotope.LambdaSSA

universe u v
variable {Φ : Type u} {τ : Type v}
open Silmaril.DeBruijn


namespace Tm

theorem rename_comp (a : Tm Φ) (ρ σ : Nat → Nat) :
    (a.rename ρ).rename σ = a.rename (σ ∘ ρ) := by
  induction a generalizing ρ σ <;> simp_all [rename, lift_comp, liftN_comp]

end Tm

namespace Body

@[simp] theorem bound_rename (b : Body Φ) (ρ : Nat → Nat) :
    (b.rename ρ).bound = b.bound := by
  induction b generalizing ρ <;> simp_all [rename, bound]

@[simp] theorem rename_id (b : Body Φ) : b.rename id = b := by
  induction b <;> simp_all [rename]

theorem rename_comp (b : Body Φ) (ρ σ : Nat → Nat) :
    (b.rename ρ).rename σ = b.rename (σ ∘ ρ) := by
  induction b generalizing ρ σ <;> simp_all [rename, Tm.rename_comp, lift_comp, liftN_comp]

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

/-- Renaming a body also renames the context exposed to its terminator. -/
theorem HasType.rename {Γ Δ Θ : VCtx τ} {b : Body Φ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (hb : HasType Γ b Θ) :
    ∃ Θ', HasType Δ (b.rename ρ) Θ' ∧ Ren Θ Θ' (liftN b.bound ρ) := by
  induction hb generalizing Δ ρ with
  | nil => exact ⟨Δ, .nil, hρ⟩
  | let₁ ha hb ih =>
      obtain ⟨Θ', hb', hw⟩ := ih (hρ.lift _)
      refine ⟨Θ', .let₁ (ha.rename hρ) hb', ?_⟩
      simpa only [bound, liftN, liftN_lift] using hw
  | let₂ ha hb ih =>
      obtain ⟨Θ', hb', hw⟩ := ih ((hρ.lift _).lift _)
      refine ⟨Θ', .let₂ (ha.rename hρ) hb', ?_⟩
      simpa only [bound, liftN, liftN_lift] using hw

end Body

namespace Terminator

@[simp] theorem renameVars_id (t : Terminator Φ) : t.renameVars id = t := by
  induction t <;> simp_all [renameVars]

@[simp] theorem renameLabels_id (t : Terminator Φ) : t.renameLabels id = t := by
  induction t <;> simp_all [renameLabels]

theorem renameVars_comp (t : Terminator Φ) (ρ σ : Nat → Nat) :
    (t.renameVars ρ).renameVars σ = t.renameVars (σ ∘ ρ) := by
  induction t generalizing ρ σ <;> simp_all [renameVars, Tm.rename_comp, lift_comp]

theorem renameLabels_comp (t : Terminator Φ) (ρ σ : Nat → Nat) :
    (t.renameLabels ρ).renameLabels σ = t.renameLabels (σ ∘ ρ) := by
  induction t <;> simp_all [renameLabels]

theorem renameVars_renameLabels (t : Terminator Φ) (ρ σ : Nat → Nat) :
    (t.renameLabels σ).renameVars ρ = (t.renameVars ρ).renameLabels σ := by
  induction t generalizing ρ <;> simp_all [renameVars, renameLabels]

end Terminator

namespace Block

@[simp] theorem renameVars_id (b : Block Φ) : b.renameVars id = b := by
  cases b
  simp [renameVars]

@[simp] theorem renameLabels_id (b : Block Φ) : b.renameLabels id = b := by
  cases b
  simp [renameLabels]

theorem renameVars_comp (b : Block Φ) (ρ σ : Nat → Nat) :
    (b.renameVars ρ).renameVars σ = b.renameVars (σ ∘ ρ) := by
  simp [renameVars, Body.rename_comp, Terminator.renameVars_comp, liftN_comp]

theorem renameLabels_comp (b : Block Φ) (ρ σ : Nat → Nat) :
    (b.renameLabels ρ).renameLabels σ = b.renameLabels (σ ∘ ρ) := by
  simp [renameLabels, Terminator.renameLabels_comp]

theorem renameVars_renameLabels (b : Block Φ) (ρ σ : Nat → Nat) :
    (b.renameLabels σ).renameVars ρ = (b.renameVars ρ).renameLabels σ := by
  simp [renameVars, renameLabels, Terminator.renameVars_renameLabels]

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {b : Block Φ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (hb : HasType Γ b L) : HasType Δ (b.renameVars ρ) L := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  obtain ⟨Θ', hbody', hw⟩ := hbody.rename hρ
  exact ⟨Θ', hbody', hterm.renameVars hw⟩

theorem HasType.renameLabels {Γ : VCtx τ} {L K : LCtx τ} {b : Block Φ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) (hb : HasType Γ b L) : HasType Γ (b.renameLabels ρ) K := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  exact ⟨Θ, hbody, hterm.renameLabels hρ⟩

end Block

namespace Region

@[simp] theorem renameVars_id (r : Region Φ) : r.renameVars id = r := by
  induction r <;> simp_all [renameVars]

@[simp] theorem renameLabels_id (r : Region Φ) : r.renameLabels id = r := by
  induction r <;> simp_all [renameLabels]

theorem renameVars_comp (r : Region Φ) (ρ σ : Nat → Nat) :
    (r.renameVars ρ).renameVars σ = r.renameVars (σ ∘ ρ) := by
  induction r generalizing ρ σ <;> simp_all [renameVars, Tm.rename_comp, lift_comp, liftN_comp]

theorem renameLabels_comp (r : Region Φ) (ρ σ : Nat → Nat) :
    (r.renameLabels ρ).renameLabels σ = r.renameLabels (σ ∘ ρ) := by
  induction r generalizing ρ σ <;> simp_all [renameLabels, liftN_comp]

theorem renameVars_renameLabels (r : Region Φ) (ρ σ : Nat → Nat) :
    (r.renameLabels σ).renameVars ρ = (r.renameVars ρ).renameLabels σ := by
  induction r generalizing ρ σ <;> simp_all [renameVars, renameLabels]

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (hr : HasType Γ r L) : HasType Δ (r.renameVars ρ) L := by
  induction hr generalizing Δ ρ with
  | br hl ha => exact .br hl (ha.rename hρ)
  | case he hl hr ihl ihr => exact .case (he.rename hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))
  | let₁ ha hr ih => exact .let₁ (ha.rename hρ) (ih (hρ.lift _))
  | let₂ ha hr ih => exact .let₂ (ha.rename hρ) (ih ((hρ.lift _).lift _))
  | cfg R he hb ihe ihb => exact .cfg R (ihe hρ) (fun i => ihb i (hρ.lift _))

theorem HasType.renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) (hr : HasType Γ r L) : HasType Γ (r.renameLabels ρ) K := by
  induction hr generalizing K ρ with
  | br hl ha => exact .br (hρ hl) ha
  | case he hl hr ihl ihr => exact .case he (ihl hρ) (ihr hρ)
  | let₁ ha hr ih => exact .let₁ ha (ih hρ)
  | let₂ ha hr ih => exact .let₂ ha (ih hρ)
  | cfg R he hb ihe ihb =>
      have hlabels := SSA.Ren.append hρ (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      exact .cfg R (ihe hlabels) (fun i => ihb i hlabels)

end Region

end Silmaril.Isotope.LambdaSSA

end
