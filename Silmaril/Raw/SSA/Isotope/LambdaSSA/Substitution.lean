module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-!
# Simultaneous value substitution in lambda-SSA

These are syntactic and typing laws. Substitutions may contain effects; no
semantic claim that duplicates or discards effects is made here.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {τ : Type v}

open Silmaril.DeBruijn

namespace Tm

@[simp] theorem liftSubst_var : liftSubst (var : Nat → Tm Φ) = var := by
  funext i
  cases i <;> rfl

@[simp] theorem liftSubstN_var (n : Nat) : liftSubstN n (var : Nat → Tm Φ) = var := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, ih, liftSubst_var]

@[simp] theorem subst_var (a : Tm Φ) : a.subst var = a := by
  induction a <;> simp_all [subst]

theorem liftSubst_comp_rename (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubst (σ ∘ ρ) = liftSubst σ ∘ lift ρ := by
  funext i
  cases i <;> rfl

theorem liftSubstN_comp_rename (n : Nat) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubstN n (σ ∘ ρ) = liftSubstN n σ ∘ liftN n ρ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, liftN, ih, liftSubst_comp_rename]

theorem subst_rename (a : Tm Φ) (ρ : Nat → Nat) (σ : Nat → Tm Φ) :
    (a.rename ρ).subst σ = a.subst (σ ∘ ρ) := by
  induction a generalizing ρ σ <;>
    simp_all [rename, subst, liftSubst_comp_rename, liftSubstN_comp_rename]

theorem liftSubst_rename (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubst (fun i => (σ i).rename ρ) = fun i => (liftSubst σ i).rename (lift ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [liftSubst, rename_comp]; rfl

theorem liftSubstN_rename (n : Nat) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubstN n (fun i => (σ i).rename ρ) =
      fun i => (liftSubstN n σ i).rename (liftN n ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, liftN, ih, liftSubst_rename]

theorem rename_subst (a : Tm Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (a.subst σ).rename ρ = a.subst (fun i => (σ i).rename ρ) := by
  induction a generalizing ρ σ <;>
    simp_all [rename, subst, liftSubst_rename, liftSubstN_rename]

theorem liftSubst_comp (σ υ : Nat → Tm Φ) :
    liftSubst (fun i => (σ i).subst υ) = fun i => (liftSubst σ i).subst (liftSubst υ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [liftSubst, subst_rename, rename_subst]; rfl

theorem liftSubstN_comp (n : Nat) (σ υ : Nat → Tm Φ) :
    liftSubstN n (fun i => (σ i).subst υ) =
      fun i => (liftSubstN n σ i).subst (liftSubstN n υ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, ih, liftSubst_comp]

theorem subst_comp (a : Tm Φ) (σ υ : Nat → Tm Φ) :
    (a.subst σ).subst υ = a.subst (fun i => (σ i).subst υ) := by
  induction a generalizing σ υ <;> simp_all [subst, liftSubst_comp, liftSubstN_comp]

theorem liftSubstN_liftSubst (n : Nat) (σ : Nat → Tm Φ) :
    liftSubstN n (liftSubst σ) = liftSubst (liftSubstN n σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, ih]

theorem liftSubstN_add (n m : Nat) (σ : Nat → Tm Φ) :
    liftSubstN (n + m) σ = liftSubstN n (liftSubstN m σ) := by
  induction n with
  | zero => simp only [Nat.zero_add, liftSubstN]
  | succ n ih => simp only [Nat.succ_add, liftSubstN, ih]

theorem rename_eq_subst (a : Tm Φ) (ρ : Nat → Nat) :
    a.rename ρ = a.subst (var ∘ ρ) := by
  simpa using subst_rename a ρ var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

namespace Subst.HasType

theorem id (Γ : VCtx τ) : Subst.HasType (Φ := Φ) Γ Γ var := by
  intro i A hi
  exact .var hi

theorem comp {Γ Δ Θ : VCtx τ} {σ υ : Nat → Tm Φ}
    (hσ : Subst.HasType Γ Δ σ) (hυ : Subst.HasType Δ Θ υ) :
    Subst.HasType Γ Θ (fun i => (σ i).subst υ) := by
  intro i A hi
  exact (hσ hi).subst hυ

theorem append {Γ Δ : VCtx τ} {σ : Nat → Tm Φ} (hσ : Subst.HasType Γ Δ σ)
    (Ξ : VCtx τ) : Subst.HasType (Ξ ++ Γ) (Ξ ++ Δ) (liftSubstN Ξ.length σ) := by
  induction Ξ with
  | nil => exact hσ
  | cons A Ξ ih => exact ih.lift A

end Subst.HasType
end Tm

namespace Body

/-- Substitute a body's free values, preserving each definition it binds. -/
def subst (σ : Nat → Tm Φ) : Body Φ → Body Φ
  | .nil => .nil
  | .let₁ a b => .let₁ (a.subst σ) (b.subst (Tm.liftSubst σ))
  | .let₂ a b => .let₂ (a.subst σ) (b.subst (Tm.liftSubstN 2 σ))

@[simp] theorem bound_subst (b : Body Φ) (σ : Nat → Tm Φ) :
    (b.subst σ).bound = b.bound := by
  induction b generalizing σ <;> simp_all [subst, bound]

@[simp] theorem subst_var (b : Body Φ) : b.subst Tm.var = b := by
  induction b <;> simp_all [subst]

theorem subst_rename (b : Body Φ) (ρ : Nat → Nat) (σ : Nat → Tm Φ) :
    (b.rename ρ).subst σ = b.subst (σ ∘ ρ) := by
  induction b generalizing ρ σ <;>
    simp_all [rename, subst, Tm.subst_rename,
      Tm.liftSubst_comp_rename, Tm.liftSubstN_comp_rename]

theorem rename_subst (b : Body Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (b.subst σ).rename ρ = b.subst (fun i => (σ i).rename ρ) := by
  induction b generalizing ρ σ <;>
    simp_all [rename, subst, Tm.rename_subst, Tm.liftSubst_rename, Tm.liftSubstN_rename]

theorem subst_comp (b : Body Φ) (σ υ : Nat → Tm Φ) :
    (b.subst σ).subst υ = b.subst (fun i => (σ i).subst υ) := by
  induction b generalizing σ υ <;>
    simp_all [subst, Tm.subst_comp, Tm.liftSubst_comp, Tm.liftSubstN_comp]

theorem rename_eq_subst (b : Body Φ) (ρ : Nat → Nat) :
    b.rename ρ = b.subst (Tm.var ∘ ρ) := by
  simpa using subst_rename b ρ Tm.var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

/-- Body substitution exposes the lifted substitution into its final context. -/
theorem HasType.subst {Γ Δ Θ : VCtx τ} {b : Body Φ} {σ : Nat → Tm Φ}
    (hσ : Tm.Subst.HasType Γ Δ σ) (hb : HasType Γ b Θ) :
    ∃ Θ', HasType Δ (b.subst σ) Θ' ∧
      Tm.Subst.HasType Θ Θ' (Tm.liftSubstN b.bound σ) := by
  induction hb generalizing Δ σ with
  | nil => exact ⟨Δ, .nil, hσ⟩
  | let₁ ha hb ih =>
      obtain ⟨Θ', hb', hsubst⟩ := ih (hσ.lift _)
      refine ⟨Θ', .let₁ (ha.subst hσ) hb', ?_⟩
      simpa only [bound, Tm.liftSubstN, Tm.liftSubstN_liftSubst] using hsubst
  | let₂ ha hb ih =>
      obtain ⟨Θ', hb', hsubst⟩ := ih ((hσ.lift _).lift _)
      refine ⟨Θ', .let₂ (ha.subst hσ) hb', ?_⟩
      simpa only [bound, Tm.liftSubstN, Tm.liftSubstN_liftSubst] using hsubst

end Body

namespace Terminator

/-- Substitute free values without changing branch labels. -/
def substVars (σ : Nat → Tm Φ) : Terminator Φ → Terminator Φ
  | .br ℓ a => .br ℓ (a.subst σ)
  | .case a l r =>
      .case (a.subst σ) (l.substVars (Tm.liftSubst σ)) (r.substVars (Tm.liftSubst σ))

@[simp] theorem substVars_var (t : Terminator Φ) : t.substVars Tm.var = t := by
  induction t <;> simp_all [substVars]

theorem substVars_renameVars (t : Terminator Φ) (ρ : Nat → Nat) (σ : Nat → Tm Φ) :
    (t.renameVars ρ).substVars σ = t.substVars (σ ∘ ρ) := by
  induction t generalizing ρ σ <;>
    simp_all [renameVars, substVars, Tm.subst_rename, Tm.liftSubst_comp_rename]

theorem renameVars_substVars (t : Terminator Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (t.substVars σ).renameVars ρ = t.substVars (fun i => (σ i).rename ρ) := by
  induction t generalizing ρ σ <;>
    simp_all [renameVars, substVars, Tm.rename_subst, Tm.liftSubst_rename]

theorem substVars_comp (t : Terminator Φ) (σ υ : Nat → Tm Φ) :
    (t.substVars σ).substVars υ = t.substVars (fun i => (σ i).subst υ) := by
  induction t generalizing σ υ <;>
    simp_all [substVars, Tm.subst_comp, Tm.liftSubst_comp]

theorem substVars_renameLabels (t : Terminator Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (t.renameLabels ρ).substVars σ = (t.substVars σ).renameLabels ρ := by
  induction t generalizing σ <;> simp_all [renameLabels, substVars]

theorem renameVars_eq_substVars (t : Terminator Φ) (ρ : Nat → Nat) :
    t.renameVars ρ = t.substVars (Tm.var ∘ ρ) := by
  simpa using substVars_renameVars t ρ Tm.var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {t : Terminator Φ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (ht : HasType Γ t L) :
    HasType Δ (t.substVars σ) L := by
  induction ht generalizing Δ σ with
  | br hl ha => exact .br hl (ha.subst hσ)
  | case he hl hr ihl ihr => exact .case (he.subst hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))

end Terminator

namespace Block

/-- Substitute a block's incoming values, lifting past all body definitions. -/
def substVars (σ : Nat → Tm Φ) (b : Block Φ) : Block Φ :=
  ⟨b.body.subst σ, b.terminator.substVars (Tm.liftSubstN b.body.bound σ)⟩

@[simp] theorem substVars_var (b : Block Φ) : b.substVars Tm.var = b := by
  cases b
  simp [substVars]

theorem substVars_renameVars (b : Block Φ) (ρ : Nat → Nat) (σ : Nat → Tm Φ) :
    (b.renameVars ρ).substVars σ = b.substVars (σ ∘ ρ) := by
  simp [renameVars, substVars, Body.subst_rename,
    Terminator.substVars_renameVars, Tm.liftSubstN_comp_rename]

theorem renameVars_substVars (b : Block Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (b.substVars σ).renameVars ρ = b.substVars (fun i => (σ i).rename ρ) := by
  simp [renameVars, substVars, Body.rename_subst,
    Terminator.renameVars_substVars, Tm.liftSubstN_rename]

theorem substVars_comp (b : Block Φ) (σ υ : Nat → Tm Φ) :
    (b.substVars σ).substVars υ = b.substVars (fun i => (σ i).subst υ) := by
  simp [substVars, Body.subst_comp, Terminator.substVars_comp, Tm.liftSubstN_comp]

theorem substVars_renameLabels (b : Block Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (b.renameLabels ρ).substVars σ = (b.substVars σ).renameLabels ρ := by
  simp [renameLabels, substVars, Terminator.substVars_renameLabels]

theorem renameVars_eq_substVars (b : Block Φ) (ρ : Nat → Nat) :
    b.renameVars ρ = b.substVars (Tm.var ∘ ρ) := by
  simpa using substVars_renameVars b ρ Tm.var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {b : Block Φ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (hb : HasType Γ b L) :
    HasType Δ (b.substVars σ) L := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  obtain ⟨Θ', hbody', hsubst⟩ := hbody.subst hσ
  exact ⟨Θ', hbody', hterm.substVars hsubst⟩

end Block

namespace Region

/-- Substitute free values. Each CFG block binds one fresh parameter, while
its captured values are substituted from the surrounding context. -/
def substVars (σ : Nat → Tm Φ) : Region Φ → Region Φ
  | .br ℓ a => .br ℓ (a.subst σ)
  | .case a l r =>
      .case (a.subst σ) (l.substVars (Tm.liftSubst σ)) (r.substVars (Tm.liftSubst σ))
  | .let₁ a r => .let₁ (a.subst σ) (r.substVars (Tm.liftSubst σ))
  | .let₂ a r => .let₂ (a.subst σ) (r.substVars (Tm.liftSubstN 2 σ))
  | .cfg e n bs => .cfg (e.substVars σ) n (fun i => (bs i).substVars (Tm.liftSubst σ))

@[simp] theorem substVars_var (r : Region Φ) : r.substVars Tm.var = r := by
  induction r <;> simp_all [substVars]

theorem substVars_renameVars (r : Region Φ) (ρ : Nat → Nat) (σ : Nat → Tm Φ) :
    (r.renameVars ρ).substVars σ = r.substVars (σ ∘ ρ) := by
  induction r generalizing ρ σ <;>
    simp_all [renameVars, substVars, Tm.subst_rename,
      Tm.liftSubst_comp_rename, Tm.liftSubstN_comp_rename]

theorem renameVars_substVars (r : Region Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (r.substVars σ).renameVars ρ = r.substVars (fun i => (σ i).rename ρ) := by
  induction r generalizing ρ σ <;>
    simp_all [renameVars, substVars, Tm.rename_subst,
      Tm.liftSubst_rename, Tm.liftSubstN_rename]

theorem substVars_comp (r : Region Φ) (σ υ : Nat → Tm Φ) :
    (r.substVars σ).substVars υ = r.substVars (fun i => (σ i).subst υ) := by
  induction r generalizing σ υ <;>
    simp_all [substVars, Tm.subst_comp, Tm.liftSubst_comp, Tm.liftSubstN_comp]

theorem substVars_renameLabels (r : Region Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (r.renameLabels ρ).substVars σ = (r.substVars σ).renameLabels ρ := by
  induction r generalizing σ ρ <;> simp_all [renameLabels, substVars]

theorem renameVars_eq_substVars (r : Region Φ) (ρ : Nat → Nat) :
    r.renameVars ρ = r.substVars (Tm.var ∘ ρ) := by
  simpa using substVars_renameVars r ρ Tm.var

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

theorem HasType.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (hr : HasType Γ r L) :
    HasType Δ (r.substVars σ) L := by
  induction hr generalizing Δ σ with
  | br hl ha => exact .br hl (ha.subst hσ)
  | case he hl hr ihl ihr => exact .case (he.subst hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))
  | let₁ ha hr ih => exact .let₁ (ha.subst hσ) (ih (hσ.lift _))
  | let₂ ha hr ih => exact .let₂ (ha.subst hσ) (ih ((hσ.lift _).lift _))
  | cfg R he hb ihe ihb => exact .cfg R (ihe hσ) (fun i => ihb i (hσ.lift _))

end Region

end Silmaril.Isotope.LambdaSSA
