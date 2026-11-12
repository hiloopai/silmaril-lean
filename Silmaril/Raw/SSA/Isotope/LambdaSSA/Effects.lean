module

public import Silmaril.Raw.SSA.Isotope.Foundations.Effects
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Fin

/-!
# SSA effect bounds

Expression effects are joins of primitive annotations. A CFG evaluates its
entry once and may repeat its blocks; the block bound therefore uses the
iteration closure. These syntax-directed bounds can overapproximate unreachable
blocks and are independent of exact typing.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {ε : Type v} [SemilatticeSup ε] [OrderBot ε] [HasEff Φ ε]

def Tm.effect : Tm Φ → ε
  | .var _ | .unit => ⊥
  | .op f a => instrEff f ⊔ a.effect
  | .let₁ a b | .pair a b | .let₂ a b => a.effect ⊔ b.effect
  | .inl a | .inr a | .abort a => a.effect
  | .case a l r => a.effect ⊔ (l.effect ⊔ r.effect)

def Tm.HasEffect (t : Tm Φ) (e : ε) : Prop := t.effect ≤ e

theorem Tm.HasEffect.mono {t : Tm Φ} {e e' : ε} (h : t.HasEffect e) (he : e ≤ e') :
    t.HasEffect e' := h.trans he

theorem Tm.HasEffect.top [OrderTop ε] (t : Tm Φ) : t.HasEffect (⊤ : ε) := le_top

@[simp] theorem Tm.effect_rename (ρ : Nat → Nat) (t : Tm Φ) :
    (t.rename ρ).effect = (t.effect : ε) := by
  induction t generalizing ρ <;> simp_all [Tm.rename, Tm.effect]

theorem Tm.Pure.effect_eq_bot {t : Tm Φ} (h : t.Pure (⊥ : ε)) : t.effect = (⊥ : ε) := by
  induction h <;> simp_all [Tm.effect, IsPure]

theorem Tm.Pure.hasEffect {t : Tm Φ} (h : t.Pure (⊥ : ε)) : t.HasEffect (⊥ : ε) :=
  le_of_eq h.effect_eq_bot

theorem Tm.pure_of_hasEffect_bot {t : Tm Φ} (h : t.HasEffect (⊥ : ε)) : t.Pure (⊥ : ε) := by
  induction t with
  | var => exact .var
  | unit => exact .unit
  | op f a ih =>
      obtain ⟨hf, ha⟩ := sup_le_iff.mp h
      exact .op (le_bot_iff.mp hf) (ih ha)
  | let₁ a b iha ihb => exact .let₁ (iha (sup_le_iff.mp h).1) (ihb (sup_le_iff.mp h).2)
  | pair a b iha ihb => exact .pair (iha (sup_le_iff.mp h).1) (ihb (sup_le_iff.mp h).2)
  | let₂ a b iha ihb => exact .let₂ (iha (sup_le_iff.mp h).1) (ihb (sup_le_iff.mp h).2)
  | inl a ih => exact .inl (ih h)
  | inr a ih => exact .inr (ih h)
  | abort a ih => exact .abort (ih h)
  | case a l r iha ihl ihr =>
      obtain ⟨ha, hlr⟩ := sup_le_iff.mp h
      exact .case (iha ha) (ihl (sup_le_iff.mp hlr).1) (ihr (sup_le_iff.mp hlr).2)

theorem Tm.pure_iff_hasEffect_bot (t : Tm Φ) : t.Pure (⊥ : ε) ↔ t.HasEffect (⊥ : ε) :=
  ⟨Tm.Pure.hasEffect, Tm.pure_of_hasEffect_bot⟩

theorem Tm.HasEffect.subst {t : Tm Φ} {e : ε} (h : t.HasEffect e)
    {σ : Nat → Tm Φ} (hσ : ∀ i, (σ i).HasEffect e) : (t.subst σ).HasEffect e := by
  have hup : ∀ {σ : Nat → Tm Φ}, (∀ i, (σ i).HasEffect e) →
      ∀ i, (Tm.liftSubst σ i).HasEffect e := by
    intro σ hσ i
    cases i with
    | zero => exact bot_le
    | succ i => simpa only [Tm.liftSubst, Tm.HasEffect, Tm.effect_rename] using hσ i
  induction t generalizing σ with
  | var i => exact hσ i
  | unit => exact bot_le
  | op f a ih => exact sup_le (sup_le_iff.mp h).1 (ih (sup_le_iff.mp h).2 hσ)
  | let₁ a b iha ihb =>
      exact sup_le (iha (sup_le_iff.mp h).1 hσ) (ihb (sup_le_iff.mp h).2 (hup hσ))
  | pair a b iha ihb =>
      exact sup_le (iha (sup_le_iff.mp h).1 hσ) (ihb (sup_le_iff.mp h).2 hσ)
  | let₂ a b iha ihb =>
      exact sup_le (iha (sup_le_iff.mp h).1 hσ) (ihb (sup_le_iff.mp h).2 (hup (hup hσ)))
  | inl a ih => exact ih h hσ
  | inr a ih => exact ih h hσ
  | abort a ih => exact ih h hσ
  | case a l r iha ihl ihr =>
      obtain ⟨ha, hlr⟩ := sup_le_iff.mp h
      exact sup_le (iha ha hσ)
        (sup_le (ihl (sup_le_iff.mp hlr).1 (hup hσ)) (ihr (sup_le_iff.mp hlr).2 (hup hσ)))

def Terminator.effect : Terminator Φ → ε
  | .br _ a => a.effect
  | .case a l r => a.effect ⊔ (l.effect ⊔ r.effect)

def Body.effect : Body Φ → ε
  | .nil => ⊥
  | .let₁ a b | .let₂ a b => a.effect ⊔ b.effect

def Block.effect (b : Block Φ) : ε := b.body.effect ⊔ b.terminator.effect

variable [EffectIteration ε]

def Region.effect : Region Φ → ε
  | .br _ a => a.effect
  | .case a l r => a.effect ⊔ (l.effect ⊔ r.effect)
  | .let₁ a r | .let₂ a r => a.effect ⊔ r.effect
  | .cfg entry _ blocks => entry.effect ⊔ iterEffect (Finset.univ.sup fun i => (blocks i).effect)

def Region.HasEffect (r : Region Φ) (e : ε) : Prop := r.effect ≤ e

theorem Region.HasEffect.mono {r : Region Φ} {e e' : ε} (h : r.HasEffect e) (he : e ≤ e') :
    r.HasEffect e' := h.trans he

theorem Region.HasEffect.top [OrderTop ε] (r : Region Φ) : r.HasEffect (⊤ : ε) := le_top

theorem Region.HasEffect.cfg {entry : Region Φ} {n : Nat} {blocks : Fin n → Region Φ}
    {e : ε} (he : IsIterative e) (hentry : entry.HasEffect e)
    (hblocks : ∀ i, (blocks i).HasEffect e) : (Region.cfg entry n blocks).HasEffect e :=
  sup_le hentry (he.iterEffect_le (Finset.sup_le fun i _ => hblocks i))

@[simp] theorem Region.effect_renameVars (ρ : Nat → Nat) (r : Region Φ) :
    (r.renameVars ρ).effect = (r.effect : ε) := by
  induction r generalizing ρ <;> simp_all [Region.renameVars, Region.effect, Tm.effect_rename]

@[simp] theorem Region.effect_renameLabels (ρ : Nat → Nat) (r : Region Φ) :
    (r.renameLabels ρ).effect = (r.effect : ε) := by
  induction r generalizing ρ <;> simp_all [Region.renameLabels, Region.effect]

theorem Region.HasEffect.renameVars {r : Region Φ} {e : ε} (h : r.HasEffect e) (ρ : Nat → Nat) :
    (r.renameVars ρ).HasEffect e := by simpa only [HasEffect, effect_renameVars] using h

theorem Region.HasEffect.renameLabels {r : Region Φ} {e : ε} (h : r.HasEffect e) (ρ : Nat → Nat) :
    (r.renameLabels ρ).HasEffect e := by simpa only [HasEffect, effect_renameLabels] using h

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ]

def Tm.HasTypeEffect (Γ : VCtx τ) (t : Tm Φ) (A : τ) (e : ε) : Prop :=
  t.HasType Γ A ∧ t.HasEffect e

def Region.HasTypeEffect (Γ : VCtx τ) (r : Region Φ) (L : LCtx τ) (e : ε) : Prop :=
  r.HasType Γ L ∧ r.HasEffect e

theorem Region.HasType.hasTypeEffect_top [OrderTop ε] {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : r.HasType Γ L) : r.HasTypeEffect Γ L (⊤ : ε) := ⟨h, .top r⟩

end Silmaril.Isotope.LambdaSSA
