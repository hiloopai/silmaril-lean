module

public import Silmaril.Raw.SSA.Isotope.Foundations.Effects
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Purity
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing

/-! Structural effect bounds, independent of exact typing. -/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w}
    [SemilatticeSup ε] [OrderBot ε] [HasEff Φ ε] {n m : Nat}

def Tm.effect : {n : Nat} → Tm ν Φ n → ε
  | _, .fv _ | _, .bv _ | _, .unit => ⊥
  | _, .op f a => instrEff f ⊔ a.effect
  | _, .let₁ a b | _, .pair a b | _, .let₂ a b => a.effect ⊔ b.effect
  | _, .inl a | _, .inr a | _, .abort a => a.effect
  | _, .case a l r => a.effect ⊔ (l.effect ⊔ r.effect)

def HasEffect (t : Tm ν Φ n) (e : ε) : Prop := t.effect ≤ e

theorem HasEffect.mono {t : Tm ν Φ n} {e e' : ε} (h : HasEffect t e) (he : e ≤ e') :
    HasEffect t e' := h.trans he

theorem HasEffect.top [OrderTop ε] (t : Tm ν Φ n) : HasEffect t (⊤ : ε) := le_top

theorem HasEffect.inferred (t : Tm ν Φ n) : HasEffect t (t.effect : ε) := le_rfl

@[simp] theorem Tm.effect_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    (t.rename ρ).effect = (t.effect : ε) := by
  induction t generalizing m <;> simp_all [Tm.rename, Tm.effect]

theorem HasEffect.rename {t : Tm ν Φ n} {e : ε} (h : HasEffect t e) (ρ : Fin n → Fin m) :
    HasEffect (t.rename ρ) e := by simpa only [HasEffect, Tm.effect_rename] using h

theorem Pure.effect_eq_bot {t : Tm ν Φ n} (h : Pure (⊥ : ε) t) : t.effect = (⊥ : ε) := by
  induction h <;> simp_all [Tm.effect, IsPure]

theorem Pure.hasEffect {t : Tm ν Φ n} (h : Pure (⊥ : ε) t) : HasEffect t (⊥ : ε) :=
  le_of_eq h.effect_eq_bot

theorem pure_of_hasEffect_bot {t : Tm ν Φ n} (h : HasEffect t (⊥ : ε)) : Pure (⊥ : ε) t := by
  induction t with
  | fv => exact .fv
  | bv => exact .bv
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

theorem pure_iff_hasEffect_bot (t : Tm ν Φ n) :
    Pure (⊥ : ε) t ↔ HasEffect t (⊥ : ε) :=
  ⟨Pure.hasEffect, pure_of_hasEffect_bot⟩

/-- Substitution at a common bound preserves that bound. -/
theorem HasEffect.bsubst {t : Tm ν Φ n} {e : ε} (h : HasEffect t e)
    {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, HasEffect (σ i) e) :
    HasEffect (t.bsubst σ) e := by
  have hup : ∀ {n m : Nat} {σ : Fin n → Tm ν Φ m},
      (∀ i, HasEffect (σ i) e) → ∀ i, HasEffect (Tm.upSub σ i) e := by
    intro n m σ hσ i
    refine Fin.cases bot_le (fun j => ?_) i
    simpa only [Tm.upSub, Fin.cases_succ, Tm.lift, HasEffect, Tm.effect_rename] using hσ j
  induction t generalizing m with
  | fv => exact bot_le
  | bv i => exact hσ i
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

variable {τ : Type r} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]

def HasTypeEffect (Γ : Ctx ν τ) (β : BoundCtx τ n) (t : Tm ν Φ n) (A : τ) (e : ε) : Prop :=
  HasType Φ Γ β t A ∧ HasEffect t e

theorem HasTypeEffect.mono {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A : τ} {e e' : ε} (h : HasTypeEffect Γ β t A e) (he : e ≤ e') :
    HasTypeEffect Γ β t A e' := ⟨h.1, h.2.mono he⟩

theorem HasType.hasTypeEffect_top [OrderTop ε] {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    HasTypeEffect Γ β t A (⊤ : ε) := ⟨h, .top t⟩

end Silmaril.Isotope.LetCase.LocallyNameless
