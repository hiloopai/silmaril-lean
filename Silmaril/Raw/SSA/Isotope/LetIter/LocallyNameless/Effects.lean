module

public import Silmaril.Raw.SSA.Isotope.Foundations.Effects
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-!
# Effect bounds for let-iter

The initializer runs once, so its effect is joined with the iterated body
effect. Bounds and exact typing are independent; their conjunction is the
effectful typing judgment. Existing `Pure` remains the loop-free fragment.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w}
    [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [HasEff Φ ε]
    {n m : Nat}

/-- A conservative structural effect bound, independent of typing. -/
def Tm.effect : {n : Nat} → Tm ν Φ n → ε
  | _, .fv _ | _, .bv _ | _, .unit => ⊥
  | _, .op f a => instrEff f ⊔ a.effect
  | _, .let₁ a b | _, .pair a b | _, .let₂ a b => a.effect ⊔ b.effect
  | _, .inl a | _, .inr a | _, .abort a => a.effect
  | _, .case a l r => a.effect ⊔ (l.effect ⊔ r.effect)
  | _, .iter a b => a.effect ⊔ iterEffect b.effect

def HasEffect (t : Tm ν Φ n) (e : ε) : Prop := t.effect ≤ e

theorem HasEffect.mono {t : Tm ν Φ n} {e e' : ε} (h : HasEffect t e) (he : e ≤ e') :
    HasEffect t e' := h.trans he

theorem HasEffect.top [OrderTop ε] (t : Tm ν Φ n) : HasEffect t (⊤ : ε) := le_top

theorem HasEffect.inferred (t : Tm ν Φ n) : HasEffect t (t.effect : ε) := le_rfl

@[simp] theorem hasEffect_op_iff {f : Φ} {a : Tm ν Φ n} {e : ε} :
    HasEffect (.op f a) e ↔ instrEff f ≤ e ∧ HasEffect a e := sup_le_iff

@[simp] theorem hasEffect_iter_iff {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {e : ε} :
    HasEffect (.iter a b) e ↔ HasEffect a e ∧ iterEffect b.effect ≤ e := sup_le_iff

/-- The common-bound iteration rule: repeated effects must stay within the bound. -/
theorem HasEffect.iter {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {e : ε}
    (he : IsIterative e) (ha : HasEffect a e) (hb : HasEffect b e) :
    HasEffect (.iter a b) e := sup_le ha (he.iterEffect_le hb)

/-- The sharper rule does not iterate the initializer's effects. -/
theorem HasEffect.iter_join {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {ea eb : ε}
    (ha : HasEffect a ea) (hb : HasEffect b eb) :
    HasEffect (.iter a b) (ea ⊔ iterEffect eb) := sup_le_sup ha (iterEffect_mono hb)

/-- The upward-closed predicate presentation additionally ensures every bound
on an iteration is itself iterative. This is not assumed for arbitrary closures. -/
theorem HasEffect.isIterative_of_iter (upward : IterativeUpwardClosed (ε := ε))
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {e : ε} (h : HasEffect (.iter a b) e) :
    IsIterative e := upward (isIterative_iterEffect _) (hasEffect_iter_iff.mp h).2

@[simp] theorem Tm.effect_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    (t.rename ρ).effect = (t.effect : ε) := by
  induction t generalizing m <;> simp_all [Tm.rename, Tm.effect]

theorem HasEffect.rename {t : Tm ν Φ n} {e : ε} (h : HasEffect t e) (ρ : Fin n → Fin m) :
    HasEffect (t.rename ρ) e := by simpa only [HasEffect, Tm.effect_rename] using h

/-- Loop-free primitive purity is sufficient for a bottom bound in every model. -/
theorem Pure.effect_eq_bot {t : Tm ν Φ n} (h : Pure (⊥ : ε) t) : t.effect = (⊥ : ε) := by
  induction h <;> simp_all [Tm.effect, IsPure]

theorem Pure.hasEffect {t : Tm ν Φ n} (h : Pure (⊥ : ε) t) : HasEffect t (⊥ : ε) :=
  le_of_eq h.effect_eq_bot

/-- When iteration adds an effect at bottom, a bottom-bounded term cannot contain
iteration. Without this assumption bottom bounds can include loops. -/
theorem pure_of_hasEffect_bot (hiter : iterEffect (⊥ : ε) ≠ ⊥)
    {t : Tm ν Φ n} (h : HasEffect t (⊥ : ε)) : Pure (⊥ : ε) t := by
  induction t with
  | fv => exact .fv
  | bv => exact .bv
  | unit => exact .unit
  | op f a ih =>
      obtain ⟨hf, ha⟩ := hasEffect_op_iff.mp h
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
  | iter a b _ _ =>
      have hb := (hasEffect_iter_iff.mp h).2
      exact False.elim (hiter (le_bot_iff.mp ((iterEffect_mono bot_le).trans hb)))

theorem pure_iff_hasEffect_bot (hiter : iterEffect (⊥ : ε) ≠ ⊥) (t : Tm ν Φ n) :
    Pure (⊥ : ε) t ↔ HasEffect t (⊥ : ε) :=
  ⟨Pure.hasEffect, pure_of_hasEffect_bot hiter⟩

/-- Substituting bottom-bounded terms never increases the structural effect. -/
theorem Tm.effect_bsubst_le (t : Tm ν Φ n) {σ : Fin n → Tm ν Φ m}
    (hσ : ∀ i, HasEffect (σ i) (⊥ : ε)) :
    (t.bsubst σ).effect ≤ (t.effect : ε) := by
  have hup : ∀ {n m : Nat} {σ : Fin n → Tm ν Φ m},
      (∀ i, HasEffect (σ i) (⊥ : ε)) → ∀ i, HasEffect (Tm.upSub σ i) (⊥ : ε) := by
    intro n m σ hσ i
    refine Fin.cases bot_le (fun j => ?_) i
    simpa only [Tm.upSub, Fin.cases_succ, Tm.lift, HasEffect, Tm.effect_rename] using hσ j
  induction t generalizing m with
  | fv => exact le_rfl
  | bv i => exact hσ i
  | unit => exact le_rfl
  | op f a ih => exact sup_le_sup_left (ih hσ) _
  | let₁ a b iha ihb => exact sup_le_sup (iha hσ) (ihb (hup hσ))
  | pair a b iha ihb => exact sup_le_sup (iha hσ) (ihb hσ)
  | let₂ a b iha ihb => exact sup_le_sup (iha hσ) (ihb (hup (hup hσ)))
  | inl a ih => exact ih hσ
  | inr a ih => exact ih hσ
  | abort a ih => exact ih hσ
  | case a l r iha ihl ihr =>
      exact sup_le_sup (iha hσ) (sup_le_sup (ihl (hup hσ)) (ihr (hup hσ)))
  | iter a b iha ihb => exact sup_le_sup (iha hσ) (iterEffect_mono (ihb (hup hσ)))

theorem HasEffect.bsubst_bot {t : Tm ν Φ n} {e : ε} (h : HasEffect t e)
    {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, HasEffect (σ i) (⊥ : ε)) :
    HasEffect (t.bsubst σ) e := (t.effect_bsubst_le hσ).trans h

/-- Substitution at an iterative common bound may introduce effects beneath loops. -/
theorem HasEffect.bsubst {t : Tm ν Φ n} {e : ε} (he : IsIterative e) (h : HasEffect t e)
    {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, HasEffect (σ i) e) : HasEffect (t.bsubst σ) e := by
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
  | iter a b iha ihb =>
      obtain ⟨ha, hb⟩ := hasEffect_iter_iff.mp h
      exact .iter he (iha ha hσ) (ihb ((le_iterEffect _).trans hb) (hup hσ))

section Typing

variable {τ : Type r} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]

/-- Exact typing and the independent effect upper bound. -/
def HasTypeEffect (Γ : Ctx ν τ) (β : BoundCtx τ n) (t : Tm ν Φ n) (A : τ) (e : ε) : Prop :=
  HasType Φ Γ β t A ∧ HasEffect t e

theorem HasTypeEffect.mono {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A : τ} {e e' : ε} (h : HasTypeEffect Γ β t A e) (he : e ≤ e') :
    HasTypeEffect Γ β t A e' := ⟨h.1, h.2.mono he⟩

theorem HasType.hasTypeEffect_top [OrderTop ε] {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    HasTypeEffect Γ β t A (⊤ : ε) := ⟨h, .top t⟩

theorem HasTypeEffect.iter {Γ : Ctx ν τ} {β : BoundCtx τ n} {a : Tm ν Φ n}
    {b : Tm ν Φ (n + 1)} {A B : τ} {e : ε} (he : IsIterative e)
    (ha : HasTypeEffect Γ β a A e)
    (hb : HasTypeEffect Γ (.snoc β A) b (coprod B A) e) :
    HasTypeEffect Γ β (.iter a b) B e := ⟨.iter ha.1 hb.1, .iter he ha.2 hb.2⟩

theorem HasTypeEffect.iter_join {Γ : Ctx ν τ} {β : BoundCtx τ n} {a : Tm ν Φ n}
    {b : Tm ν Φ (n + 1)} {A B : τ} {ea eb : ε}
    (ha : HasTypeEffect Γ β a A ea)
    (hb : HasTypeEffect Γ (.snoc β A) b (coprod B A) eb) :
    HasTypeEffect Γ β (.iter a b) B (ea ⊔ iterEffect eb) :=
  ⟨.iter ha.1 hb.1, .iter_join ha.2 hb.2⟩

theorem HasTypeEffect.bsubst {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} {e : ε} {σ : Fin n → Tm ν Φ m}
    (he : IsIterative e) (h : HasTypeEffect Γ β t A e)
    (hσ : ∀ i, HasTypeEffect Γ β' (σ i) (β.get i) e) :
    HasTypeEffect Γ β' (t.bsubst σ) A e :=
  ⟨HasType.bsubst (fun i => (hσ i).1) h.1, HasEffect.bsubst he h.2 (fun i => (hσ i).2)⟩

theorem HasTypeEffect.bsubst_bot {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} {e : ε} {σ : Fin n → Tm ν Φ m}
    (h : HasTypeEffect Γ β t A e)
    (hσ : ∀ i, HasTypeEffect Γ β' (σ i) (β.get i) (⊥ : ε)) :
    HasTypeEffect Γ β' (t.bsubst σ) A e :=
  ⟨HasType.bsubst (fun i => (hσ i).1) h.1, h.2.bsubst_bot (fun i => (hσ i).2)⟩

end Typing

end Silmaril.Isotope.LetIter.LocallyNameless
