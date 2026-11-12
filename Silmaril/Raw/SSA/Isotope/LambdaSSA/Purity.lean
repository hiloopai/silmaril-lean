module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.SSA.Isotope.Types.Thms

/-! Syntactic expression purity is independent of typing and scoping. -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Tm

variable {Φ : Type u} {ε : Type v} [HasEff Φ ε]

/-- Every primitive occurrence has the chosen pure effect. -/
inductive Pure (pureEff : ε) : Tm Φ → Prop where
  | var {i : Nat} : Pure pureEff (.var i)
  | op {f : Φ} {a : Tm Φ} (hf : IsPure pureEff f) (ha : Pure pureEff a) :
      Pure pureEff (.op f a)
  | let₁ {a b : Tm Φ} (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.let₁ a b)
  | pair {a b : Tm Φ} (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.pair a b)
  | unit : Pure pureEff .unit
  | let₂ {a b : Tm Φ} (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.let₂ a b)
  | inl {a : Tm Φ} (ha : Pure pureEff a) : Pure pureEff (.inl a)
  | inr {a : Tm Φ} (ha : Pure pureEff a) : Pure pureEff (.inr a)
  | case {e l r : Tm Φ} (he : Pure pureEff e) (hl : Pure pureEff l) (hr : Pure pureEff r) :
      Pure pureEff (.case e l r)
  | abort {a : Tm Φ} (ha : Pure pureEff a) : Pure pureEff (.abort a)

namespace Pure

variable {pureEff : ε}

theorem rename {t : Tm Φ} (h : Pure pureEff t) (ρ : Nat → Nat) :
    Pure pureEff (Tm.rename ρ t) := by
  induction h generalizing ρ with
  | var => exact .var
  | op hf _ ih => exact .op hf (ih ρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha ρ) (ihb _)
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ (iha ρ) (ihb _)
  | inl _ ih => exact .inl (ih ρ)
  | inr _ ih => exact .inr (ih ρ)
  | case _ _ _ ihe ihl ihr => exact .case (ihe ρ) (ihl _) (ihr _)
  | abort _ ih => exact .abort (ih ρ)

theorem liftSubst {σ : Nat → Tm Φ} (hσ : ∀ i, Pure pureEff (σ i)) :
    ∀ i, Pure pureEff (Tm.liftSubst σ i)
  | 0 => .var
  | _ + 1 => (hσ _).rename Nat.succ

theorem subst {t : Tm Φ} (h : Pure pureEff t) {σ : Nat → Tm Φ}
    (hσ : ∀ i, Pure pureEff (σ i)) : Pure pureEff (Tm.subst σ t) := by
  induction h generalizing σ with
  | var => exact hσ _
  | op hf _ ih => exact .op hf (ih hσ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hσ) (ihb (liftSubst hσ))
  | pair _ _ iha ihb => exact .pair (iha hσ) (ihb hσ)
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ (iha hσ) (ihb (liftSubst (liftSubst hσ)))
  | inl _ ih => exact .inl (ih hσ)
  | inr _ ih => exact .inr (ih hσ)
  | case _ _ _ ihe ihl ihr => exact .case (ihe hσ) (ihl (liftSubst hσ)) (ihr (liftSubst hσ))
  | abort _ ih => exact .abort (ih hσ)

end Pure
end Silmaril.Isotope.LambdaSSA.Tm
