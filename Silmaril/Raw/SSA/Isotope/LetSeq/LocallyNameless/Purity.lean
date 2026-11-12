module

public import Silmaril.SSA.Isotope.Types.Thms
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Structural

/-!
# Syntactic purity

Every primitive occurrence must have the chosen pure effect. This predicate is
independent of typing and imposes no effect algebra or semantic laws.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]

/-- All primitive operations in the term have the chosen pure effect. -/
inductive Pure (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv {n : Nat} {x : ν} : Pure pureEff (.fv (n := n) x)
  | bv {n : Nat} {i : Fin n} : Pure pureEff (.bv i)
  | op {n : Nat} {f : Φ} {a : Tm ν Φ n}
      (hf : IsPure pureEff f) (ha : Pure pureEff a) : Pure pureEff (.op f a)
  | let₁ {n : Nat} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.let₁ a b)
  | unit {n : Nat} : Pure pureEff (.unit (ν := ν) (Φ := Φ) (n := n))
  | pair {n : Nat} {a b : Tm ν Φ n}
      (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.pair a b)
  | let₂ {n : Nat} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)}
      (ha : Pure pureEff a) (hb : Pure pureEff b) : Pure pureEff (.let₂ a b)

namespace Pure

variable {pureEff : ε} {n m : Nat}

theorem rename {t : Tm ν Φ n} (h : Pure pureEff t) (ρ : Fin n → Fin m) :
    Pure pureEff (Tm.rename ρ t) := by
  induction h generalizing m with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf (ih ρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha ρ) (ihb (Tm.up ρ))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ _ _ iha ihb => exact .let₂ (iha ρ) (ihb (Tm.up (Tm.up ρ)))

theorem lift {t : Tm ν Φ n} (h : Pure pureEff t) : Pure pureEff t.lift :=
  h.rename Fin.succ

theorem underBinder {t : Tm ν Φ (n + 1)} (h : Pure pureEff t) :
    Pure pureEff t.underBinder := h.rename _

theorem underTwoBinders {t : Tm ν Φ (n + 2)} (h : Pure pureEff t) :
    Pure pureEff t.underTwoBinders := h.rename _

/-- Substitution preserves purity when every replacement is pure. -/
theorem bsubst {t : Tm ν Φ n} (h : Pure pureEff t) {σ : Fin n → Tm ν Φ m}
    (hσ : ∀ i, Pure pureEff (σ i)) : Pure pureEff (Tm.bsubst σ t) := by
  have hup : ∀ {n m : Nat} {σ : Fin n → Tm ν Φ m},
      (∀ i, Pure pureEff (σ i)) → ∀ i, Pure pureEff (Tm.upSub σ i) := by
    intro n m σ hσ i
    exact Fin.cases .bv (fun j => (hσ j).lift) i
  induction h generalizing m with
  | fv => exact .fv
  | bv => exact hσ _
  | op hf _ ih => exact .op hf (ih hσ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hσ) (ihb (hup hσ))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hσ) (ihb hσ)
  | let₂ _ _ iha ihb => exact .let₂ (iha hσ) (ihb (hup (hup hσ)))

theorem instantiate {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : Pure pureEff b) (ha : Pure pureEff a) : Pure pureEff (Tm.instantiate b a) :=
  hb.bsubst (Fin.cases ha fun _ => .bv)

theorem fsubst [DecidableEq ν] {t s : Tm ν Φ n} (h : Pure pureEff t)
    (hs : Pure pureEff s) (x : ν) : Pure pureEff (Tm.fsubst x s t) := by
  induction h with
  | fv => unfold Tm.fsubst; split <;> first | exact hs | exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf (ih hs)
  | let₁ _ _ iha ihb => exact .let₁ (iha hs) (ihb hs.lift)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hs) (ihb hs)
  | let₂ _ _ iha ihb => exact .let₂ (iha hs) (ihb hs.lift.lift)

end Pure

end Silmaril.Isotope.LetSeq.LocallyNameless
