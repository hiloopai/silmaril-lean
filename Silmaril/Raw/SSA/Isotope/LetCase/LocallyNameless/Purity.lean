module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε] {pureEff : ε}

namespace Pure

theorem rename {t : Tm ν Φ n} (h : Pure pureEff t) (ρ : Fin n → Fin m) :
    Pure pureEff (t.rename ρ) := by
  induction h generalizing m with
  | fv => exact .fv
  | bv => exact .bv
  | op hf ha ih => exact .op hf (ih _)
  | let₁ ha hb iha ihb => exact .let₁ (iha _) (ihb _)
  | unit => exact .unit
  | pair ha hb iha ihb => exact .pair (iha _) (ihb _)
  | let₂ ha hb iha ihb => exact .let₂ (iha _) (ihb _)
  | inl ha ih => exact .inl (ih _)
  | inr ha ih => exact .inr (ih _)
  | case he hl hr ihe ihl ihr => exact .case (ihe _) (ihl _) (ihr _)
  | abort ha ih => exact .abort (ih _)

theorem lift {t : Tm ν Φ n} (h : Pure pureEff t) : Pure pureEff t.lift :=
  h.rename Fin.succ

theorem upSub {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, Pure pureEff (σ i)) :
    ∀ i, Pure pureEff (Tm.upSub σ i) :=
  Fin.cases .bv (fun i => (hσ i).lift)

theorem bsubst {t : Tm ν Φ n} (h : Pure pureEff t)
    {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, Pure pureEff (σ i)) :
    Pure pureEff (t.bsubst σ) := by
  induction h generalizing m with
  | fv => exact .fv
  | bv => exact hσ _
  | op hf ha ih => exact .op hf (ih hσ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hσ) (ihb (upSub hσ))
  | unit => exact .unit
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | let₂ ha hb iha ihb => exact .let₂ (iha hσ) (ihb (upSub (upSub hσ)))
  | inl ha ih => exact .inl (ih hσ)
  | inr ha ih => exact .inr (ih hσ)
  | case he hl hr ihe ihl ihr => exact .case (ihe hσ) (ihl (upSub hσ)) (ihr (upSub hσ))
  | abort ha ih => exact .abort (ih hσ)

theorem instantiate {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : Pure pureEff b) (ha : Pure pureEff a) : Pure pureEff (Tm.instantiate b a) :=
  hb.bsubst (Fin.cases ha (fun _ => .bv))

end Pure
end Silmaril.Isotope.LetCase.LocallyNameless
