module

public import Silmaril.Semantics.CPort.Isotope.LetCase.Semantics.Monadic.Defs
public import Silmaril.Semantics.CPort.Isotope.LetIter.Semantics.Monadic.Defs
public import Silmaril.Semantics.CPort.Isotope.Morphism.CaseIter.Defs
/-! Exact derivations and their meanings commute with this calculus inclusion. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope

open Semantics

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type q} [HasTy Φ τ] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

namespace Morphism.CaseIter

open LetCase.LocallyNameless

/-- Case derivations embed without introducing iteration. -/
def derivation : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A → LetIter.LocallyNameless.Derivation Φ Γ β (embed t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (derivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (derivation ha) (derivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (derivation ha) (derivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (derivation ha) (derivation hb)
  | _, _, _, _, .inl ha => .inl (derivation ha)
  | _, _, _, _, .inr hb => .inr (derivation hb)
  | _, _, _, _, .case he hl hr => .case (derivation he) (derivation hl) (derivation hr)
  | _, _, _, _, .abort ha => .abort (derivation ha)

@[simp] theorem denote_derivation (D : τ → Type v)
    [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type v → Type v} [Monad m] [Elgot.Iterate m] (M : InstructionModel D Φ m)
    {t : Tm ν Φ n} (d : Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M γ ρ = d.denote D M γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
      simp only [derivation, embed, Derivation.denote,
        LetIter.LocallyNameless.Derivation.denote, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp only [derivation, embed, Derivation.denote,
        LetIter.LocallyNameless.Derivation.denote, iha, ihb]
  | case _ _ _ ihe ihl ihr =>
      simp only [derivation, embed, Derivation.denote,
        LetIter.LocallyNameless.Derivation.denote, ihe, ihl, ihr]
      congr 1

end Morphism.CaseIter

end Silmaril.Isotope
