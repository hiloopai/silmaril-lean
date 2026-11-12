module

public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase

/-! Exact derivations and their meanings commute with this calculus inclusion. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope

open Semantics

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type q} [HasTy Φ τ] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

namespace Morphism.SeqCase

open LetSeq.LocallyNameless

/-- The constructor-preserving inclusion also preserves exact typing data. -/
def derivation : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A → LetCase.LocallyNameless.Derivation Φ Γ β (embed t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (derivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (derivation ha) (derivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (derivation ha) (derivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (derivation ha) (derivation hb)

@[simp] theorem denote_derivation (D : τ → Type v)
    [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type v → Type v} [Monad m] (M : InstructionModel D Φ m)
    {t : Tm ν Φ n} (d : Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M γ ρ = d.denote D M γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih => simp only [derivation, embed, Derivation.denote,
      LetCase.LocallyNameless.Derivation.denote, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp only [derivation, embed, Derivation.denote,
        LetCase.LocallyNameless.Derivation.denote, iha, ihb]

end Morphism.SeqCase

end Silmaril.Isotope
