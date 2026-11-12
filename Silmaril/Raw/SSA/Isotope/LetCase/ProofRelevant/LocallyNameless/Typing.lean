module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Purity
public import Silmaril.Raw.SSA.Isotope.Subtyping

@[expose] public section

open Silmaril.Isotope.LetCase.LocallyNameless

-- Infer indexed binders locally.
set_option autoImplicit true

namespace Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]

/-- Syntax-directed typing over a shared free context and an anonymous snoc
bound context. Derivations retain subtyping evidence in `Type`. -/
inductive HasType (Φ : Type q) [HasTy Φ τ] (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv ι) (β.get ι)
  | op (ha : HasType Φ Γ β a (instrSrc f)) : HasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) : HasType Φ Γ β (.let₁ a b) B
  | unit : HasType Φ Γ β .unit Silmaril.unit
  | pair (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (Silmaril.product A B)
  | let₂ (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) : HasType Φ Γ β (.let₂ a c) C
  | inl (ha : HasType Φ Γ β a A) : HasType Φ Γ β (.inl a) (Silmaril.coprod A B)
  | inr (hb : HasType Φ Γ β b B) : HasType Φ Γ β (.inr b) (Silmaril.coprod A B)
  | case (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) : HasType Φ Γ β (.case e l r) C
  | abort (ha : HasType Φ Γ β a Silmaril.empty) : HasType Φ Γ β (.abort a) C
  | sub (ha : HasType Φ Γ β a A) (hAB : Subty A B) : HasType Φ Γ β a B


end Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless
