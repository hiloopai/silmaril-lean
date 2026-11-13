module

public import Silmaril.Semantics.CPort.Isotope.Ctx.Bound.Defs
public import Silmaril.Semantics.CPort.Isotope.LetCase.LocallyNameless.Syntax.Defs
@[expose] public section

-- Infer indexed binders locally.
set_option autoImplicit true

namespace Silmaril.Isotope.LetCase.LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]

/-- Exact typing over free and scoped bound contexts, independent of purity. -/
inductive HasType (Φ : Type q) [HasTy Φ τ] (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Prop where
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


inductive Pure [HasEff Φ ε] (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv : Pure pureEff (.fv x)
  | bv : Pure pureEff (.bv ι)
  | op (hf : IsPure pureEff f) (ha : Pure pureEff a) : Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ a b)
  | inl : Pure pureEff a → Pure pureEff (.inl a)
  | inr : Pure pureEff a → Pure pureEff (.inr a)
  | case : Pure pureEff e → Pure pureEff l → Pure pureEff r → Pure pureEff (.case e l r)
  | abort : Pure pureEff a → Pure pureEff (.abort a)

end Silmaril.Isotope.LetCase.LocallyNameless
