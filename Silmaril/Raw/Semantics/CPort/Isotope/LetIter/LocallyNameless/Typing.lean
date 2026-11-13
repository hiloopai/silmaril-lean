module

public import Silmaril.Semantics.CPort.Isotope.Ctx.Bound.Defs
public import Silmaril.Semantics.CPort.Isotope.LetIter.LocallyNameless.Syntax.Defs
public import Silmaril.Semantics.CPort.Foundations.Signature.Defs
/-!
# Exact typing and purity for let-iter

Typing is proposition-valued and has no coercion rule. Purity is a separate
syntactic judgment; iteration is not pure merely because its instructions are.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]

/-- Exact typing over shared free and bound contexts. -/
inductive HasType (Φ : Type v) [HasTy Φ τ] (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Prop where
  | fv {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
      (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv {n : Nat} {β : BoundCtx τ n} {ι : Fin n} :
      HasType Φ Γ β (.bv ι) (β.get ι)
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      (ha : HasType Φ Γ β a (instrSrc f)) : HasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
      HasType Φ Γ β (.let₁ a b) B
  | unit {n : Nat} {β : BoundCtx τ n} : HasType Φ Γ β .unit Silmaril.unit
  | pair {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (Silmaril.product A B)
  | let₂ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
      (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) : HasType Φ Γ β (.let₂ a c) C
  | inl {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      (ha : HasType Φ Γ β a A) : HasType Φ Γ β (.inl a) (Silmaril.coprod A B)
  | inr {n : Nat} {β : BoundCtx τ n} {b : Tm ν Φ n} {A B : τ}
      (hb : HasType Φ Γ β b B) : HasType Φ Γ β (.inr b) (Silmaril.coprod A B)
  | case {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) : HasType Φ Γ β (.case e l r) C
  | abort {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {C : τ}
      (ha : HasType Φ Γ β a Silmaril.empty) : HasType Φ Γ β (.abort a) C
  | iter {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b (Silmaril.coprod B A)) :
      HasType Φ Γ β (.iter a b) B

namespace HasType

variable {Φ : Type v} [HasTy Φ τ] {Γ Γ' : Isotope.Ctx ν τ}

/-- Free-context transport needs only preservation of visible lookup types. -/
theorem weaken (hΓ : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β t A → HasType Φ Γ' β t A
  | _, _, _, _, .fv h => .fv (hΓ _ _ h)
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op h => .op (weaken hΓ h)
  | _, _, _, _, .let₁ ha hb => .let₁ (weaken hΓ ha) (weaken hΓ hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (weaken hΓ ha) (weaken hΓ hb)
  | _, _, _, _, .let₂ ha hc => .let₂ (weaken hΓ ha) (weaken hΓ hc)
  | _, _, _, _, .inl h => .inl (weaken hΓ h)
  | _, _, _, _, .inr h => .inr (weaken hΓ h)
  | _, _, _, _, .case he hl hr => .case (weaken hΓ he) (weaken hΓ hl) (weaken hΓ hr)
  | _, _, _, _, .abort h => .abort (weaken hΓ h)
  | _, _, _, _, .iter ha hb => .iter (weaken hΓ ha) (weaken hΓ hb)

end HasType

variable {Φ : Type v} {ε : Type r}

/-- Pure terms contain only pure instructions and no iteration. -/
inductive Pure [HasEff Φ ε] (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv {n : Nat} {x : ν} : Pure pureEff (.fv (n := n) x)
  | bv {n : Nat} {ι : Fin n} : Pure pureEff (.bv ι)
  | op {n : Nat} {f : Φ} {a : Tm ν Φ n}
      (hf : IsPure pureEff f) (ha : Pure pureEff a) : Pure pureEff (.op f a)
  | let₁ {n : Nat} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} :
      Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)
  | unit {n : Nat} : Pure pureEff (.unit (n := n))
  | pair {n : Nat} {a b : Tm ν Φ n} :
      Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ {n : Nat} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} :
      Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ a b)
  | inl {n : Nat} {a : Tm ν Φ n} : Pure pureEff a → Pure pureEff (.inl a)
  | inr {n : Nat} {a : Tm ν Φ n} : Pure pureEff a → Pure pureEff (.inr a)
  | case {n : Nat} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} :
      Pure pureEff e → Pure pureEff l → Pure pureEff r → Pure pureEff (.case e l r)
  | abort {n : Nat} {a : Tm ν Φ n} : Pure pureEff a → Pure pureEff (.abort a)

end Silmaril.Isotope.LetIter.LocallyNameless
