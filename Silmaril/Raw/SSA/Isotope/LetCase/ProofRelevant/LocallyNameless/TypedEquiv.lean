module

public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.TypingSubst

@[expose] public section

open Silmaril.Isotope.LetCase.LocallyNameless

-- Infer indexed binders locally.
set_option autoImplicit true

/-!
# Proof-relevant typed equality derivations

This native fragment judgment is indexed by the exact typing derivations at
its endpoints.  In particular, transitivity shares one literal middle typing
derivation.  This is necessary because subtype derivations have
proof-relevant denotations.
-/

namespace Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless.TypedEquiv

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]
variable {pureEff : ε} {Γ : Isotope.Ctx ν τ}

open LocallyNameless

set_option relaxedAutoImplicit true

-- Lean 4.35 cannot synthesize SizeOf for these dependent endpoint indices.
set_option genSizeOf false in
/-- A typed equational derivation whose endpoint typing evidence is retained.
Every equation is a native fragment constructor: no iteration rule or
intermediate term from a larger calculus is imported. -/
inductive Deriv (pureEff : ε) (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β a A → HasType Φ Γ β b A → Type (max u q w r) where
  | refl (h : HasType Φ Γ β a A) : Deriv pureEff Γ h h
  | symm (h : Deriv pureEff Γ ha hb) : Deriv pureEff Γ hb ha
  | trans (h : Deriv pureEff Γ ha hm) (k : Deriv pureEff Γ hm hc) :
      Deriv pureEff Γ ha hc
  | sub {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
      (h : Deriv pureEff Γ ha hb) (d : Subty A B) :
      Deriv pureEff Γ (.sub ha d) (.sub hb d)
  | op (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (.op ha) (.op hb)
  | let₁ (da : Deriv pureEff Γ ha ha')
      (db : Deriv pureEff Γ hb hb') :
      Deriv pureEff Γ (.let₁ ha hb) (.let₁ ha' hb')
  | pair (da : Deriv pureEff Γ ha ha')
      (db : Deriv pureEff Γ hb hb') :
      Deriv pureEff Γ (.pair ha hb) (.pair ha' hb')
  | let₂ (da : Deriv pureEff Γ ha ha')
      (dc : Deriv pureEff Γ hc hc') :
      Deriv pureEff Γ (.let₂ ha hc) (.let₂ ha' hc')
  | inl (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.inl (B := B) ha) (HasType.inl (B := B) hb)
  | inr (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.inr (A := A) ha) (HasType.inr (A := A) hb)
  | case (de : Deriv pureEff Γ he he')
      (dl : Deriv pureEff Γ hl hl') (dr : Deriv pureEff Γ hr hr') :
      Deriv pureEff Γ (.case he hl hr) (.case he' hl' hr')
  | abort (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.abort (C := C) ha) (HasType.abort (C := C) hb)
  | letBeta (hp : Pure pureEff a) (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) :
      Deriv pureEff Γ (.let₁ ha hb) (hb.instantiate ha)
  | letEta (ha : HasType Φ Γ β a A) :
      Deriv pureEff Γ
        (.let₁ ha HasType.newest) ha
  | unitEta (ha : HasType Φ Γ β a Silmaril.unit) :
      Deriv pureEff Γ (.let₁ ha .unit) ha
  | pairBeta (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Deriv pureEff Γ (.let₂ (.pair ha hb) hc)
        (.let₁ ha (.let₁ (hb.lift (B := A)) hc))
  | pairEta (ha : HasType Φ Γ β a (Silmaril.product A B)) :
      Deriv pureEff Γ
        (.let₂ ha
          (.pair HasType.previous HasType.newest)) ha
  | caseBetaL (he : HasType Φ Γ β e A)
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case (.inl he) hl hr) (.let₁ he hl)
  | caseBetaR (he : HasType Φ Γ β e B)
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case (.inr he) hl hr) (.let₁ he hr)
  | caseEta (he : HasType Φ Γ β e (Silmaril.coprod A B)) :
      Deriv pureEff Γ
        (.case he
          (.inl HasType.newest) (.inr HasType.newest)) he
  | bindOp (ha : HasType Φ Γ β a (instrSrc f))
      (hc : HasType Φ Γ (.snoc β (instrTrg f)) c C) :
      Deriv pureEff Γ (.let₁ (.op ha) hc)
        (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder))
  | bindLet (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B)
      (hc : HasType Φ Γ (.snoc β B) c C) :
      Deriv pureEff Γ (.let₁ (.let₁ ha hb) hc)
        (.let₁ ha (.let₁ hb hc.underBinder))
  | bindLetPair (he : HasType Φ Γ β e (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Deriv pureEff Γ (.let₁ (.let₂ he hc) hd)
        (.let₂ he (.let₁ hc (hd.underBinder.underBinder)))
  | bindLetCase (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Deriv pureEff Γ (.let₁ (.case he hl hr) hd)
        (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder))
  | bindPair (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Deriv pureEff Γ (.let₂ ha hc)
        (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders))
  | bindCase (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case he hl hr)
        (.let₁ he
          (.case HasType.newest hl.underBinder hr.underBinder))
  | emptyInitial (ha : HasType Φ Γ β a Silmaril.empty)
      (hb : HasType Φ Γ (.snoc β A) b B)
      (hc : HasType Φ Γ (.snoc β A) c B) :
      Deriv pureEff Γ (.let₁ (.abort ha) hb) (.let₁ (.abort ha) hc)
set_option relaxedAutoImplicit false

/-- Proposition truncation at fixed proof-relevant endpoints. -/
abbrev Related (pureEff : ε) (Γ : Isotope.Ctx ν τ)
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  Nonempty (Deriv pureEff Γ ha hb)

/-- Proposition-level equality of raw terms: endpoint derivations merely have
to exist, while the derivation connecting the chosen endpoints is truncated. -/
def EqvProp (pureEff : ε) (Γ : Isotope.Ctx ν τ) (β : BoundCtx τ n)
    (a b : Tm ν Φ n) (A : τ) : Prop :=
  Nonempty (Σ ha : HasType Φ Γ β a A,
    Σ hb : HasType Φ Γ β b A, Deriv pureEff Γ ha hb)

end Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless.TypedEquiv
