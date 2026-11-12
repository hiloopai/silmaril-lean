module

public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.EquationEmbedding
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementInference
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementInference

@[expose] public section
noncomputable section
set_option autoImplicit true

/-! # Native witness-sensitive refinement and inference inclusions -/

namespace Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless.Refinement

open Silmaril.Isotope.LetSeq.LocallyNameless (Tm)
open Silmaril.Logic.Metatheory Cslib.Logic Silmaril.Logic.Metatheory

universe u v w r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] {pureEff : ε} {Γ : Ctx ν τ}

/-- Restrict primitive rewrites by the exact typing inclusion. -/
def Theory.restrict (S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) : Theory (Φ := Φ) Γ where
  rel ha hb := S.rel ha.embed hb.embed

/-- Inclusion of a native refinement derivation, with arbitrary mapped axioms. -/
def Deriv.embed {R : Theory (Φ := Φ) Γ} {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Theory.restrict S)
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) :
    LetCase.ProofRelevant.LocallyNameless.Refinement.Deriv pureEff Γ S ha.embed hb.embed := by
  induction d with
  | refl h => exact .refl h.embed
  | trans _ _ ih ik => exact .trans ih ik
  | «axiom» h => exact .«axiom» (f h)
  | equiv d => exact .equiv d.embed
  | sub _ d ih => exact .sub ih d
  | op _ ih => exact .op ih
  | let₁ _ _ ih ik => exact .let₁ ih ik
  | pair _ _ ih ik => exact .pair ih ik
  | let₂ _ _ ih ik => exact .let₂ ih ik

/-- The translated conclusion retains its source subtype witnesses. -/
def Judgment.embed (j : Judgment (Φ := Φ) Γ) : LetCase.ProofRelevant.LocallyNameless.Refinement.Judgment (Φ := Φ) Γ where
  n := j.n
  bound := j.bound
  type := j.type
  left := Morphism.SeqCase.embed j.left
  right := Morphism.SeqCase.embed j.right
  leftTyping := j.leftTyping.embed
  rightTyping := j.rightTyping.embed

/-- Equational inclusion as a proof-relevant inference morphism. -/
def equationEmbedding (pureEff : ε) (Γ : Ctx ν τ) : InferenceMorphism
    (EquationalSystem pureEff Γ) (LetCase.ProofRelevant.LocallyNameless.Refinement.EquationalSystem pureEff Γ)
    (Judgment (Φ := Φ) Γ) (LetCase.ProofRelevant.LocallyNameless.Refinement.Judgment (Φ := Φ) Γ) where
  map := Judgment.embed
  mapDerivation := TypedEquiv.Deriv.embed

/-- Refinement inclusion maps the entire derivation, including exact transitivity witnesses. -/
def refinementEmbedding (pureEff : ε) (Γ : Ctx ν τ)
    {R : Theory (Φ := Φ) Γ} {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Theory.restrict S) : InferenceMorphism
    (RefinementSystem pureEff Γ R) (LetCase.ProofRelevant.LocallyNameless.Refinement.RefinementSystem pureEff Γ S)
    (Judgment (Φ := Φ) Γ) (LetCase.ProofRelevant.LocallyNameless.Refinement.Judgment (Φ := Φ) Γ) where
  map := Judgment.embed
  mapDerivation := Deriv.embed f

end Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless.Refinement
