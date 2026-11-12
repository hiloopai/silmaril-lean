module

public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementEmbedding
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementEmbedding
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevantSeq
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevantCase
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevant
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModelReindex

@[expose] public section
noncomputable section

/-! # Model restriction preserving native fragment coercion witnesses

Each subtype witness is mapped to the identical target operation symbol.
The reduct functors and quotient comparisons follow the same exact typed
inclusions as the derivation-level inference morphisms.
-/

namespace Silmaril.Isotope.Morphism.SeqCase.ProofRelevant

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open LetSeq.ProofRelevant.LocallyNameless

universe u v w r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]

/-- The signature inclusion retains the exact coercion witness in `sub`. -/
def signatureHom (Γ : Ctx ν τ) : Signature.Hom (Models.signature Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.signature Φ Γ) where
  sort i := i
  op o := match o with
    | .fv h => .fv h
    | .bv i => .bv i
    | .op f => .op f
    | .let₁ A B => .let₁ A B
    | .unit => .unit
    | .pair A B => .pair A B
    | .let₂ A B C => .let₂ A B C
    | .sub d => .sub d
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- Native typing inclusion is an operation homomorphism. -/
def algebraHom (Γ : Ctx ν τ) : Models.syntaxAlgebra Φ Γ ⟶
    Algebra.reductObj (signatureHom Γ) (LetCase.ProofRelevant.LocallyNameless.Models.syntaxAlgebra Φ Γ) where
  map := TypedTerm.embed
  comm o args := by cases o <;> rfl

variable {ε : Type r} [HasEff Φ ε]

/-- Restrict equational models using actual native equation preservation. -/
def equationalModelRestriction (pureEff : ε) (Γ : Ctx ν τ) :
    LetCase.ProofRelevant.LocallyNameless.Models.EquationalModels (Φ := Φ) pureEff Γ ⥤
      Models.EquationalModels (Φ := Φ) pureEff Γ :=
  TheoryModel.Models.reindex (signatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ) (algebraHom Γ)
    (fun h => h.map TypedEquiv.Deriv.embed)

/-- The induced equation-class map is the unique arrow from the initial model. -/
def equationalQuotientComparison (pureEff : ε) (Γ : Ctx ν τ) :
    Models.syntacticModel (Φ := Φ) pureEff Γ ⟶
      (equationalModelRestriction pureEff Γ).obj (LetCase.ProofRelevant.LocallyNameless.Models.syntacticModel pureEff Γ) :=
  quotientReindex (signatureHom Γ) (algebraHom Γ) (fun h => h.map TypedEquiv.Deriv.embed)

@[simp] theorem equationalQuotientComparison_class (pureEff : ε) (Γ : Ctx ν τ)
    {i} (a : Models.Carrier Φ Γ i) :
    (equationalQuotientComparison pureEff Γ).map
      ((quotientMap (Models.equationCongruence pureEff Γ)).map a) =
        (quotientMap (LetCase.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)).map a.embed := rfl

/-- Restrict ordered models along any sound map of primitive witness relations. -/
def refinementModelRestriction (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) :
    LetCase.ProofRelevant.LocallyNameless.Models.RefinementModels pureEff Γ S ⥤ Models.RefinementModels pureEff Γ R :=
  OrderedModels.reindex (signatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ) (algebraHom Γ)
    (fun h => h.map (Refinement.Deriv.embed f))

/-- Mutual-refinement classes map by the same exact witness inclusion. -/
def refinementQuotientComparison (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) :
    Models.orderedSyntacticModel pureEff Γ R ⟶
      (refinementModelRestriction pureEff Γ f).obj (LetCase.ProofRelevant.LocallyNameless.Models.orderedSyntacticModel pureEff Γ S) :=
  orderedQuotientReindex (signatureHom Γ) (algebraHom Γ) (fun h => h.map (Refinement.Deriv.embed f))

@[simp] theorem refinementQuotientComparison_class (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) {i} (a : Models.Carrier Φ Γ i) :
    (refinementQuotientComparison pureEff Γ f).toHom.map
      ((quotientMap (Models.refinementPreorder pureEff Γ R).equationalCore).map a) =
        (quotientMap (LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ S).equationalCore).map a.embed := rfl

end Silmaril.Isotope.Morphism.SeqCase.ProofRelevant

namespace Silmaril.Isotope.Morphism.CaseIter.ProofRelevant

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open LetCase.ProofRelevant.LocallyNameless

universe u v w r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]

/-- The signature inclusion retains the exact coercion witness in `sub`. -/
def signatureHom (Γ : Ctx ν τ) : Signature.Hom (Models.signature Φ Γ)
    (LetIter.ProofRelevant.LocallyNameless.Models.signature Φ Γ) where
  sort i := i
  op o := match o with
    | .fv h => .fv h
    | .bv i => .bv i
    | .op f => .op f
    | .let₁ A B => .let₁ A B
    | .unit => .unit
    | .pair A B => .pair A B
    | .let₂ A B C => .let₂ A B C
    | .inl A B => .inl A B
    | .inr A B => .inr A B
    | .case A B C => .case A B C
    | .abort C => .abort C
    | .sub d => .sub d
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- Native typing inclusion is an operation homomorphism. -/
def algebraHom (Γ : Ctx ν τ) : Models.syntaxAlgebra Φ Γ ⟶
    Algebra.reductObj (signatureHom Γ) (LetIter.ProofRelevant.LocallyNameless.Models.syntaxAlgebra Φ Γ) where
  map := TypedTerm.embed
  comm o args := by cases o <;> rfl

variable {ε : Type r} [HasEff Φ ε]

/-- Restrict equational models using actual native equation preservation. -/
def equationalModelRestriction (pureEff : ε) (Γ : Ctx ν τ) :
    LetIter.ProofRelevant.LocallyNameless.Models.EquationalModels (Φ := Φ) pureEff Γ ⥤
      Models.EquationalModels (Φ := Φ) pureEff Γ :=
  TheoryModel.Models.reindex (signatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetIter.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ) (algebraHom Γ)
    (fun h => h.map TypedEquiv.Deriv.embed)

/-- The induced equation-class map is the unique arrow from the initial model. -/
def equationalQuotientComparison (pureEff : ε) (Γ : Ctx ν τ) :
    Models.syntacticModel (Φ := Φ) pureEff Γ ⟶
      (equationalModelRestriction pureEff Γ).obj (LetIter.ProofRelevant.LocallyNameless.Models.syntacticModel pureEff Γ) :=
  quotientReindex (signatureHom Γ) (algebraHom Γ) (fun h => h.map TypedEquiv.Deriv.embed)

@[simp] theorem equationalQuotientComparison_class (pureEff : ε) (Γ : Ctx ν τ)
    {i} (a : Models.Carrier Φ Γ i) :
    (equationalQuotientComparison pureEff Γ).map
      ((quotientMap (Models.equationCongruence pureEff Γ)).map a) =
        (quotientMap (LetIter.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)).map a.embed := rfl

/-- Restrict ordered models along any sound map of primitive witness relations. -/
def refinementModelRestriction (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetIter.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) :
    LetIter.ProofRelevant.LocallyNameless.Models.RefinementModels pureEff Γ S ⥤ Models.RefinementModels pureEff Γ R :=
  OrderedModels.reindex (signatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetIter.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ) (algebraHom Γ)
    (fun h => h.map (Refinement.Deriv.embed f))

/-- Mutual-refinement classes map by the same exact witness inclusion. -/
def refinementQuotientComparison (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetIter.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) :
    Models.orderedSyntacticModel pureEff Γ R ⟶
      (refinementModelRestriction pureEff Γ f).obj (LetIter.ProofRelevant.LocallyNameless.Models.orderedSyntacticModel pureEff Γ S) :=
  orderedQuotientReindex (signatureHom Γ) (algebraHom Γ) (fun h => h.map (Refinement.Deriv.embed f))

@[simp] theorem refinementQuotientComparison_class (pureEff : ε) (Γ : Ctx ν τ)
    {R : Refinement.Theory (Φ := Φ) Γ} {S : LetIter.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ Refinement.Theory.restrict S) {i} (a : Models.Carrier Φ Γ i) :
    (refinementQuotientComparison pureEff Γ f).toHom.map
      ((quotientMap (Models.refinementPreorder pureEff Γ R).equationalCore).map a) =
        (quotientMap (LetIter.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ S).equationalCore).map a.embed := rfl

end Silmaril.Isotope.Morphism.CaseIter.ProofRelevant
