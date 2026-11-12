module

public import Silmaril.Raw.SSA.Isotope.Morphism.Models
public import Silmaril.Raw.SSA.Isotope.Theory.Models.RawRefinement
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Refinement
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModelReindex

/-! # Ordered model restriction and comparison of refinement quotients -/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.SeqCase

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- Restrict a raw ordered model along a refinement-preserving inclusion. -/
def rawOrderedModelRestriction (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    LetCase.LocallyNameless.RawModels.RefinementModels Q ⥤ RawModels.RefinementModels R :=
  OrderedModels.reindex rawSignatureHom (RawModels.termIsInitial ν Φ)
    (LetCase.LocallyNameless.RawModels.termIsInitial ν Φ) rawAlgebraHom sound

/-- Raw mutual-refinement classes embed by the actual constructor inclusion. -/
noncomputable def rawOrderedQuotientComparison (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    RawModels.orderedSyntacticModel R ⟶ (rawOrderedModelRestriction R Q sound).obj
      (LetCase.LocallyNameless.RawModels.orderedSyntacticModel Q) :=
  orderedQuotientReindex rawSignatureHom rawAlgebraHom sound

@[simp] theorem rawOrderedQuotientComparison_class (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b))
    {n} (a : Tm ν Φ n) :
    (rawOrderedQuotientComparison R Q sound).toHom.map
        ((quotientMap (RawModels.compatiblePreorder R).equationalCore).map a) =
      (quotientMap (LetCase.LocallyNameless.RawModels.compatiblePreorder Q).equationalCore).map
        (embed a) := rfl

theorem rawOrderedQuotientComparison_initial (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    rawOrderedQuotientComparison R Q sound = (RawModels.orderedSyntacticModelIsInitial R).to
      ((rawOrderedModelRestriction R Q sound).obj
        (LetCase.LocallyNameless.RawModels.orderedSyntacticModel Q)) :=
  (RawModels.orderedSyntacticModelIsInitial R).hom_ext _ _

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exact typed ordered models restrict along the same operation map. -/
def typedOrderedModelRestriction (Γ : Ctx ν τ) (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    LetCase.LocallyNameless.Models.OrderedModelsOfTheory Q ⥤ Models.OrderedModelsOfTheory R :=
  OrderedModels.reindex (typedSignatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetCase.LocallyNameless.Models.syntaxIsInitial Φ Γ) (typedAlgebraHom Γ)
    (fun h => sound h)

/-- The unique comparison of typed refinement quotients preserves order and operations. -/
noncomputable def typedOrderedQuotientComparison (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    Models.theoryOrderedQuotientModel R ⟶ (typedOrderedModelRestriction Γ R Q sound).obj
      (LetCase.LocallyNameless.Models.theoryOrderedQuotientModel Q) :=
  orderedQuotientReindex (typedSignatureHom Γ) (typedAlgebraHom Γ) (fun h => sound h)

@[simp] theorem typedOrderedQuotientComparison_class (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b))
    {i} (a : Models.Carrier Φ Γ i) :
    (typedOrderedQuotientComparison Γ R Q sound).toHom.map
        ((quotientMap (Models.theoryPrecongruence R).equationalCore).map a) =
      (quotientMap (LetCase.LocallyNameless.Models.theoryPrecongruence Q).equationalCore).map
        ⟨embed a.1, derivation a.2⟩ := rfl

theorem typedOrderedQuotientComparison_initial (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    typedOrderedQuotientComparison Γ R Q sound = (Models.theoryOrderedQuotientIsInitial R).to
      ((typedOrderedModelRestriction Γ R Q sound).obj
        (LetCase.LocallyNameless.Models.theoryOrderedQuotientModel Q)) :=
  (Models.theoryOrderedQuotientIsInitial R).hom_ext _ _

variable {ε : Type r} [HasEff Φ ε]

/-- Primitive-rule preservation suffices for the concrete refinement theories. -/
def refinementModelRestriction (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetCase.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :
    LetCase.LocallyNameless.Models.RefinementModels pureEff Γ Q ⥤
      Models.RefinementModels pureEff Γ R :=
  typedOrderedModelRestriction Γ (refinementTheory pureEff Γ R)
    (LetCase.LocallyNameless.refinementTheory pureEff Γ Q) (embed_refinement hRQ)

end Silmaril.Isotope.Morphism.SeqCase

namespace Silmaril.Isotope.Morphism.CaseIter

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- Restrict a raw ordered model along a refinement-preserving inclusion. -/
def rawOrderedModelRestriction (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    LetIter.LocallyNameless.RawModels.RefinementModels Q ⥤ RawModels.RefinementModels R :=
  OrderedModels.reindex rawSignatureHom (RawModels.termIsInitial ν Φ)
    (LetIter.LocallyNameless.RawModels.termIsInitial ν Φ) rawAlgebraHom sound

/-- Raw mutual-refinement classes embed by the actual constructor inclusion. -/
noncomputable def rawOrderedQuotientComparison (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    RawModels.orderedSyntacticModel R ⟶ (rawOrderedModelRestriction R Q sound).obj
      (LetIter.LocallyNameless.RawModels.orderedSyntacticModel Q) :=
  orderedQuotientReindex rawSignatureHom rawAlgebraHom sound

@[simp] theorem rawOrderedQuotientComparison_class (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b))
    {n} (a : Tm ν Φ n) :
    (rawOrderedQuotientComparison R Q sound).toHom.map
        ((quotientMap (RawModels.compatiblePreorder R).equationalCore).map a) =
      (quotientMap (LetIter.LocallyNameless.RawModels.compatiblePreorder Q).equationalCore).map
        (embed a) := rfl

theorem rawOrderedQuotientComparison_initial (R : RefinementTheory (rawSyntax ν Φ))
    (Q : RefinementTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, R.Rel a b → Q.Rel (embed a) (embed b)) :
    rawOrderedQuotientComparison R Q sound = (RawModels.orderedSyntacticModelIsInitial R).to
      ((rawOrderedModelRestriction R Q sound).obj
        (LetIter.LocallyNameless.RawModels.orderedSyntacticModel Q)) :=
  (RawModels.orderedSyntacticModelIsInitial R).hom_ext _ _

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exact typed ordered models restrict along the same operation map. -/
def typedOrderedModelRestriction (Γ : Ctx ν τ) (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    LetIter.LocallyNameless.Models.OrderedModelsOfTheory Q ⥤ Models.OrderedModelsOfTheory R :=
  OrderedModels.reindex (typedSignatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetIter.LocallyNameless.Models.syntaxIsInitial Φ Γ) (typedAlgebraHom Γ)
    (fun h => sound h)

/-- The unique comparison of typed refinement quotients preserves order and operations. -/
noncomputable def typedOrderedQuotientComparison (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    Models.theoryOrderedQuotientModel R ⟶ (typedOrderedModelRestriction Γ R Q sound).obj
      (LetIter.LocallyNameless.Models.theoryOrderedQuotientModel Q) :=
  orderedQuotientReindex (typedSignatureHom Γ) (typedAlgebraHom Γ) (fun h => sound h)

@[simp] theorem typedOrderedQuotientComparison_class (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b))
    {i} (a : Models.Carrier Φ Γ i) :
    (typedOrderedQuotientComparison Γ R Q sound).toHom.map
        ((quotientMap (Models.theoryPrecongruence R).equationalCore).map a) =
      (quotientMap (LetIter.LocallyNameless.Models.theoryPrecongruence Q).equationalCore).map
        ⟨embed a.1, derivation a.2⟩ := rfl

theorem typedOrderedQuotientComparison_initial (Γ : Ctx ν τ)
    (R : RefinementTheory (typedSyntax Φ Γ))
    (Q : RefinementTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      R.Rel a b → Q.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    typedOrderedQuotientComparison Γ R Q sound = (Models.theoryOrderedQuotientIsInitial R).to
      ((typedOrderedModelRestriction Γ R Q sound).obj
        (LetIter.LocallyNameless.Models.theoryOrderedQuotientModel Q)) :=
  (Models.theoryOrderedQuotientIsInitial R).hom_ext _ _

variable {ε : Type r} [HasEff Φ ε]

/-- Primitive-rule preservation suffices for the concrete refinement theories. -/
def refinementModelRestriction (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetIter.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :
    LetIter.LocallyNameless.Models.RefinementModels pureEff Γ Q ⥤
      Models.RefinementModels pureEff Γ R :=
  typedOrderedModelRestriction Γ (refinementTheory pureEff Γ R)
    (LetIter.LocallyNameless.refinementTheory pureEff Γ Q) (embed_refinement hRQ)

end Silmaril.Isotope.Morphism.CaseIter
