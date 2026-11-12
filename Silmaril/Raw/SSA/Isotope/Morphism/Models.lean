module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.ModelReindex
public import Silmaril.Raw.SSA.Isotope.Morphism.TheoryCategories
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase.Monadic
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic
public import Silmaril.Raw.SSA.Isotope.Theory.Models.RawQuotient
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories

/-!
# Model restriction along the calculus inclusions

The operation maps retain argument positions and binder sorts. Restricting an
arbitrary model therefore retains all source operations, and the induced map
of syntactic quotients computes as the existing term embedding.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.SeqCase

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- The raw signature inclusion preserves every source constructor and binder. -/
def rawSignatureHom : Signature.Hom (RawModels.signature ν Φ)
    (LetCase.LocallyNameless.RawModels.signature ν Φ) where
  sort n := n
  op o := match o with
    | .fv x => .fv x
    | .bv i => .bv i
    | .op f => .op f
    | .let₁ => .let₁
    | .unit => .unit
    | .pair => .pair
    | .let₂ => .let₂
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- The existing raw embedding is a homomorphism of constructor algebras. -/
def rawAlgebraHom : RawModels.termAlgebra ν Φ ⟶
    Algebra.reductObj rawSignatureHom (LetCase.LocallyNameless.RawModels.termAlgebra ν Φ) where
  map := embed
  comm o args := by cases o <;> rfl

/-- Restrict any validating target model along a sound calculus inclusion. -/
def rawModelRestriction (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    LetCase.LocallyNameless.RawModels.EquationalModels F ⥤ RawModels.EquationalModels E :=
  TheoryModel.Models.reindex rawSignatureHom (RawModels.termIsInitial ν Φ)
    (LetCase.LocallyNameless.RawModels.termIsInitial ν Φ) rawAlgebraHom sound

/-- The comparison between raw syntactic quotients preserves all operations. -/
noncomputable def rawQuotientComparison (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    RawModels.syntacticModel E ⟶ (rawModelRestriction E F sound).obj
      (LetCase.LocallyNameless.RawModels.syntacticModel F) :=
  quotientReindex rawSignatureHom rawAlgebraHom sound

@[simp] theorem rawQuotientComparison_class (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b))
    {n} (a : Tm ν Φ n) :
    (rawQuotientComparison E F sound).map ((quotientMap (RawModels.congruence E)).map a) =
      (quotientMap (LetCase.LocallyNameless.RawModels.congruence F)).map (embed a) := rfl

/-- The computed quotient comparison is precisely the unique initial arrow. -/
theorem rawQuotientComparison_initial (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetCase.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    rawQuotientComparison E F sound = (RawModels.syntacticModelIsInitial E).to
      ((rawModelRestriction E F sound).obj (LetCase.LocallyNameless.RawModels.syntacticModel F)) :=
  (RawModels.syntacticModelIsInitial E).hom_ext _ _

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exact typing signatures have the same operation inclusion, at typed sorts. -/
def typedSignatureHom (Γ : Ctx ν τ) : Signature.Hom (Models.signature Φ Γ)
    (LetCase.LocallyNameless.Models.signature Φ Γ) where
  sort i := i
  op o := match o with
    | .fv h => .fv h
    | .bv i => .bv i
    | .op f => .op f
    | .let₁ A B => .let₁ A B
    | .unit => .unit
    | .pair A B => .pair A B
    | .let₂ A B C => .let₂ A B C
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- Data-valued typing derivations translate by the existing exact inclusion. -/
def typedAlgebraHom (Γ : Ctx ν τ) : Models.syntaxAlgebra Φ Γ ⟶
    Algebra.reductObj (typedSignatureHom Γ) (LetCase.LocallyNameless.Models.syntaxAlgebra Φ Γ) where
  map a := ⟨embed a.1, derivation a.2⟩
  comm o args := by cases o <;> rfl

/-- Restrict an arbitrary exact typed equation model. -/
def typedModelRestriction (Γ : Ctx ν τ) (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    LetCase.LocallyNameless.Models.ModelsOfTheory F ⥤ Models.ModelsOfTheory E :=
  TheoryModel.Models.reindex (typedSignatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetCase.LocallyNameless.Models.syntaxIsInitial Φ Γ) (typedAlgebraHom Γ)
    (fun h => sound h)

/-- A quotient term embeds into the restricted target syntactic model. -/
noncomputable def typedQuotientComparison (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    Models.theoryQuotientModel E ⟶ (typedModelRestriction Γ E F sound).obj
      (LetCase.LocallyNameless.Models.theoryQuotientModel F) :=
  quotientReindex (typedSignatureHom Γ) (typedAlgebraHom Γ) (fun h => sound h)

@[simp] theorem typedQuotientComparison_class (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b))
    {i} (a : Models.Carrier Φ Γ i) :
    (typedQuotientComparison Γ E F sound).map ((quotientMap (Models.theoryCongruence E)).map a) =
      (quotientMap (LetCase.LocallyNameless.Models.theoryCongruence F)).map
        ⟨embed a.1, derivation a.2⟩ := rfl

/-- Initiality determines the quotient comparison uniquely. -/
theorem typedQuotientComparison_initial (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetCase.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    typedQuotientComparison Γ E F sound = (Models.theoryQuotientIsInitial E).to
      ((typedModelRestriction Γ E F sound).obj (LetCase.LocallyNameless.Models.theoryQuotientModel F)) :=
  (Models.theoryQuotientIsInitial E).hom_ext _ _

variable {ε : Type r} [HasEff Φ ε]

/-- The base equational theories satisfy the restriction obligation. -/
def equationalModelRestriction (pureEff : ε) (Γ : Ctx ν τ) :
    LetCase.LocallyNameless.Models.EquationalModels (Φ := Φ) pureEff Γ ⥤
      Models.EquationalModels (Φ := Φ) pureEff Γ :=
  typedModelRestriction Γ (equationalTheory pureEff Γ)
    (LetCase.LocallyNameless.equationalTheory pureEff Γ) embed_equiv

end Silmaril.Isotope.Morphism.SeqCase

namespace Silmaril.Isotope.Morphism.CaseIter

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- The raw signature inclusion preserves every source constructor and binder. -/
def rawSignatureHom : Signature.Hom (RawModels.signature ν Φ)
    (LetIter.LocallyNameless.RawModels.signature ν Φ) where
  sort n := n
  op o := match o with
    | .fv x => .fv x
    | .bv i => .bv i
    | .op f => .op f
    | .let₁ => .let₁
    | .unit => .unit
    | .pair => .pair
    | .let₂ => .let₂
    | .inl => .inl
    | .inr => .inr
    | .case => .case
    | .abort => .abort
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- The existing raw embedding is a homomorphism of constructor algebras. -/
def rawAlgebraHom : RawModels.termAlgebra ν Φ ⟶
    Algebra.reductObj rawSignatureHom (LetIter.LocallyNameless.RawModels.termAlgebra ν Φ) where
  map := embed
  comm o args := by cases o <;> rfl

/-- Restrict any validating target model along a sound calculus inclusion. -/
def rawModelRestriction (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    LetIter.LocallyNameless.RawModels.EquationalModels F ⥤ RawModels.EquationalModels E :=
  TheoryModel.Models.reindex rawSignatureHom (RawModels.termIsInitial ν Φ)
    (LetIter.LocallyNameless.RawModels.termIsInitial ν Φ) rawAlgebraHom sound

/-- The comparison between raw syntactic quotients preserves all operations. -/
noncomputable def rawQuotientComparison (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    RawModels.syntacticModel E ⟶ (rawModelRestriction E F sound).obj
      (LetIter.LocallyNameless.RawModels.syntacticModel F) :=
  quotientReindex rawSignatureHom rawAlgebraHom sound

@[simp] theorem rawQuotientComparison_class (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b))
    {n} (a : Tm ν Φ n) :
    (rawQuotientComparison E F sound).map ((quotientMap (RawModels.congruence E)).map a) =
      (quotientMap (LetIter.LocallyNameless.RawModels.congruence F)).map (embed a) := rfl

/-- The computed quotient comparison is precisely the unique initial arrow. -/
theorem rawQuotientComparison_initial (E : EquationalTheory (rawSyntax ν Φ))
    (F : EquationalTheory (LetIter.LocallyNameless.rawSyntax ν Φ))
    (sound : ∀ {n} {a b : Tm ν Φ n}, E.Rel a b → F.Rel (embed a) (embed b)) :
    rawQuotientComparison E F sound = (RawModels.syntacticModelIsInitial E).to
      ((rawModelRestriction E F sound).obj (LetIter.LocallyNameless.RawModels.syntacticModel F)) :=
  (RawModels.syntacticModelIsInitial E).hom_ext _ _

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exact typing signatures have the same operation inclusion, at typed sorts. -/
def typedSignatureHom (Γ : Ctx ν τ) : Signature.Hom (Models.signature Φ Γ)
    (LetIter.LocallyNameless.Models.signature Φ Γ) where
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
  arg o := by cases o <;> exact Equiv.refl _
  argSort o j := by cases o <;> rfl

/-- Data-valued typing derivations translate by the existing exact inclusion. -/
def typedAlgebraHom (Γ : Ctx ν τ) : Models.syntaxAlgebra Φ Γ ⟶
    Algebra.reductObj (typedSignatureHom Γ) (LetIter.LocallyNameless.Models.syntaxAlgebra Φ Γ) where
  map a := ⟨embed a.1, derivation a.2⟩
  comm o args := by cases o <;> rfl

/-- Restrict an arbitrary exact typed equation model. -/
def typedModelRestriction (Γ : Ctx ν τ) (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    LetIter.LocallyNameless.Models.ModelsOfTheory F ⥤ Models.ModelsOfTheory E :=
  TheoryModel.Models.reindex (typedSignatureHom Γ) (Models.syntaxIsInitial Φ Γ)
    (LetIter.LocallyNameless.Models.syntaxIsInitial Φ Γ) (typedAlgebraHom Γ)
    (fun h => sound h)

/-- A quotient term embeds into the restricted target syntactic model. -/
noncomputable def typedQuotientComparison (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    Models.theoryQuotientModel E ⟶ (typedModelRestriction Γ E F sound).obj
      (LetIter.LocallyNameless.Models.theoryQuotientModel F) :=
  quotientReindex (typedSignatureHom Γ) (typedAlgebraHom Γ) (fun h => sound h)

@[simp] theorem typedQuotientComparison_class (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b))
    {i} (a : Models.Carrier Φ Γ i) :
    (typedQuotientComparison Γ E F sound).map ((quotientMap (Models.theoryCongruence E)).map a) =
      (quotientMap (LetIter.LocallyNameless.Models.theoryCongruence F)).map
        ⟨embed a.1, derivation a.2⟩ := rfl

/-- Initiality determines the quotient comparison uniquely. -/
theorem typedQuotientComparison_initial (Γ : Ctx ν τ)
    (E : EquationalTheory (typedSyntax Φ Γ))
    (F : EquationalTheory (LetIter.LocallyNameless.typedSyntax Φ Γ))
    (sound : ∀ {i} {a b : (typedSyntax Φ Γ).Term i},
      E.Rel a b → F.Rel ((typedTranslation Γ).term a) ((typedTranslation Γ).term b)) :
    typedQuotientComparison Γ E F sound = (Models.theoryQuotientIsInitial E).to
      ((typedModelRestriction Γ E F sound).obj (LetIter.LocallyNameless.Models.theoryQuotientModel F)) :=
  (Models.theoryQuotientIsInitial E).hom_ext _ _

variable {ε : Type r} [HasEff Φ ε]

/-- The base equational theories satisfy the restriction obligation. -/
def equationalModelRestriction (pureEff : ε) (Γ : Ctx ν τ) :
    LetIter.LocallyNameless.Models.EquationalModels (Φ := Φ) pureEff Γ ⥤
      Models.EquationalModels (Φ := Φ) pureEff Γ :=
  typedModelRestriction Γ (equationalTheory pureEff Γ)
    (LetIter.LocallyNameless.equationalTheory pureEff Γ) embed_equiv

end Silmaril.Isotope.Morphism.CaseIter
