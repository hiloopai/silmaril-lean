module

public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetSeq
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetCase
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetIter
public import Silmaril.Raw.SSA.Isotope.Theory.Equational
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel

/-!
# Models of arbitrary theories over exact typed let syntax

Every contextual theory induces a congruence, or compatible preorder, on the
full constructor algebra. Its quotient is initial among all operation models
satisfying that theory. Thus the construction covers theory extensions as well
as the distinguished base theories.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory

variable {τ : Type u} [HasProduct τ] [HasUnit τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}

/-- One-hole contextual closure entails compatibility in all constructor arguments. -/
def theoryPrecongruence (R : RefinementTheory (typedSyntax Φ Γ)) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) where
  Rel a b := R.Rel (eraseCarrier a) (eraseCarrier b)
  refl a := R.refl _
  trans := R.trans
  compatible o a b h := by
    cases o with
    | fv hx => exact R.refl _
    | bv i => exact R.refl _
    | unit => exact R.refl _
    | op f => exact R.congr _ .op (h 0)
    | let₁ A B =>
        exact R.trans (R.congr _ (.let₁_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₁_right (eraseCarrier (b 0))) (h 1))
    | pair A B =>
        exact R.trans (R.congr _ (.pair_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.pair_right (eraseCarrier (b 0))) (h 1))
    | let₂ A B C =>
        exact R.trans (R.congr _ (.let₂_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₂_right (eraseCarrier (b 0))) (h 1))

/-- An arbitrary exact contextual equivalence is an operation congruence. -/
def theoryCongruence (E : EquationalTheory (typedSyntax Φ Γ)) :
    Congruence (syntaxAlgebra Φ Γ) where
  Rel := (theoryPrecongruence E.toRefinementTheory).Rel
  equivalence _ := ⟨fun _ => E.refl _, E.symm, E.trans⟩
  compatible := (theoryPrecongruence E.toRefinementTheory).compatible

/-- All operation models of a chosen equational theory, with all homomorphisms. -/
abbrev ModelsOfTheory (E : EquationalTheory (typedSyntax Φ Γ)) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial Φ Γ) (theoryCongruence E)

noncomputable def theoryQuotientModel (E : EquationalTheory (typedSyntax Φ Γ)) : ModelsOfTheory E :=
  quotientModel (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Quotient syntax is initial for every chosen equational theory extension. -/
noncomputable def theoryQuotientIsInitial (E : EquationalTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryQuotientModel E) :=
  quotientIsInitial (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Ordered operation models of an arbitrary contextual refinement theory. -/
abbrev OrderedModelsOfTheory (R : RefinementTheory (typedSyntax Φ Γ)) :=
  OrderedModels (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

noncomputable def theoryOrderedQuotientModel (R : RefinementTheory (typedSyntax Φ Γ)) :
    OrderedModelsOfTheory R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- Quotient by mutual refinement is initial among order-preserving models. -/
noncomputable def theoryOrderedQuotientIsInitial (R : RefinementTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryOrderedQuotientModel R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- The general construction specializes to the independently presented base calculus. -/
@[simp] theorem theoryCongruence_base {ε : Type*} [HasEff Φ ε] (pureEff : ε) :
    theoryCongruence (equationalTheory (Φ := Φ) pureEff Γ) =
      equationCongruence pureEff Γ := rfl

/-- Validity in every model characterizes any chosen equational theory. -/
theorem theory_semantic_iff (E : EquationalTheory (typedSyntax Φ Γ))
    {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    E.Rel (eraseCarrier a) (eraseCarrier b) ↔
      ∀ M : ModelsOfTheory E, denote M.algebra a.2 = denote M.algebra b.2 := by
  rcases i with ⟨n, β, A⟩
  rcases a with ⟨a, da⟩
  rcases b with ⟨b, db⟩
  simpa only [syntaxIsInitial_to, fold, theoryCongruence, theoryPrecongruence,
    eraseCarrier, ModelsOfTheory] using
    (Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
      (syntaxIsInitial Φ Γ) (theoryCongruence E) (i := ⟨n, β, A⟩) ⟨a, da⟩ ⟨b, db⟩)

end Silmaril.Isotope.LetSeq.LocallyNameless.Models

namespace Silmaril.Isotope.LetCase.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}

/-- One-hole contextual closure entails compatibility in all constructor arguments. -/
def theoryPrecongruence (R : RefinementTheory (typedSyntax Φ Γ)) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) where
  Rel a b := R.Rel (eraseCarrier a) (eraseCarrier b)
  refl a := R.refl _
  trans := R.trans
  compatible o a b h := by
    cases o with
    | fv hx => exact R.refl _
    | bv i => exact R.refl _
    | unit => exact R.refl _
    | op f => exact R.congr _ .op (h 0)
    | let₁ A B =>
        exact R.trans (R.congr _ (.let₁_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₁_right (eraseCarrier (b 0))) (h 1))
    | pair A B =>
        exact R.trans (R.congr _ (.pair_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.pair_right (eraseCarrier (b 0))) (h 1))
    | let₂ A B C =>
        exact R.trans (R.congr _ (.let₂_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₂_right (eraseCarrier (b 0))) (h 1))
    | inl A B => exact R.congr _ .inl (h 0)
    | inr A B => exact R.congr _ .inr (h 0)
    | case A B C =>
        exact R.trans
          (R.congr _ (.case_scrutinee (eraseCarrier (a 1)) (eraseCarrier (a 2))) (h 0))
          (R.trans
            (R.congr _ (.case_left (eraseCarrier (b 0)) (eraseCarrier (a 2))) (h 1))
            (R.congr _ (.case_right (eraseCarrier (b 0)) (eraseCarrier (b 1))) (h 2)))
    | abort C => exact R.congr _ .abort (h 0)

/-- An arbitrary exact contextual equivalence is an operation congruence. -/
def theoryCongruence (E : EquationalTheory (typedSyntax Φ Γ)) :
    Congruence (syntaxAlgebra Φ Γ) where
  Rel := (theoryPrecongruence E.toRefinementTheory).Rel
  equivalence _ := ⟨fun _ => E.refl _, E.symm, E.trans⟩
  compatible := (theoryPrecongruence E.toRefinementTheory).compatible

/-- All operation models of a chosen equational theory, with all homomorphisms. -/
abbrev ModelsOfTheory (E : EquationalTheory (typedSyntax Φ Γ)) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial Φ Γ) (theoryCongruence E)

noncomputable def theoryQuotientModel (E : EquationalTheory (typedSyntax Φ Γ)) : ModelsOfTheory E :=
  quotientModel (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Quotient syntax is initial for every chosen equational theory extension. -/
noncomputable def theoryQuotientIsInitial (E : EquationalTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryQuotientModel E) :=
  quotientIsInitial (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Ordered operation models of an arbitrary contextual refinement theory. -/
abbrev OrderedModelsOfTheory (R : RefinementTheory (typedSyntax Φ Γ)) :=
  OrderedModels (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

noncomputable def theoryOrderedQuotientModel (R : RefinementTheory (typedSyntax Φ Γ)) :
    OrderedModelsOfTheory R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- Quotient by mutual refinement is initial among order-preserving models. -/
noncomputable def theoryOrderedQuotientIsInitial (R : RefinementTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryOrderedQuotientModel R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- The general construction specializes to the independently presented base calculus. -/
@[simp] theorem theoryCongruence_base {ε : Type*} [HasEff Φ ε] (pureEff : ε) :
    theoryCongruence (equationalTheory (Φ := Φ) pureEff Γ) =
      equationCongruence pureEff Γ := rfl

/-- Validity in every model characterizes any chosen equational theory. -/
theorem theory_semantic_iff (E : EquationalTheory (typedSyntax Φ Γ))
    {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    E.Rel (eraseCarrier a) (eraseCarrier b) ↔
      ∀ M : ModelsOfTheory E, denote M.algebra a.2 = denote M.algebra b.2 := by
  rcases i with ⟨n, β, A⟩
  rcases a with ⟨a, da⟩
  rcases b with ⟨b, db⟩
  simpa only [syntaxIsInitial_to, fold, theoryCongruence, theoryPrecongruence,
    eraseCarrier, ModelsOfTheory] using
    (Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
      (syntaxIsInitial Φ Γ) (theoryCongruence E) (i := ⟨n, β, A⟩) ⟨a, da⟩ ⟨b, db⟩)

end Silmaril.Isotope.LetCase.LocallyNameless.Models

namespace Silmaril.Isotope.LetIter.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}

/-- One-hole contextual closure entails compatibility in all constructor arguments. -/
def theoryPrecongruence (R : RefinementTheory (typedSyntax Φ Γ)) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) where
  Rel a b := R.Rel (eraseCarrier a) (eraseCarrier b)
  refl a := R.refl _
  trans := R.trans
  compatible o a b h := by
    cases o with
    | fv hx => exact R.refl _
    | bv i => exact R.refl _
    | unit => exact R.refl _
    | op f => exact R.congr _ .op (h 0)
    | let₁ A B =>
        exact R.trans (R.congr _ (.let₁_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₁_right (eraseCarrier (b 0))) (h 1))
    | pair A B =>
        exact R.trans (R.congr _ (.pair_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.pair_right (eraseCarrier (b 0))) (h 1))
    | let₂ A B C =>
        exact R.trans (R.congr _ (.let₂_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.let₂_right (eraseCarrier (b 0))) (h 1))
    | inl A B => exact R.congr _ .inl (h 0)
    | inr A B => exact R.congr _ .inr (h 0)
    | case A B C =>
        exact R.trans
          (R.congr _ (.case_scrutinee (eraseCarrier (a 1)) (eraseCarrier (a 2))) (h 0))
          (R.trans
            (R.congr _ (.case_left (eraseCarrier (b 0)) (eraseCarrier (a 2))) (h 1))
            (R.congr _ (.case_right (eraseCarrier (b 0)) (eraseCarrier (b 1))) (h 2)))
    | abort C => exact R.congr _ .abort (h 0)
    | iter A B =>
        exact R.trans (R.congr _ (.iter_left (eraseCarrier (a 1))) (h 0))
          (R.congr _ (.iter_right (eraseCarrier (b 0))) (h 1))

/-- An arbitrary exact contextual equivalence is an operation congruence. -/
def theoryCongruence (E : EquationalTheory (typedSyntax Φ Γ)) :
    Congruence (syntaxAlgebra Φ Γ) where
  Rel := (theoryPrecongruence E.toRefinementTheory).Rel
  equivalence _ := ⟨fun _ => E.refl _, E.symm, E.trans⟩
  compatible := (theoryPrecongruence E.toRefinementTheory).compatible

/-- All operation models of a chosen equational theory, with all homomorphisms. -/
abbrev ModelsOfTheory (E : EquationalTheory (typedSyntax Φ Γ)) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial Φ Γ) (theoryCongruence E)

noncomputable def theoryQuotientModel (E : EquationalTheory (typedSyntax Φ Γ)) : ModelsOfTheory E :=
  quotientModel (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Quotient syntax is initial for every chosen equational theory extension. -/
noncomputable def theoryQuotientIsInitial (E : EquationalTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryQuotientModel E) :=
  quotientIsInitial (syntaxIsInitial Φ Γ) (theoryCongruence E)

/-- Ordered operation models of an arbitrary contextual refinement theory. -/
abbrev OrderedModelsOfTheory (R : RefinementTheory (typedSyntax Φ Γ)) :=
  OrderedModels (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

noncomputable def theoryOrderedQuotientModel (R : RefinementTheory (typedSyntax Φ Γ)) :
    OrderedModelsOfTheory R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- Quotient by mutual refinement is initial among order-preserving models. -/
noncomputable def theoryOrderedQuotientIsInitial (R : RefinementTheory (typedSyntax Φ Γ)) :
    CategoryTheory.Limits.IsInitial (theoryOrderedQuotientModel R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (theoryPrecongruence R)

/-- The general construction specializes to the independently presented base calculus. -/
@[simp] theorem theoryCongruence_base {ε : Type*} [HasEff Φ ε] (pureEff : ε) :
    theoryCongruence (equationalTheory (Φ := Φ) pureEff Γ) =
      equationCongruence pureEff Γ := rfl

/-- Validity in every model characterizes any chosen equational theory. -/
theorem theory_semantic_iff (E : EquationalTheory (typedSyntax Φ Γ))
    {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    E.Rel (eraseCarrier a) (eraseCarrier b) ↔
      ∀ M : ModelsOfTheory E, denote M.algebra a.2 = denote M.algebra b.2 := by
  rcases i with ⟨n, β, A⟩
  rcases a with ⟨a, da⟩
  rcases b with ⟨b, db⟩
  simpa only [syntaxIsInitial_to, fold, theoryCongruence, theoryPrecongruence,
    eraseCarrier, ModelsOfTheory] using
    (Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
      (syntaxIsInitial Φ Γ) (theoryCongruence E) (i := ⟨n, β, A⟩) ⟨a, da⟩ ⟨b, db⟩)

end Silmaril.Isotope.LetIter.LocallyNameless.Models

