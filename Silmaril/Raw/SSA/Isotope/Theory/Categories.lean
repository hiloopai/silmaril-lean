module

public import Silmaril.Raw.SSA.Isotope.Theory.Refinement
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Inference

/-!
# Categories of theories extending the let calculi

The fixed-syntax categories have inclusions as arrows. The ambient categories
allow translations of scopes/types and terms. Both have actual functors to the
existing inference-system categories. Erasure is a separate, generally
non-reflecting inference morphism from typed equations to raw equations.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetSeq.LocallyNameless

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε]

/-- Raw equational extensions of this calculus, ordered by inclusion. -/
abbrev RawEquationalExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).Extensions

/-- Raw directed theories must include every base equation in both directions. -/
abbrev RawRefinementExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Extensions

/-- This calculus as an object of the category allowing syntax translations. -/
def rawEquationalObject (pureEff : ε) : EquationalTheories :=
  ⟨rawSyntax ν Φ, rawEquationalTheory pureEff⟩

def rawRefinementObject (pureEff : ε) (R : RawRelation ν Φ) : RefinementTheories :=
  ⟨rawSyntax ν Φ, rawRefinementTheory pureEff R⟩

/-- A directed extension includes the equations, as an actual theory morphism. -/
def rawEquationsToRefinement (pureEff : ε) (R : RawRelation ν Φ) :
    (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Hom (rawRefinementTheory pureEff R) :=
  RefinementTheory.Hom.ofLE RawRefinement.equiv

/-- Forget the base-law constraint, then send the theory to its inference system. -/
def rawEquationalInference (pureEff : ε) :
    RawEquationalExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def rawRefinementInference (pureEff : ε) :
    RawRefinementExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exactly typed extensions of this calculus. -/
abbrev TypedEquationalExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).Extensions

abbrev TypedRefinementExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Extensions

def equationalObject (pureEff : ε) (Γ : Ctx ν τ) : EquationalTheories :=
  ⟨typedSyntax Φ Γ, equationalTheory pureEff Γ⟩

def refinementObject (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    RefinementTheories := ⟨typedSyntax Φ Γ, refinementTheory pureEff Γ R⟩

def equationsToRefinement (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Hom (refinementTheory pureEff Γ R) :=
  RefinementTheory.Hom.ofLE Refinement.equiv

def equationalInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedEquationalExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def refinementInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedRefinementExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

/-- Erasure is a theory morphism: it retains scopes and forgets exact typing. -/
def eraseTheory (pureEff : ε) (Γ : Ctx ν τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).Hom
      (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff) where
  sort i := i.depth
  term a := a.val
  preserves := Equiv.toRaw

/-- Erase both endpoints using the common heterogeneous theory/inference bridge. -/
abbrev eraseEquations (pureEff : ε) (Γ : Ctx ν τ) :=
  (eraseTheory (Φ := Φ) pureEff Γ).toInferenceMorphism

/-- The inference map erases exactly the endpoint typing evidence. -/
@[simp] theorem eraseEquations_map (pureEff : ε) (Γ : Ctx ν τ)
    (i : Silmaril.Isotope.Theory.TypingIndex τ) (a b : TypedTerm Φ Γ i) :
    (eraseEquations pureEff Γ).map ⟨i, a, b⟩ = ⟨i.depth, a.val, b.val⟩ := rfl

end Silmaril.Isotope.LetSeq.LocallyNameless

namespace Silmaril.Isotope.LetCase.LocallyNameless

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε]

/-- Raw equational extensions of this calculus, ordered by inclusion. -/
abbrev RawEquationalExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).Extensions

/-- Raw directed theories must include every base equation in both directions. -/
abbrev RawRefinementExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Extensions

/-- This calculus as an object of the category allowing syntax translations. -/
def rawEquationalObject (pureEff : ε) : EquationalTheories :=
  ⟨rawSyntax ν Φ, rawEquationalTheory pureEff⟩

def rawRefinementObject (pureEff : ε) (R : RawRelation ν Φ) : RefinementTheories :=
  ⟨rawSyntax ν Φ, rawRefinementTheory pureEff R⟩

/-- A directed extension includes the equations, as an actual theory morphism. -/
def rawEquationsToRefinement (pureEff : ε) (R : RawRelation ν Φ) :
    (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Hom (rawRefinementTheory pureEff R) :=
  RefinementTheory.Hom.ofLE RawRefinement.equiv

/-- Forget the base-law constraint, then send the theory to its inference system. -/
def rawEquationalInference (pureEff : ε) :
    RawEquationalExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def rawRefinementInference (pureEff : ε) :
    RawRefinementExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exactly typed extensions of this calculus. -/
abbrev TypedEquationalExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).Extensions

abbrev TypedRefinementExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Extensions

def equationalObject (pureEff : ε) (Γ : Ctx ν τ) : EquationalTheories :=
  ⟨typedSyntax Φ Γ, equationalTheory pureEff Γ⟩

def refinementObject (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    RefinementTheories := ⟨typedSyntax Φ Γ, refinementTheory pureEff Γ R⟩

def equationsToRefinement (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Hom (refinementTheory pureEff Γ R) :=
  RefinementTheory.Hom.ofLE Refinement.equiv

def equationalInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedEquationalExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def refinementInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedRefinementExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

/-- Erasure is a theory morphism: it retains scopes and forgets exact typing. -/
def eraseTheory (pureEff : ε) (Γ : Ctx ν τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).Hom
      (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff) where
  sort i := i.depth
  term a := a.val
  preserves := Equiv.toRaw

/-- Erase both endpoints using the common heterogeneous theory/inference bridge. -/
abbrev eraseEquations (pureEff : ε) (Γ : Ctx ν τ) :=
  (eraseTheory (Φ := Φ) pureEff Γ).toInferenceMorphism

/-- The inference map erases exactly the endpoint typing evidence. -/
@[simp] theorem eraseEquations_map (pureEff : ε) (Γ : Ctx ν τ)
    (i : Silmaril.Isotope.Theory.TypingIndex τ) (a b : TypedTerm Φ Γ i) :
    (eraseEquations pureEff Γ).map ⟨i, a, b⟩ = ⟨i.depth, a.val, b.val⟩ := rfl

end Silmaril.Isotope.LetCase.LocallyNameless

namespace Silmaril.Isotope.LetIter.LocallyNameless

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε]

/-- Raw equational extensions of this calculus, ordered by inclusion. -/
abbrev RawEquationalExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).Extensions

/-- Raw directed theories must include every base equation in both directions. -/
abbrev RawRefinementExtensions (pureEff : ε) :=
  (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Extensions

/-- This calculus as an object of the category allowing syntax translations. -/
def rawEquationalObject (pureEff : ε) : EquationalTheories :=
  ⟨rawSyntax ν Φ, rawEquationalTheory pureEff⟩

def rawRefinementObject (pureEff : ε) (R : RawRelation ν Φ) : RefinementTheories :=
  ⟨rawSyntax ν Φ, rawRefinementTheory pureEff R⟩

/-- A directed extension includes the equations, as an actual theory morphism. -/
def rawEquationsToRefinement (pureEff : ε) (R : RawRelation ν Φ) :
    (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff).toRefinementTheory.Hom (rawRefinementTheory pureEff R) :=
  RefinementTheory.Hom.ofLE RawRefinement.equiv

/-- Forget the base-law constraint, then send the theory to its inference system. -/
def rawEquationalInference (pureEff : ε) :
    RawEquationalExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def rawRefinementInference (pureEff : ε) :
    RawRefinementExtensions (ν := ν) (Φ := Φ) pureEff ⥤
      InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Exactly typed extensions of this calculus. -/
abbrev TypedEquationalExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).Extensions

abbrev TypedRefinementExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Extensions

def equationalObject (pureEff : ε) (Γ : Ctx ν τ) : EquationalTheories :=
  ⟨typedSyntax Φ Γ, equationalTheory pureEff Γ⟩

def refinementObject (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    RefinementTheories := ⟨typedSyntax Φ Γ, refinementTheory pureEff Γ R⟩

def equationsToRefinement (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory.Hom (refinementTheory pureEff Γ R) :=
  RefinementTheory.Hom.ofLE Refinement.equiv

def equationalInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedEquationalExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  EquationalTheory.Extensions.inclusion _ ⋙ EquationalTheories.fixedInferenceSystems _

def refinementInference (pureEff : ε) (Γ : Ctx ν τ) :
    TypedRefinementExtensions (Φ := Φ) pureEff Γ ⥤ InferenceSystemCat.PropSystems :=
  RefinementTheory.Extensions.inclusion _ ⋙ RefinementTheories.fixedInferenceSystems _

/-- Erasure is a theory morphism: it retains scopes and forgets exact typing. -/
def eraseTheory (pureEff : ε) (Γ : Ctx ν τ) :
    (equationalTheory (Φ := Φ) pureEff Γ).Hom
      (rawEquationalTheory (ν := ν) (Φ := Φ) pureEff) where
  sort i := i.depth
  term a := a.val
  preserves := Equiv.toRaw

/-- Erase both endpoints using the common heterogeneous theory/inference bridge. -/
abbrev eraseEquations (pureEff : ε) (Γ : Ctx ν τ) :=
  (eraseTheory (Φ := Φ) pureEff Γ).toInferenceMorphism

/-- The inference map erases exactly the endpoint typing evidence. -/
@[simp] theorem eraseEquations_map (pureEff : ε) (Γ : Ctx ν τ)
    (i : Silmaril.Isotope.Theory.TypingIndex τ) (a b : TypedTerm Φ Γ i) :
    (eraseEquations pureEff Γ).map ⟨i, a, b⟩ = ⟨i.depth, a.val, b.val⟩ := rfl

end Silmaril.Isotope.LetIter.LocallyNameless

