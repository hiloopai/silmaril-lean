module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Generated
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace Silmaril.Logic.Metatheory

open CategoryTheory

universe u v w x y z

/-- A refinement-preserving map, with an explicit translation of syntax. -/
structure RefinementTheory.Hom {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}
    (R : RefinementTheory S) (Q : RefinementTheory T) extends S.Translation T where
  preserves : ∀ {i} {a b : S.Term i}, R.Rel a b → Q.Rel (term a) (term b)

namespace RefinementTheory.Hom

variable {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}
  {U : IndexedSyntax.{y, z}}
  {R : RefinementTheory S} {Q : RefinementTheory T} {P : RefinementTheory U}

@[ext] theorem ext {f g : R.Hom Q} (h : f.toTranslation = g.toTranslation) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (R : RefinementTheory S) : R.Hom R where
  toTranslation := IndexedSyntax.Translation.id S
  preserves h := h

def comp (g : Q.Hom P) (f : R.Hom Q) : R.Hom P where
  toTranslation := g.toTranslation.comp f.toTranslation
  preserves h := g.preserves (f.preserves h)

/-- A fixed-syntax theory inclusion is an identity-on-terms morphism. -/
def ofLE {Q : RefinementTheory S} (h : R ≤ Q) : R.Hom Q where
  toTranslation := IndexedSyntax.Translation.id S
  preserves := h

/-- Extend sound primitive rules to the generated theory. -/
def fromGenerated (base : S.Relation) (Q : RefinementTheory T)
    (f : S.Translation T) (hf : f.Contextual)
    (hbase : ∀ {i} {a b : S.Term i}, base a b → Q.Rel (f.term a) (f.term b)) :
    (generated S base).Hom Q where
  toTranslation := f
  preserves := (generated_le_iff base (Q.pullback f hf)).2 hbase

end RefinementTheory.Hom

/-- Equational-theory maps use the same relation-preserving translations. -/
abbrev EquationalTheory.Hom {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}
    (R : EquationalTheory S) (Q : EquationalTheory T) :=
  RefinementTheory.Hom R.toRefinementTheory Q.toRefinementTheory

/-- Soundness of generators extends to an equational-theory morphism. -/
def EquationalTheory.Hom.fromGenerated {S : IndexedSyntax.{u, v}}
    {T : IndexedSyntax.{w, x}} (base : S.Relation) (Q : EquationalTheory T)
    (f : S.Translation T) (hf : f.Contextual)
    (hbase : ∀ {i} {a b : S.Term i}, base a b → Q.Rel (f.term a) (f.term b)) :
    (EquationalTheory.generated S base).Hom Q where
  toTranslation := f
  preserves := (EquationalTheory.generated_le_iff base (Q.pullback f hf)).2 hbase

/-- Refinement theories allowing both the syntax and its theory to vary. -/
structure RefinementTheories where
  carrier : IndexedSyntax.{u, v}
  theory : RefinementTheory carrier

namespace RefinementTheories

instance : Category RefinementTheories.{u, v} where
  Hom R Q := R.theory.Hom Q.theory
  id R := RefinementTheory.Hom.id R.theory
  comp f g := g.comp f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- Include the thin category of extensions on one syntax in the ambient category. -/
def ofFixed (S : IndexedSyntax.{u, v}) : RefinementTheory S ⥤ RefinementTheories.{u, v} where
  obj R := ⟨S, R⟩
  map h := RefinementTheory.Hom.ofLE (leOfHom h)

end RefinementTheories

/-- Equational theories allowing the syntax and the equations to vary. -/
structure EquationalTheories where
  carrier : IndexedSyntax.{u, v}
  theory : EquationalTheory carrier

namespace EquationalTheories

instance : Category EquationalTheories.{u, v} where
  Hom R Q := R.theory.Hom Q.theory
  id R := RefinementTheory.Hom.id R.theory.toRefinementTheory
  comp f g := g.comp f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

def ofFixed (S : IndexedSyntax.{u, v}) : EquationalTheory S ⥤ EquationalTheories.{u, v} where
  obj R := ⟨S, R⟩
  map h := RefinementTheory.Hom.ofLE (leOfHom h)

/-- Every equational theory is a refinement theory with symmetric judgments. -/
def toRefinement : EquationalTheories.{u, v} ⥤ RefinementTheories.{u, v} where
  obj R := ⟨R.carrier, R.theory.toRefinementTheory⟩
  map f := f

end EquationalTheories

namespace RefinementTheories

/-- A translation preserving refinement also preserves mutual refinement. -/
def equationalCore : RefinementTheories.{u, v} ⥤ EquationalTheories.{u, v} where
  obj R := ⟨R.carrier, R.theory.equationalCore⟩
  map f := {
    toTranslation := f.toTranslation
    preserves := fun h => ⟨f.preserves h.1, f.preserves h.2⟩ }

/-- Equational maps into mutual refinement are exactly refinement maps out of
an equational source. No invertibility of the term translation is required. -/
def coreHomEquiv (E : EquationalTheories.{u, v}) (R : RefinementTheories.{u, v}) :
    (EquationalTheories.toRefinement.obj E ⟶ R) ≃ (E ⟶ equationalCore.obj R) where
  toFun f := {
    toTranslation := f.toTranslation
    preserves := fun h => ⟨f.preserves h, f.preserves (E.theory.symm h)⟩ }
  invFun f := {
    toTranslation := f.toTranslation
    preserves := fun h => (f.preserves h).1 }
  left_inv _ := RefinementTheory.Hom.ext rfl
  right_inv _ := RefinementTheory.Hom.ext rfl

/-- Mutual refinement is right adjoint to including equational theories. -/
def coreAdjunction : EquationalTheories.toRefinement.{u, v} ⊣ equationalCore :=
  Adjunction.mkOfHomEquiv {
    homEquiv := coreHomEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

end RefinementTheories

end Silmaril.Logic.Metatheory
