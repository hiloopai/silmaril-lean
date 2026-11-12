module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Extensions
public import Silmaril.Logic.Metatheory.InferenceSystemCat.PropSystems

@[expose] public section

/-!
# Theories as inference systems

The conclusion of a theory judgment records a sort and two terms of that sort.
Theory morphisms translate the sort and both terms. This restriction is stronger
than an arbitrary inference-system morphism: an arbitrary map on pairs need not
arise by translating each term separately.
-/

namespace Silmaril.Logic.Metatheory
open Silmaril.Logic.Metatheory

open CategoryTheory InferenceSystemCat

universe u v w x y z

namespace RefinementTheory

variable {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}

/-- A closed theory is a proposition-valued inference system on term pairs. -/
def toInferenceSystem (R : RefinementTheory S) : PropSystems.{max u v} where
  Conclusion := S.Judgment
  Derivation a := R.Rel a.2.1 a.2.2

/-- A theory translation is an existing `InferenceMorphism`, including when
source and target syntax have different universes. At equal universes this is
definitionally an arrow of `PropSystems`. -/
def Hom.toInferenceMorphism {R : RefinementTheory S} {Q : RefinementTheory T}
    (f : R.Hom Q) :
    InferenceMorphism (PropSystems.Tag R.toInferenceSystem)
      (PropSystems.Tag Q.toInferenceSystem)
      R.toInferenceSystem.Conclusion Q.toInferenceSystem.Conclusion where
  map := f.toTranslation.judgment
  mapDerivation := f.preserves

@[simp] theorem Hom.toInferenceMorphism_map {R : RefinementTheory S}
    {Q : RefinementTheory T} (f : R.Hom Q) (i : S.Index) (a b : S.Term i) :
    f.toInferenceMorphism.map ⟨i, a, b⟩ = ⟨f.sort i, f.term a, f.term b⟩ := rfl

@[simp] theorem Hom.toInferenceMorphism_id (R : RefinementTheory S) :
    (Hom.id R).toInferenceMorphism = 𝟙 R.toInferenceSystem := rfl

@[simp] theorem Hom.toInferenceMorphism_comp {U : IndexedSyntax.{y, z}}
    {R : RefinementTheory S} {Q : RefinementTheory T} {P : RefinementTheory U}
    (g : Q.Hom P) (f : R.Hom Q) :
    (g.comp f).toInferenceMorphism = g.toInferenceMorphism.comp f.toInferenceMorphism := rfl

/-- Relation preservation and inference preservation coincide for a prescribed
pointwise syntax translation. -/
theorem sound_iff_inference (R : RefinementTheory S) (Q : RefinementTheory T)
    (f : S.Translation T) :
    (∀ {i} {a b : S.Term i}, R.Rel a b → Q.Rel (f.term a) (f.term b)) ↔
      ∃ h : InferenceMorphism (PropSystems.Tag R.toInferenceSystem)
        (PropSystems.Tag Q.toInferenceSystem)
        R.toInferenceSystem.Conclusion Q.toInferenceSystem.Conclusion,
        h.map = f.judgment := by
  constructor
  · intro h
    exact ⟨(Hom.mk f h).toInferenceMorphism, rfl⟩
  · rintro ⟨h, hh⟩ i a b hab
    have result := h.mapDerivation (a := ⟨i, a, b⟩) hab
    rw [hh] at result
    exact result

end RefinementTheory

namespace RefinementTheories

def toInferenceSystems : RefinementTheories.{u, v} ⥤ PropSystems.{max u v} where
  obj R := R.theory.toInferenceSystem
  map f := f.toInferenceMorphism

/-- Through the established coherent-system equivalence, theory proofs can be
represented in any proof universe. -/
def toCoherentSystems : RefinementTheories.{u, v} ⥤ CoherentSystems.{max u v, w} :=
  toInferenceSystems ⋙ PropSystems.toCoherent

def fixedInferenceSystems (S : IndexedSyntax.{u, v}) :
    RefinementTheory S ⥤ PropSystems.{max u v} := ofFixed S ⋙ toInferenceSystems

end RefinementTheories

namespace EquationalTheories

def toInferenceSystems : EquationalTheories.{u, v} ⥤ PropSystems.{max u v} :=
  toRefinement ⋙ RefinementTheories.toInferenceSystems

def toCoherentSystems : EquationalTheories.{u, v} ⥤ CoherentSystems.{max u v, w} :=
  toInferenceSystems ⋙ PropSystems.toCoherent

def fixedInferenceSystems (S : IndexedSyntax.{u, v}) :
    EquationalTheory S ⥤ PropSystems.{max u v} := ofFixed S ⋙ toInferenceSystems

end EquationalTheories

end Silmaril.Logic.Metatheory
