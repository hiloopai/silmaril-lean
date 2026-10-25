module

public import Silmaril.Logic.Metatheory.InferenceMorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

@[expose] public section

/-!
# The category of inference systems

Objects bundle conclusions and their derivations. Morphisms translate both,
using `InferenceMorphism`. Derivations remain proof relevant: two morphisms with
the same conclusion map can still differ on proofs.

`of` packages any CSLib inference system. Its `PLift` lets proposition-valued
judgments and proof-relevant trees coexist in this category; `ULift` aligns
their universes. These wrappers add no derivations.
-/

namespace Silmaril.Logic.Metatheory

open Cslib.Logic CategoryTheory CategoryTheory.Limits

universe s t u v w r

/-- A type of conclusions equipped with a type of derivations for each one. -/
structure InferenceSystemCat where
  Conclusion : Type u
  Derivation : Conclusion → Type v

namespace InferenceSystemCat

/-- A distinct CSLib system tag for each bundled inference system. -/
structure Tag (S : InferenceSystemCat.{u, v}) where

instance (S : InferenceSystemCat.{u, v}) : InferenceSystem (Tag S) S.Conclusion where
  derivation := S.Derivation

instance : Category (InferenceSystemCat.{u, v}) where
  Hom S T := InferenceMorphism (Tag S) (Tag T) S.Conclusion T.Conclusion
  id _ := InferenceMorphism.id
  comp f g := g.comp f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- Extensionality includes the action on derivations, not just conclusions. -/
theorem hom_ext {S T : InferenceSystemCat.{u, v}} {f g : S ⟶ T}
    (conclusions : ∀ a, f.map a = g.map a)
    (derivations : ∀ a (d : S.Derivation a), HEq (f.mapDerivation d) (g.mapDerivation d)) :
    f = g := by
  cases f with
  | mk f df =>
    cases g with
    | mk g dg =>
      have hf : f = g := funext conclusions
      cases hf
      have hd : @df = @dg := by funext a d; exact eq_of_heq (derivations a d)
      cases hd
      rfl

theorem hom_congr_derivation {S T : InferenceSystemCat.{u, v}} {f g : S ⟶ T}
    (h : f = g) (a : S.Conclusion) (d : S.Derivation a) :
    HEq (f.mapDerivation d) (g.mapDerivation d) := by cases h; rfl

/-- Package an existing CSLib system, allowing an additional proof-universe lift. -/
def of (S : Type s) (α : Type u) [InferenceSystem.{s, u, v} S α] :
    InferenceSystemCat.{u, max v w} where
  Conclusion := α
  Derivation a := ULift.{w} (PLift (InferenceSystem.derivation S a))

/-- Packaging changes only proof representation, not which conclusions are derivable. -/
theorem of_derivable_iff (S : Type s) (α : Type u) [InferenceSystem.{s, u, v} S α]
    (a : α) :
    Nonempty ((of.{s, u, v, w} S α).Derivation a) ↔
      InferenceSystem.DerivableIn S a := by
  constructor
  · exact fun ⟨d⟩ => ⟨d.down.down⟩
  · exact fun ⟨d⟩ => ⟨⟨⟨d⟩⟩⟩

/-- A CSLib inference morphism gives a categorical arrow after aligning proof universes. -/
def ofMorphism {S : Type s} {T : Type t} {α β : Type u}
    [InferenceSystem.{s, u, v} S α] [InferenceSystem.{t, u, w} T β]
    (f : InferenceMorphism S T α β) :
    of.{s, u, v, w} S α ⟶ of.{t, u, w, v} T β where
  map := f.map
  mapDerivation d := ⟨⟨f.mapDerivation d.down.down⟩⟩

@[simp] theorem ofMorphism_map {S : Type s} {T : Type t} {α β : Type u}
    [InferenceSystem.{s, u, v} S α] [InferenceSystem.{t, u, w} T β]
    (f : InferenceMorphism S T α β) (a : α) : (ofMorphism f).map a = f a := rfl

/-- Within a fixed proof universe, packaging preserves identity maps. -/
@[simp] theorem ofMorphism_id (S : Type s) (α : Type u) [InferenceSystem.{s, u, v} S α] :
    ofMorphism (InferenceMorphism.id (S := S) (α := α)) = 𝟙 (of.{s, u, v, v} S α) := rfl

/-- Within a fixed proof universe, packaging preserves composition. -/
@[simp] theorem ofMorphism_comp {S : Type s} {T : Type t} {U : Type r} {α β γ : Type u}
    [InferenceSystem.{s, u, v} S α] [InferenceSystem.{t, u, v} T β]
    [InferenceSystem.{r, u, v} U γ]
    (g : InferenceMorphism T U β γ) (f : InferenceMorphism S T α β) :
    ofMorphism (g.comp f) = ofMorphism f ≫ ofMorphism g := rfl

/-- There are no conclusions in the initial inference system. -/
def empty : InferenceSystemCat.{u, v} where
  Conclusion := PEmpty
  Derivation _ := PEmpty

/-- The terminal inference system has one conclusion and exactly one derivation. -/
def trivial : InferenceSystemCat.{u, v} where
  Conclusion := PUnit
  Derivation _ := PUnit

/-- The unique translation out of the empty system. -/
def fromEmpty (S : InferenceSystemCat.{u, v}) : empty ⟶ S where
  map a := a.elim
  mapDerivation {a} _ := a.elim

/-- The unique translation into the trivial system. -/
def toTrivial (S : InferenceSystemCat.{u, v}) : S ⟶ trivial where
  map _ := PUnit.unit
  mapDerivation _ := PUnit.unit

theorem fromEmpty_unique {S : InferenceSystemCat.{u, v}} (f : empty ⟶ S) :
    f = fromEmpty S := by
  cases f with
  | mk f df =>
    have hf : f = (fromEmpty S).map := by funext a; exact a.elim
    cases hf
    have hd : @df = @(fromEmpty S).mapDerivation := by funext a; exact a.elim
    cases hd
    rfl

theorem toTrivial_unique {S : InferenceSystemCat.{u, v}} (f : S ⟶ trivial) :
    f = toTrivial S := by
  cases f with
  | mk f df =>
    have hf : f = (toTrivial S).map := by funext a; cases f a; rfl
    cases hf
    have hd : @df = @(toTrivial S).mapDerivation := by
      funext a d
      cases df d
      rfl
    cases hd
    rfl

instance (S : InferenceSystemCat.{u, v}) : Unique (empty ⟶ S) where
  default := fromEmpty S
  uniq := fromEmpty_unique

instance (S : InferenceSystemCat.{u, v}) : Unique (S ⟶ trivial) where
  default := toTrivial S
  uniq := toTrivial_unique

/-- The empty system is initial in Mathlib's categorical sense. -/
def emptyIsInitial : IsInitial (empty : InferenceSystemCat.{u, v}) :=
  IsInitial.ofUnique _

/-- The one-conclusion, one-derivation system is terminal. -/
def trivialIsTerminal : IsTerminal (trivial : InferenceSystemCat.{u, v}) :=
  IsTerminal.ofUnique _

instance : HasInitial (InferenceSystemCat.{u, v}) := emptyIsInitial.hasInitial

instance : HasTerminal (InferenceSystemCat.{u, v}) := trivialIsTerminal.hasTerminal

end InferenceSystemCat

end Silmaril.Logic.Metatheory
