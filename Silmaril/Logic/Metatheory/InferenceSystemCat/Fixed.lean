module

public import Silmaril.Logic.Metatheory.InferenceSystemCat
public import Mathlib.CategoryTheory.Functor.FullyFaithful

@[expose] public section

/-!
# Inference systems with a fixed type of conclusions

`Fixed α` retains the derivation family as data. Its arrows act on derivations
at each conclusion, without translating conclusions. This is a proof-relevant
category: existence of arrows will induce a separate derivability preorder.

The inclusion in `InferenceSystemCat` keeps `α` unchanged. It is faithful;
arbitrary ambient morphisms can change conclusions and therefore do not belong
to this fixed-conclusion category.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat

open CategoryTheory CategoryTheory.Limits

universe u v

/-- An inference system on the fixed conclusion type `α`. -/
structure Fixed (α : Type u) where
  Derivation : α → Type v

namespace Fixed

variable {α : Type u}

instance : Category (Fixed.{u, v} α) where
  Hom S T := ∀ a, S.Derivation a → T.Derivation a
  id _ := fun _ d => d
  comp f g := fun a d => g a (f a d)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_apply (S : Fixed.{u, v} α) (a : α) (d : S.Derivation a) :
    (𝟙 S) a d = d := rfl

@[simp] theorem comp_apply {S T U : Fixed.{u, v} α} (f : S ⟶ T) (g : T ⟶ U)
    (a : α) (d : S.Derivation a) : (f ≫ g) a d = g a (f a d) := rfl

/-- Forget that the conclusion type is fixed. -/
def toAmbient (S : Fixed.{u, v} α) : InferenceSystemCat.{u, v} where
  Conclusion := α
  Derivation := S.Derivation

/-- Include fixed-conclusion maps as ambient maps whose conclusion function is identity. -/
def inclusion : Fixed.{u, v} α ⥤ InferenceSystemCat.{u, v} where
  obj := toAmbient
  map f := { map := id, mapDerivation := fun {a} d => f a d }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem inclusion_map {S T : Fixed.{u, v} α} (f : S ⟶ T) (a : α) :
    (inclusion.map f).map a = a := rfl

@[simp] theorem inclusion_mapDerivation {S T : Fixed.{u, v} α} (f : S ⟶ T)
    (a : α) (d : S.Derivation a) :
    (inclusion.map f).mapDerivation d = f a d := rfl

instance : (inclusion : Fixed.{u, v} α ⥤ InferenceSystemCat.{u, v}).Faithful where
  map_injective := by
    intro S T f g h
    have hd := (InferenceMorphism.mk.inj h).2
    funext a d
    exact congrArg (fun k : {a : α} → S.Derivation a → T.Derivation a => k d)
      (eq_of_heq hd)

/-- There are no derivations, while the conclusion type remains `α`. -/
def empty : Fixed.{u, v} α where
  Derivation _ := PEmpty

/-- Every conclusion has exactly one derivation. -/
def trivial : Fixed.{u, v} α where
  Derivation _ := PUnit

/-- The unique map out of the empty derivation family. -/
def fromEmpty (S : Fixed.{u, v} α) : empty ⟶ S := fun _ d => d.elim

/-- The unique map into the family with one derivation at each conclusion. -/
def toTrivial (S : Fixed.{u, v} α) : S ⟶ trivial := fun _ _ => PUnit.unit

theorem fromEmpty_unique {S : Fixed.{u, v} α} (f : empty ⟶ S) :
    f = fromEmpty S := by
  funext a d
  exact d.elim

theorem toTrivial_unique {S : Fixed.{u, v} α} (f : S ⟶ trivial) :
    f = toTrivial S := by
  funext a d
  exact @Subsingleton.elim PUnit inferInstance _ _

instance (S : Fixed.{u, v} α) : Unique (empty ⟶ S) where
  default := fromEmpty S
  uniq := fromEmpty_unique

instance (S : Fixed.{u, v} α) : Unique (S ⟶ trivial) where
  default := toTrivial S
  uniq := toTrivial_unique

/-- Empty derivation fibers are initial among systems with the same conclusions. -/
def emptyIsInitial : IsInitial (empty : Fixed.{u, v} α) := IsInitial.ofUnique _

/-- Singleton derivation fibers are terminal among systems with the same conclusions. -/
def trivialIsTerminal : IsTerminal (trivial : Fixed.{u, v} α) := IsTerminal.ofUnique _

instance : HasInitial (Fixed.{u, v} α) := emptyIsInitial.hasInitial

instance : HasTerminal (Fixed.{u, v} α) := trivialIsTerminal.hasTerminal

end Fixed

end Silmaril.Logic.Metatheory.InferenceSystemCat
