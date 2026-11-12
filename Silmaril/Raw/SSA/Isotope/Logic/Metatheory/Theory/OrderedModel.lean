module

public import Silmaril.Logic.Metatheory.Theory.Model
public import Mathlib.Order.Antisymmetrization

@[expose] public section

/-!
# Ordered algebraic models and their initial refinement quotient

An ordered model has actual many-sorted operations, each monotone in all its
arguments. Morphisms preserve these operations and order. The quotient of a
free algebra by mutual refinement is initial among partial-order algebras
validating the refinement relation. This is an algebraic universal property,
not merely initiality in a category of relations.
-/

namespace Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {I : Type u} {Sig : Signature.{u, v} I}

/-- A reflexive transitive relation respected by all algebra operations. -/
structure CompatiblePreorder (A : Algebra.{u, v, w} Sig) where
  Rel : A.Relation
  refl : ∀ {i} (a : A.Carrier i), Rel a a
  trans : ∀ {i} {a b c : A.Carrier i}, Rel a b → Rel b c → Rel a c
  compatible : A.Compatible Rel

/-- An algebra whose carriers are partial orders and operations are monotone. -/
structure OrderedAlgebra (Sig : Signature.{u, v} I) extends Algebra.{u, v, w} Sig where
  order : ∀ i, PartialOrder (Carrier i)
  monotone_op : ∀ {i} (o : Sig.Op i)
    (a b : (j : Fin (Sig.arity o)) → Carrier (Sig.argSort o j)),
    (∀ j, @LE.le _ (order (Sig.argSort o j)).toLE (a j) (b j)) →
      @LE.le _ (order i).toLE (op o a) (op o b)

attribute [instance] OrderedAlgebra.order

namespace OrderedAlgebra

/-- A monotone algebra homomorphism, preserving every operation. -/
structure Hom (A B : OrderedAlgebra.{u, v, w} Sig) where
  toHom : Algebra.Hom A.toAlgebra B.toAlgebra
  monotone : ∀ i, Monotone (fun a : A.Carrier i => toHom.map a)

@[ext] theorem Hom.ext {A B : OrderedAlgebra.{u, v, w} Sig} {f g : Hom A B}
    (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Hom.id (A : OrderedAlgebra.{u, v, w} Sig) : Hom A A where
  toHom := Algebra.Hom.id A.toAlgebra
  monotone _ := monotone_id

def Hom.comp {A B C : OrderedAlgebra.{u, v, w} Sig} (g : Hom B C) (f : Hom A B) : Hom A C where
  toHom := Algebra.Hom.comp g.toHom f.toHom
  monotone i := (g.monotone i).comp (f.monotone i)

instance : Category (OrderedAlgebra.{u, v, w} Sig) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp _ := Hom.ext (Algebra.Hom.ext fun _ => rfl)
  comp_id _ := Hom.ext (Algebra.Hom.ext fun _ => rfl)
  assoc _ _ _ := Hom.ext (Algebra.Hom.ext fun _ => rfl)

/-- Forget the order while preserving the actual algebra operations. -/
def forget : OrderedAlgebra.{u, v, w} Sig ⥤ Algebra.{u, v, w} Sig where
  obj := toAlgebra
  map f := f.toHom

end OrderedAlgebra


variable {A : Algebra.{u, v, w} Sig}

namespace CompatiblePreorder

/-- Mutual refinement is an operation congruence. -/
def equationalCore (R : CompatiblePreorder A) : Congruence A where
  Rel a b := R.Rel a b ∧ R.Rel b a
  equivalence _ := ⟨fun a => ⟨R.refl a, R.refl a⟩, And.symm,
    fun h k => ⟨R.trans h.1 k.1, R.trans k.2 h.2⟩⟩
  compatible o a b h :=
    ⟨R.compatible o a b (fun j => (h j).1), R.compatible o b a (fun j => (h j).2)⟩

/-- The source carriers form preorders before quotienting. -/
@[instance_reducible] def preorder (R : CompatiblePreorder A) (i : I) : Preorder (A.Carrier i) where
  le := R.Rel
  le_refl := R.refl
  le_trans _ _ _ := R.trans

/-- The algebraic quotient by mutual refinement is precisely an antisymmetrization. -/
@[instance_reducible] def quotientOrder (R : CompatiblePreorder A) (i : I) :
    PartialOrder ((quotient R.equationalCore).Carrier i) where
  le := Quotient.lift₂ R.Rel (fun _ _ _ _ h k => propext
    ⟨fun p => R.trans h.2 (R.trans p k.1), fun p => R.trans h.1 (R.trans p k.2)⟩)
  le_refl a := Quotient.inductionOn a R.refl
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ => R.trans)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h k => Quotient.sound ⟨h, k⟩)

end CompatiblePreorder

/-- The quotient operations are monotone for the order induced by refinement. -/
noncomputable def orderedQuotient (R : CompatiblePreorder A) : OrderedAlgebra.{u, v, w} Sig where
  toAlgebra := quotient R.equationalCore
  order := R.quotientOrder
  monotone_op o a b h := by
    change R.Rel (A.op o (fun j => (a j).out)) (A.op o (fun j => (b j).out))
    apply R.compatible
    intro j
    have hj := h j
    rw [← Quotient.out_eq (a j), ← Quotient.out_eq (b j)] at hj
    exact hj

/-- The quotient records exactly the presented refinement relation. -/
theorem orderedQuotient_le_iff (R : CompatiblePreorder A) {i : I} (a b : A.Carrier i) :
    (show (orderedQuotient R).Carrier i from (quotientMap R.equationalCore).map a) ≤
      (quotientMap R.equationalCore).map b ↔ R.Rel a b := Iff.rfl

/-- An operation homomorphism preserving the presented preorder factors
through its antisymmetrization as a monotone operation homomorphism. -/
noncomputable def orderedQuotientDesc (R : CompatiblePreorder A)
    {B : OrderedAlgebra.{u, v, w} Sig} (f : A ⟶ B.toAlgebra)
    (hf : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → f.map a ≤ f.map b) :
    orderedQuotient R ⟶ B where
  toHom := quotientDesc R.equationalCore f (fun h => le_antisymm (hf h.1) (hf h.2))
  monotone i := by
    intro a b h
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b => exact hf h

@[simp] theorem orderedQuotientMap_desc (R : CompatiblePreorder A)
    {B : OrderedAlgebra.{u, v, w} Sig} (f : A ⟶ B.toAlgebra)
    (hf : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → f.map a ≤ f.map b) :
    quotientMap R.equationalCore ≫ (orderedQuotientDesc R f hf).toHom = f :=
  quotientMap_desc R.equationalCore f (fun h => le_antisymm (hf h.1) (hf h.2))

/-- Factorization is unique among all monotone operation-preserving maps. -/
theorem orderedQuotientDesc_unique (R : CompatiblePreorder A)
    {B : OrderedAlgebra.{u, v, w} Sig} (f g : orderedQuotient R ⟶ B)
    (h : quotientMap R.equationalCore ≫ f.toHom = quotientMap R.equationalCore ≫ g.toHom) :
    f = g := OrderedAlgebra.Hom.ext (quotientDesc_unique R.equationalCore f.toHom g.toHom h)

/-- Partial-order algebras validating the presented directed theory under the
unique fold from a free syntax algebra. Arrows preserve all operations and order. -/
structure OrderedModels (hA : IsInitial A) (R : CompatiblePreorder A) where
  algebra : OrderedAlgebra.{u, v, w} Sig
  sound : ∀ {i : I} {a b : A.Carrier i},
    R.Rel a b → (hA.to algebra.toAlgebra).map a ≤ (hA.to algebra.toAlgebra).map b

namespace OrderedModels

variable {hA : IsInitial A} {R : CompatiblePreorder A}

instance : Category (OrderedModels hA R) where
  Hom M N := M.algebra ⟶ N.algebra
  id M := 𝟙 M.algebra
  comp f g := f ≫ g

/-- Forget satisfaction, retaining all ordered algebra operations. -/
def forget : OrderedModels hA R ⥤ OrderedAlgebra.{u, v, w} Sig where
  obj M := M.algebra
  map f := f

instance : (forget (hA := hA) (R := R)).Faithful where
  map_injective h := h

instance : (forget (hA := hA) (R := R)).Full where
  map_surjective f := ⟨f, rfl⟩

/-- Mutual refinement is equality in every partial-order model, yielding a
functor to the algebraic models of the equational core. -/
def toEquationalCore : OrderedModels hA R ⥤ Models hA R.equationalCore where
  obj M := {
    algebra := M.algebra.toAlgebra
    sound := fun h => le_antisymm (M.sound h.1) (M.sound h.2)
  }
  map f := f.toHom

end OrderedModels

/-- The antisymmetrized syntax validates every generated refinement. -/
noncomputable def orderedQuotientModel (hA : IsInitial A) (R : CompatiblePreorder A) :
    OrderedModels hA R where
  algebra := orderedQuotient R
  sound h := by
    have hq : hA.to (orderedQuotient R).toAlgebra = quotientMap R.equationalCore := hA.hom_ext _ _
    rw [hq]
    exact h

/-- The canonical model morphism interprets representatives by the free fold. -/
noncomputable def orderedQuotientModelDesc (hA : IsInitial A) (R : CompatiblePreorder A)
    (M : OrderedModels hA R) : orderedQuotientModel hA R ⟶ M :=
  orderedQuotientDesc R (hA.to M.algebra.toAlgebra) M.sound

noncomputable instance orderedQuotientModelUnique (hA : IsInitial A)
    (R : CompatiblePreorder A) (M : OrderedModels hA R) :
    Unique (orderedQuotientModel hA R ⟶ M) where
  default := orderedQuotientModelDesc hA R M
  uniq f := orderedQuotientDesc_unique R f (orderedQuotientModelDesc hA R M) (hA.hom_ext _ _)

/-- Initiality holds in the category of genuine ordered operation algebras. -/
noncomputable def orderedQuotientIsInitial (hA : IsInitial A) (R : CompatiblePreorder A) :
    IsInitial (orderedQuotientModel hA R) := IsInitial.ofUnique _

noncomputable instance (hA : IsInitial A) (R : CompatiblePreorder A) :
    HasInitial (OrderedModels hA R) := (orderedQuotientIsInitial hA R).hasInitial


/-- Refinement valid in every partial-order algebra of the presentation. -/
def SemanticallyRefines (hA : IsInitial A) (R : CompatiblePreorder A)
    {i : I} (a b : A.Carrier i) : Prop :=
  ∀ M : OrderedModels hA R,
    (hA.to M.algebra.toAlgebra).map a ≤ (hA.to M.algebra.toAlgebra).map b

/-- The antisymmetrized syntax is a complete ordered model: all-model validity
is exactly the presented compatible preorder. -/
theorem semanticallyRefines_iff (hA : IsInitial A) (R : CompatiblePreorder A)
    {i : I} (a b : A.Carrier i) : SemanticallyRefines hA R a b ↔ R.Rel a b := by
  constructor
  · intro h
    have hm := h (orderedQuotientModel hA R)
    have hq : hA.to (orderedQuotientModel hA R).algebra.toAlgebra =
        quotientMap R.equationalCore := hA.hom_ext _ _
    rw [hq] at hm
    exact hm
  · intro h M
    exact M.sound h

/-- Equality valid in every partial-order model is mutual refinement. -/
theorem semanticallyEqual_iff (hA : IsInitial A) (R : CompatiblePreorder A)
    {i : I} (a b : A.Carrier i) :
    (∀ M : OrderedModels hA R,
      (hA.to M.algebra.toAlgebra).map a = (hA.to M.algebra.toAlgebra).map b) ↔
      R.Rel a b ∧ R.Rel b a := by
  constructor
  · intro h
    have hm := h (orderedQuotientModel hA R)
    have hq : hA.to (orderedQuotientModel hA R).algebra.toAlgebra =
        quotientMap R.equationalCore := hA.hom_ext _ _
    rw [hq] at hm
    exact Quotient.exact hm
  · rintro ⟨h, k⟩ M
    exact le_antisymm (M.sound h) (M.sound k)

end Silmaril.Logic.Metatheory.TheoryModel
