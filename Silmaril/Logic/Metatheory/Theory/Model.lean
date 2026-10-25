module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Data.Quot
public import Mathlib.CategoryTheory.Functor.FullyFaithful

@[expose] public section

/-!
# Operation algebras and initial quotient models

The category's morphisms preserve every many-sorted operation. They do not
include a preferred interpretation or a quotient factorization. Starting with
a free syntax algebra, a compatible equivalence gives a quotient algebra that
is initial among algebras validating its equations.

Validity refers to equations under the unique fold from the chosen syntax
algebra. Thus these are models of an algebra presentation, including its named
generators. Universal laws on arbitrary non-denoting semantic elements or
additional categorical structure are not part of this interface.
-/

namespace Silmaril.Logic.Metatheory.TheoryModel

open CategoryTheory CategoryTheory.Limits

universe u v w x y

/-- A surjective change of representatives gives the same quotient when it
preserves and reflects the identifying relation. This permits removing typing
derivation data without choosing inverse derivations in each concrete calculus. -/
noncomputable def quotientEquivOfSurjective {α : Type x} {β : Type y}
    (r : Setoid α) (s : Setoid β) (f : α → β) (hf : Function.Surjective f)
    (hr : ∀ a b, r.r a b ↔ s.r (f a) (f b)) : Quotient r ≃ Quotient s := by
  refine Equiv.ofBijective (Quotient.map f (fun a b h => (hr a b).1 h)) ⟨?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b => exact fun h => Quotient.sound ((hr a b).2 (Quotient.exact h))
  · intro b
    induction b using Quotient.inductionOn with
    | h b =>
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨Quotient.mk _ a, rfl⟩

@[simp] theorem quotientEquivOfSurjective_mk {α : Type x} {β : Type y}
    (r : Setoid α) (s : Setoid β) (f : α → β) (hf : Function.Surjective f)
    (hr : ∀ a b, r.r a b ↔ s.r (f a) (f b)) (a : α) :
    quotientEquivOfSurjective r s f hf hr (Quotient.mk _ a) = Quotient.mk _ (f a) := rfl

/-- Finitary operations with a result sort and one sort for each argument. -/
structure Signature (I : Type u) where
  Op : I → Type v
  arity : {i : I} → Op i → Nat
  argSort : {i : I} → (o : Op i) → Fin (arity o) → I

/-- A many-sorted algebra interprets all operation symbols. -/
structure Algebra {I : Type u} (Sig : Signature.{u, v} I) where
  Carrier : I → Type w
  op : {i : I} → (o : Sig.Op i) →
    ((j : Fin (Sig.arity o)) → Carrier (Sig.argSort o j)) → Carrier i

namespace Algebra

variable {I : Type u} {Sig : Signature.{u, v} I}

/-- Relations compare elements in a common carrier sort. -/
abbrev Relation (A : Algebra.{u, v, w} Sig) :=
  {i : I} → A.Carrier i → A.Carrier i → Prop

/-- Compatibility is shared by equational and directed presentations. -/
abbrev Compatible (A : Algebra.{u, v, w} Sig) (R : A.Relation) :=
  ∀ {i : I} (o : Sig.Op i)
    (a b : (j : Fin (Sig.arity o)) → A.Carrier (Sig.argSort o j)),
    (∀ j, R (a j) (b j)) → R (A.op o a) (A.op o b)

/-- Algebra homomorphisms preserve all constructors, including constants.
Source and target carriers may live in different universes; the categorical
instance below fixes one carrier universe. -/
structure Hom (A : Algebra.{u, v, w} Sig) (B : Algebra.{u, v, x} Sig) where
  map : {i : I} → A.Carrier i → B.Carrier i
  comm : ∀ {i : I} (o : Sig.Op i) (args : (j : Fin (Sig.arity o)) → A.Carrier (Sig.argSort o j)),
    map (A.op o args) = B.op o (fun j => map (args j))

@[ext] theorem Hom.ext {A : Algebra.{u, v, w} Sig} {B : Algebra.{u, v, x} Sig}
    {f g : Hom A B}
    (h : ∀ {i : I} (a : A.Carrier i), f.map a = g.map a) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : @f = @g := by funext i a; exact h a
      cases hfg
      rfl

def Hom.id (A : Algebra.{u, v, w} Sig) : Hom A A where
  map a := a
  comm _ _ := rfl

def Hom.comp {A : Algebra.{u, v, w} Sig} {B : Algebra.{u, v, x} Sig}
    {C : Algebra.{u, v, y} Sig} (g : Hom B C) (f : Hom A B) : Hom A C where
  map a := g.map (f.map a)
  comm o args := by rw [f.comm, g.comm]

instance : Category (Algebra.{u, v, w} Sig) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp _ := Hom.ext fun _ => rfl
  comp_id _ := Hom.ext fun _ => rfl
  assoc _ _ _ := Hom.ext fun _ => rfl

@[simp] theorem id_map (A : Algebra.{u, v, w} Sig) {i : I} (a : A.Carrier i) :
    (𝟙 A : A ⟶ A).map a = a := rfl

@[simp] theorem comp_map {A B C : Algebra.{u, v, w} Sig} (f : A ⟶ B) (g : B ⟶ C)
    {i : I} (a : A.Carrier i) : (f ≫ g).map a = g.map (f.map a) := rfl

end Algebra

variable {I : Type u} {Sig : Signature.{u, v} I}

/-- Equations must be preserved when replacing all arguments of an operation. -/
structure Congruence (A : Algebra.{u, v, w} Sig) where
  Rel : A.Relation
  equivalence : ∀ i : I, Equivalence (@Rel i)
  compatible : A.Compatible Rel

namespace Congruence

variable {A : Algebra.{u, v, w} Sig}

@[ext] theorem ext {E F : Congruence A}
    (h : ∀ {i : I} (a b : A.Carrier i), E.Rel a b ↔ F.Rel a b) : E = F := by
  cases E with
  | mk e he ce =>
    cases F with
    | mk f hf cf =>
      have hef : @e = @f := by funext i a b; exact propext (h a b)
      cases hef
      rfl

instance : PartialOrder (Congruence A) where
  le E F := ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel a b
  le_refl _ := fun h => h
  le_trans _ _ _ h k := fun p => k (h p)
  le_antisymm _ _ h k := ext fun _ _ => ⟨h, k⟩

def setoid (E : Congruence A) (i : I) : Setoid (A.Carrier i) where
  r := E.Rel
  iseqv := E.equivalence i

/-- Equations validated by an algebra interpretation form a congruence. -/
def kernel {B : Algebra.{u, v, w} Sig} (f : A ⟶ B) : Congruence A where
  Rel a b := f.map a = f.map b
  equivalence _ := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  compatible o a b h := by
    change f.map (A.op o a) = f.map (A.op o b)
    rw [f.comm, f.comm]
    exact congrArg (B.op o) (funext h)

end Congruence

variable {A : Algebra.{u, v, w} Sig}

/-- The quotient operation is independent of representatives by compatibility. -/
noncomputable def quotient (E : Congruence A) : Algebra.{u, v, w} Sig where
  Carrier i := Quotient (E.setoid i)
  op o args := Quotient.mk _ (A.op o (fun j => (args j).out))

/-- The constructor-preserving projection to congruence classes. -/
noncomputable def quotientMap (E : Congruence A) : A ⟶ quotient E where
  map a := Quotient.mk _ a
  comm o args := by
    apply Quotient.sound
    apply E.compatible
    intro j
    apply (E.equivalence _).symm
    exact @Quotient.exact _ (E.setoid _) _ _
      (Quotient.out_eq (Quotient.mk (E.setoid _) (args j)))

/-- Equality in the quotient is precisely the presented relation. -/
theorem quotientMap_eq_iff (E : Congruence A) {i : I} (a b : A.Carrier i) :
    (quotientMap E).map a = (quotientMap E).map b ↔ E.Rel a b :=
  by
  change Quotient.mk (E.setoid i) a = Quotient.mk (E.setoid i) b ↔ E.Rel a b
  exact ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem quotientMap_surjective (E : Congruence A) (i : I) :
    Function.Surjective (@(quotientMap E).map i) := by
  intro q
  exact ⟨q.out, Quotient.out_eq q⟩

/-- Descend an operation-preserving interpretation that respects the equations. -/
noncomputable def quotientDesc (E : Congruence A) {B : Algebra.{u, v, w} Sig}
    (f : A ⟶ B) (hf : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → f.map a = f.map b) :
    quotient E ⟶ B where
  map := Quotient.lift (fun a => f.map a) (fun _ _ h => hf h)
  comm o args := by
    change f.map (A.op o (fun j => (args j).out)) =
      B.op o (fun j => Quotient.lift (fun a => f.map a) (fun _ _ h => hf h) (args j))
    rw [f.comm]
    congr 1
    funext j
    conv_rhs => rw [← Quotient.out_eq (args j)]
    rfl

@[simp] theorem quotientMap_desc (E : Congruence A) {B : Algebra.{u, v, w} Sig}
    (f : A ⟶ B) (hf : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → f.map a = f.map b) :
    quotientMap E ≫ quotientDesc E f hf = f := Algebra.Hom.ext fun _ => rfl

theorem quotientDesc_unique (E : Congruence A) {B : Algebra.{u, v, w} Sig}
    (f g : quotient E ⟶ B) (h : quotientMap E ≫ f = quotientMap E ≫ g) : f = g := by
  apply Algebra.Hom.ext
  intro i q
  obtain ⟨a, rfl⟩ := quotientMap_surjective E i q
  exact congrArg (fun h : A ⟶ B => h.map a) h

/-- Actual operation algebras satisfying the equations under the unique fold
from the free syntax algebra. All algebra homomorphisms are allowed as arrows. -/
structure Models (hA : IsInitial A) (E : Congruence A) where
  algebra : Algebra.{u, v, w} Sig
  sound : ∀ {i : I} {a b : A.Carrier i},
    E.Rel a b → (hA.to algebra).map a = (hA.to algebra).map b

namespace Models

variable {hA : IsInitial A} {E : Congruence A}

instance : Category (Models hA E) where
  Hom M N := M.algebra ⟶ N.algebra
  id M := 𝟙 M.algebra
  comp f g := f ≫ g

/-- Forget only satisfaction of the equations. -/
def forget : Models hA E ⥤ Algebra.{u, v, w} Sig where
  obj M := M.algebra
  map f := f

instance : (forget (hA := hA) (E := E)).Faithful where
  map_injective h := h

instance : (forget (hA := hA) (E := E)).Full where
  map_surjective f := ⟨f, rfl⟩

end Models

/-- The quotient syntax is itself a model of the equations. -/
noncomputable def quotientModel (hA : IsInitial A) (E : Congruence A) : Models hA E where
  algebra := quotient E
  sound h := by
    have hq : hA.to (quotient E) = quotientMap E := hA.hom_ext _ _
    rw [hq]
    exact Quotient.sound h

/-- Interpret congruence classes using the unique fold of the original syntax. -/
noncomputable def quotientModelDesc (hA : IsInitial A) (E : Congruence A)
    (M : Models hA E) : quotientModel hA E ⟶ M :=
  quotientDesc E (hA.to M.algebra) M.sound

noncomputable instance quotientModelUnique (hA : IsInitial A) (E : Congruence A)
    (M : Models hA E) : Unique (quotientModel hA E ⟶ M) where
  default := quotientModelDesc hA E M
  uniq f := quotientDesc_unique E f (quotientModelDesc hA E M) (hA.hom_ext _ _)

/-- The universal property is initiality in the operation-algebra model category. -/
noncomputable def quotientIsInitial (hA : IsInitial A) (E : Congruence A) :
    IsInitial (quotientModel hA E) := IsInitial.ofUnique _

noncomputable instance (hA : IsInitial A) (E : Congruence A) : HasInitial (Models hA E) :=
  (quotientIsInitial hA E).hasInitial

/-- The quotient model witnesses completeness: equations valid in every model
are exactly the equations used to form the quotient. -/
theorem semantic_iff (hA : IsInitial A) (E : Congruence A)
    {i : I} (a b : A.Carrier i) :
    E.Rel a b ↔ ∀ M : Models hA E,
      (hA.to M.algebra).map a = (hA.to M.algebra).map b := by
  constructor
  · intro h M
    exact M.sound h
  · intro h
    have hq := h (quotientModel hA E)
    have hf : hA.to (quotient E) = quotientMap E := hA.hom_ext _ _
    change (hA.to (quotient E)).map a = (hA.to (quotient E)).map b at hq
    rw [hf] at hq
    exact (quotientMap_eq_iff E a b).1 hq

/-- Algebra homomorphisms commute with the unique interpretation of free syntax. -/
theorem fold_naturality (hA : IsInitial A) {B C : Algebra.{u, v, w} Sig}
    (f : B ⟶ C) {i : I} (a : A.Carrier i) :
    f.map ((hA.to B).map a) = (hA.to C).map a :=
  congrArg (fun k : A ⟶ C => k.map a) (hA.hom_ext (hA.to B ≫ f) (hA.to C))

end Silmaril.Logic.Metatheory.TheoryModel
