module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Pure
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextCoherence
public import Mathlib.CategoryTheory.Monoidal.Transport

@[expose] public section

/-! # Pure model morphisms at the signature's chosen type constructors -/

namespace Silmaril.Isotope.Refinement.Models.SeqData

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A tag for the category of pure arrows at normalized signature types. -/
structure PureObject (M : SeqData.{u,v,w,r} τ Φ ε) where
  type : τ

instance pureCategory : Category M.PureObject where
  Hom A B := Denotation.PureHom M A.type B.type
  id A := ⟨M.identity A.type, M.identity_effect _ _⟩
  comp f g := ⟨M.compose f.1 g.1, M.compose_effect f.2 g.2⟩
  id_comp f := Subtype.ext (M.identity_compose f.1)
  comp_id f := Subtype.ext (M.compose_identity f.1)
  assoc f g h := Subtype.ext (M.compose_assoc f.1 g.1 h.1)

/-- The same pure arrows with the ambient category's original tensor objects. -/
abbrev RawPure := @EffectfulCategory.Pure τ M.category M.homOrder M.premonoidal M.symmetric ε _ M.effects

def pureForget : M.PureObject ⥤ M.RawPure := by
  letI := M.category
  letI := M.homOrder
  letI := M.premonoidal
  letI := M.symmetric
  exact { obj A := ⟨A.type⟩, map f := ⟨f.1, f.2⟩ }

instance pureForget_faithful : M.pureForget.Faithful where
  map_injective h := by
    let := M.category
    let := M.homOrder
    let := M.premonoidal
    let := M.symmetric
    exact Subtype.ext (congrArg (fun f => f.hom) h)

instance pureStruct : MonoidalCategoryStruct M.PureObject where
  tensorObj A B := ⟨product A.type B.type⟩
  tensorUnit := ⟨Silmaril.unit⟩
  whiskerLeft A _ _ f := ⟨M.left A.type f.1, M.left_effect _ f.2⟩
  whiskerRight f A := ⟨M.right f.1 A.type, M.right_effect _ f.2⟩
  tensorHom f g := ⟨M.tensor f.1 g.1, M.tensor_effect f.2 g.2⟩
  associator A B D :=
    { hom := ⟨M.associator A.type B.type D.type, M.associator_pure _ _ _⟩
      inv := ⟨M.associatorInv A.type B.type D.type, M.associatorInv_pure _ _ _⟩
      hom_inv_id := Subtype.ext (M.associator_hom_inv _ _ _)
      inv_hom_id := Subtype.ext (M.associator_inv_hom _ _ _) }
  leftUnitor A :=
    { hom := ⟨M.leftUnitor A.type, M.leftUnitor_pure _⟩
      inv := ⟨M.leftUnitorInv A.type, M.leftUnitorInv_pure _⟩
      hom_inv_id := Subtype.ext (M.leftUnitor_hom_inv _)
      inv_hom_id := Subtype.ext (M.leftUnitor_inv_hom _) }
  rightUnitor A :=
    { hom := ⟨M.rightUnitor A.type, M.rightUnitor_pure _⟩
      inv := ⟨M.rightUnitorInv A.type, M.rightUnitorInv_pure _⟩
      hom_inv_id := Subtype.ext (M.rightUnitor_hom_inv _)
      inv_hom_id := Subtype.ext (M.rightUnitor_inv_hom _) }

@[simp] theorem pure_tensorHom_val {A B D E : M.PureObject} (f : A ⟶ B) (g : D ⟶ E) :
    (f ⊗ₘ g).1 = M.tensor f.1 g.1 := rfl
@[simp] theorem pure_associator_val (A B D : M.PureObject) :
    (α_ A B D).hom.1 = M.associator A.type B.type D.type := rfl
@[simp] theorem pure_leftUnitor_val (A : M.PureObject) :
    (λ_ A).hom.1 = M.leftUnitor A.type := rfl
@[simp] theorem pure_rightUnitor_val (A : M.PureObject) :
    (ρ_ A).hom.1 = M.rightUnitor A.type := rfl

@[simp] theorem pure_whiskerLeft_val (A : M.PureObject) {B D : M.PureObject} (f : B ⟶ D) :
    (A ◁ f).1 = M.left A.type f.1 := rfl
@[simp] theorem pure_whiskerRight_val {A B : M.PureObject} (f : A ⟶ B) (D : M.PureObject) :
    (f ▷ D).1 = M.right f.1 D.type := rfl
@[simp] theorem pure_comp_val {A B D : M.PureObject} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).1 = M.compose f.1 g.1 := rfl
@[simp] theorem pure_associatorInv_val (A B D : M.PureObject) :
    (α_ A B D).inv.1 = M.associatorInv A.type B.type D.type := rfl
@[simp] theorem pure_leftUnitorInv_val (A : M.PureObject) :
    (λ_ A).inv.1 = M.leftUnitorInv A.type := rfl
@[simp] theorem pure_rightUnitorInv_val (A : M.PureObject) :
    (ρ_ A).inv.1 = M.rightUnitorInv A.type := rfl

/-- The tensor comparison maps are only the signature's object equalities. -/
def pureInducingData : Monoidal.InducingFunctorData M.pureForget := by
  letI := M.category
  letI := M.homOrder
  letI := M.premonoidal
  letI := M.symmetric
  refine
    { μIso := fun A B => WideSubcategory.isoMk (eqToIso (M.tensor_obj A.type B.type))
        (M.eqToHom_effect (M.tensor_obj A.type B.type) ⊥)
        (M.eqToHom_effect (M.tensor_obj A.type B.type).symm ⊥)
      εIso := WideSubcategory.isoMk (eqToIso M.tensor_unit)
        (M.eqToHom_effect M.tensor_unit ⊥) (M.eqToHom_effect M.tensor_unit.symm ⊥)
      whiskerLeft_eq := ?_
      whiskerRight_eq := ?_
      tensorHom_eq := ?_
      associator_eq := ?_
      leftUnitor_eq := ?_
      rightUnitor_eq := ?_ }
  · intro A B D f
    apply WideSubcategory.hom_ext
    rfl
  · intro A B f D
    apply WideSubcategory.hom_ext
    rfl
  · intro A B D E f g
    apply WideSubcategory.hom_ext
    simp [pureForget, tensor, right, left, compose, PremonoidalCategory.leftTensor,
      Category.assoc]
  · intro A B D
    apply WideSubcategory.hom_ext
    simp [pureForget, associator]
  · intro A
    apply WideSubcategory.hom_ext
    simp [pureForget, leftUnitor]
  · intro A
    apply WideSubcategory.hom_ext
    simp [pureForget, rightUnitor]

instance pureMonoidal : MonoidalCategory M.PureObject :=
  Monoidal.induced M.pureForget M.pureInducingData

instance pureForget_monoidal : M.pureForget.Monoidal :=
  Monoidal.fromInducedMonoidal M.pureForget M.pureInducingData

@[simp] theorem braiding_symmetry (A B : τ) :
    M.compose (M.braiding A B) (M.braiding B A) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, braiding, identity, Category.assoc]

def pureBraiding (A B : M.PureObject) : A ⊗ B ≅ B ⊗ A where
  hom := ⟨M.braiding A.type B.type, M.braiding_pure _ _⟩
  inv := ⟨M.braiding B.type A.type, M.braiding_pure _ _⟩
  hom_inv_id := Subtype.ext (M.braiding_symmetry _ _)
  inv_hom_id := Subtype.ext (M.braiding_symmetry _ _)

instance pureBraided : BraidedCategory M.PureObject := by
  letI := M.category
  letI := M.homOrder
  letI := M.premonoidal
  letI := M.symmetric
  refine BraidedCategory.ofFaithful M.pureForget M.pureBraiding ?_
  intro A B
  apply WideSubcategory.hom_ext
  change eqToHom (M.tensor_obj A.type B.type) ≫ M.braiding A.type B.type =
    (BraidedPremonoidalCategory.braiding A.type B.type).hom ≫ eqToHom (M.tensor_obj B.type A.type)
  simp [braiding]

instance pureSymmetric : SymmetricCategory M.PureObject where
  __ := M.pureBraided
  symmetry A B := Subtype.ext (M.braiding_symmetry A.type B.type)

@[simp] theorem pure_braiding_val (A B : M.PureObject) :
    (BraidedCategory.braiding A B).hom.1 = M.braiding A.type B.type := rfl

@[simp] theorem pure_middleSwap_val (A B D E : M.PureObject) :
    (MonoidalCategory.tensorμ A B D E).1 = M.middleSwap A.type B.type D.type E.type := rfl

end Silmaril.Isotope.Refinement.Models.SeqData
