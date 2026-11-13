module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Structures
public import Silmaril.Raw.SSA.Isotope.CategoryTheory.Premonoidal.Monoidal

@[expose] public section

/-! # The symmetric monoidal category of pure computations

Pure centrality supplies interchange. This construction therefore keeps the
ambient effectful category premonoidal while allowing monoidal coherence for
pure context maps.
-/

namespace Silmaril.Isotope.Refinement.Models.EffectfulCategory

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

universe u v w
variable {C : Type u} [Category.{v} C] [∀ A B : C, PartialOrder (A ⟶ B)]
variable [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
variable {ε : Type w} [EffectSystem ε]
variable (M : EffectfulCategory C ε)

/-- All objects, with just the morphisms of bottom effect. -/
abbrev Pure := M.Subcategory ⊥

instance pureMonoidalStruct : MonoidalCategoryStruct M.Pure where
  tensorObj A B := ⟨A.obj ⊗ B.obj⟩
  whiskerLeft A _ _ f := ⟨A.obj ◁ f.hom, M.whiskerLeft _ f.property⟩
  whiskerRight f B := ⟨f.hom ▷ B.obj, M.whiskerRight _ f.property⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator A B D := WideSubcategory.isoMk (α_ A.obj B.obj D.obj)
    (M.associator _ _ _) (M.associator_inv _ _ _)
  leftUnitor A := WideSubcategory.isoMk (λ_ A.obj) (M.leftUnitor _) (M.leftUnitor_inv _)
  rightUnitor A := WideSubcategory.isoMk (ρ_ A.obj) (M.rightUnitor _) (M.rightUnitor_inv _)
  tensorHom f g := ⟨f.hom ⋉ g.hom,
    M.comp (M.whiskerRight _ f.property) (M.whiskerLeft _ g.property)⟩

theorem pure_isCentral {A B : M.Pure} (f : A ⟶ B) : PremonoidalCategory.IsCentral f := by
  constructor
  · intro D E g
    apply WideSubcategory.hom_ext
    exact (M.pure_central f.property).1 g.hom
  · intro D E g
    apply WideSubcategory.hom_ext
    exact (M.pure_central f.property).2 g.hom

instance purePremonoidal : PremonoidalCategory M.Pure where
  __ := M.pureMonoidalStruct
  tensorHom_def _ _ := rfl
  whiskerLeft_id A B := WideSubcategory.hom_ext _ (PremonoidalCategory.whiskerLeft_id A.obj B.obj)
  whiskerLeft_comp A _ _ _ f g := WideSubcategory.hom_ext _ (PremonoidalCategory.whiskerLeft_comp A.obj f.hom g.hom)
  id_whiskerRight A B := WideSubcategory.hom_ext _ (PremonoidalCategory.id_whiskerRight A.obj B.obj)
  comp_whiskerRight f g D := WideSubcategory.hom_ext _ (PremonoidalCategory.comp_whiskerRight f.hom g.hom D.obj)
  associator_central _ _ _ := M.pure_isCentral _
  leftUnitor_central _ := M.pure_isCentral _
  rightUnitor_central _ := M.pure_isCentral _
  associator_naturality_left f B D := WideSubcategory.hom_ext _
    (PremonoidalCategory.associator_naturality_left f.hom B.obj D.obj)
  associator_naturality_middle A _ _ f D := WideSubcategory.hom_ext _
    (PremonoidalCategory.associator_naturality_middle A.obj f.hom D.obj)
  associator_naturality_right A B _ _ f := WideSubcategory.hom_ext _
    (PremonoidalCategory.associator_naturality_right A.obj B.obj f.hom)
  leftUnitor_naturality f := WideSubcategory.hom_ext _ (PremonoidalCategory.leftUnitor_naturality f.hom)
  rightUnitor_naturality f := WideSubcategory.hom_ext _ (PremonoidalCategory.rightUnitor_naturality f.hom)
  pentagon A B D E := WideSubcategory.hom_ext _ (PremonoidalCategory.pentagon A.obj B.obj D.obj E.obj)
  triangle A B := WideSubcategory.hom_ext _ (PremonoidalCategory.triangle A.obj B.obj)

/-- Pure morphisms satisfy full interchange, so their tensor is bifunctorial. -/
instance pureMonoidal : MonoidalCategory M.Pure :=
  PremonoidalCategory.monoidalOfCentral M.pure_isCentral

@[simp] theorem pure_tensorHom_hom {A B D E : M.Pure} (f : A ⟶ B) (g : D ⟶ E) :
    (f ⊗ₘ g).hom = f.hom ⋉ g.hom := rfl
@[simp] theorem pure_whiskerLeft_hom (A : M.Pure) {B D : M.Pure} (f : B ⟶ D) :
    (A ◁ f).hom = A.obj ◁ f.hom := rfl
@[simp] theorem pure_whiskerRight_hom {A B : M.Pure} (f : A ⟶ B) (D : M.Pure) :
    (f ▷ D).hom = f.hom ▷ D.obj := rfl
@[simp] theorem pure_associator_hom (A B D : M.Pure) :
    (α_ A B D).hom.hom = (α_ A.obj B.obj D.obj).hom := rfl
@[simp] theorem pure_leftUnitor_hom (A : M.Pure) :
    (λ_ A).hom.hom = (λ_ A.obj).hom := rfl
@[simp] theorem pure_rightUnitor_hom (A : M.Pure) :
    (ρ_ A).hom.hom = (ρ_ A.obj).hom := rfl

instance pureSymmetric : SymmetricCategory M.Pure where
  braiding A B :=
    { hom := ⟨(BraidedPremonoidalCategory.braiding A.obj B.obj).hom, M.braiding _ _⟩
      inv := ⟨(BraidedPremonoidalCategory.braiding B.obj A.obj).hom, M.braiding _ _⟩
      hom_inv_id := WideSubcategory.hom_ext _ (SymmetricPremonoidalCategory.symmetry _ _)
      inv_hom_id := WideSubcategory.hom_ext _ (SymmetricPremonoidalCategory.symmetry _ _) }
  braiding_naturality_right A _ _ f := WideSubcategory.hom_ext _
    (BraidedPremonoidalCategory.naturality_right A.obj f.hom)
  braiding_naturality_left f D := WideSubcategory.hom_ext _
    (BraidedPremonoidalCategory.naturality_left f.hom D.obj)
  hexagon_forward A B D := WideSubcategory.hom_ext _
    (BraidedPremonoidalCategory.hexagon_forward A.obj B.obj D.obj)
  hexagon_reverse A B D := WideSubcategory.hom_ext _
    (BraidedPremonoidalCategory.hexagon_reverse A.obj B.obj D.obj)
  symmetry A B := WideSubcategory.hom_ext _ (SymmetricPremonoidalCategory.symmetry A.obj B.obj)

end Silmaril.Isotope.Refinement.Models.EffectfulCategory
