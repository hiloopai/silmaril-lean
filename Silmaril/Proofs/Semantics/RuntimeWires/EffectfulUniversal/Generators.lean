module

public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulUniversal.Tensor

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal

open CategoryTheory MonoidalCategory Presentation RuntimeCoherence Position
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

@[expose] def leftmost (A : Computations G) : Position G := ⟨[], A.word⟩

@[expose] def pastOne (x : G.Obj) : Position G := ⟨[x], []⟩

theorem split_leftmost_hom (A : Computations G) :
    (leftmost A).split.hom ≈ₐ 𝟙 A.boundary := by
  exact ((split_hom (leftmost A)).trans
    (crossing_nil.whiskerRight (X := valueWord A.word) rfl)).trans
      (.of_eq (id_whiskerRight _ _))

theorem split_leftmost_inv (A : Computations G) :
    (leftmost A).split.inv ≈ₐ 𝟙 A.boundary :=
  (show (leftmost A).split.hom ≈ₐ (Iso.refl A.boundary).hom from split_leftmost_hom A).inv

theorem normalize_leftmost {A B : Computations G} (f : A ⟶ B) :
    underlying (normalize (X := leftmost A) (Y := leftmost B) (underlying f)) ≈ₐ underlying f := by
  have e := (split_leftmost_hom A).comp ((SameArrow.refl (underlying f)).comp (split_leftmost_inv B))
  exact e.trans (.of_eq ((Category.id_comp _).trans (Category.comp_id _)))

theorem split_pastOne_hom (x : G.Obj) :
    (pastOne x).split.hom ≈ₐ (crossing x).hom := by
  let y := (crossing x).hom
  have el : (crossingWord (G := G) [x]).hom ≈ₐ y := by
    refine (crossing_cons x []).trans ?_
    have e := (crossing_nil (G := G)).whiskerLeft (X := valueWord [x]) rfl
    rw [whiskerLeft_id] at e
    refine ((whiskerRight_unit y).join_congr e _ (by runtime_word)).trans ?_
    exact SameArrow.join_id rfl
  exact (split_hom (pastOne x)).trans ((el.whiskerRight rfl).trans (whiskerRight_unit y))

theorem split_pastOne_inv (x : G.Obj) :
    (pastOne x).split.inv ≈ₐ (crossing x).inv :=
  (split_pastOne_hom x).inv

theorem normalize_crossRight (x : G.Obj) :
    underlying (normalize (X := leftmost ⟨[x]⟩) (Y := pastOne x) (crossing x).hom) ≈ₐ
      𝟙 (⟨[x]⟩ : Computations G).boundary := by
  let A : Computations G := ⟨[x]⟩
  have e := (split_leftmost_hom A).comp
    ((SameArrow.refl (crossing x).hom).comp (split_pastOne_inv x))
  exact e.trans (.of_eq ((Category.id_comp _).trans (crossing x).hom_inv_id))

theorem normalize_crossLeft (x : G.Obj) :
    underlying (normalize (X := pastOne x) (Y := leftmost ⟨[x]⟩) (crossing x).inv) ≈ₐ
      𝟙 (⟨[x]⟩ : Computations G).boundary := by
  let A : Computations G := ⟨[x]⟩
  have e := (split_pastOne_hom x).comp
    ((SameArrow.refl (crossing x).inv).comp (split_leftmost_inv A))
  exact e.trans (.of_eq ((congrArg ((crossing x).hom ≫ ·) (Category.comp_id _)).trans
    (crossing x).hom_inv_id))

end Silmaril.RuntimeWires.Proofs.EffectfulUniversal
