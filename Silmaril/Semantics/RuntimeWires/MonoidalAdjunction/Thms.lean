module

public import Silmaril.Semantics.RuntimeWires.MonoidalAdjunction.Unit
import Silmaril.Proofs.Semantics.RuntimeWires.MonoidalAdjunction.Universal

@[expose] public section

namespace Silmaril.RuntimeWires.StrictMonoidal

open CategoryTheory

universe u v

/-- Extending the assignments of a polygraph map inverts restriction to generators. -/
def termsHomEquiv (G : Polygraph.{u,max u v}) (X : StrictMonoidal.{u,v}) :
    (terms G ⟶ X) ≃ (G ⟶ forget.obj X) where
  toFun := restrict
  invFun f := ⟨(interpretation f).functor (fun _ _ => False) False.elim,
    ((interpretation f).functor_extends _ False.elim).strict⟩
  left_inv F := Subtype.ext (by exact Proofs.MonoidalAdjunction.restrict_left_inverse F)
  right_inv f := by exact Proofs.MonoidalAdjunction.restrict_right_inverse f

theorem termsHomEquiv_natural (G : Polygraph.{u,max u v}) (X Y : StrictMonoidal.{u,v})
    (K : X ⟶ Y) (H : terms G ⟶ X) :
    termsHomEquiv G Y (H ≫ K) = termsHomEquiv G X H ≫ forget.map K := by
  change generatorUnit G ≫ forget.map (H ≫ K) = (generatorUnit G ≫ forget.map H) ≫ forget.map K
  rw [Functor.map_comp, Category.assoc]

/-- Lemma 3.4 on algebraic diagrams. The presented strict monoidal categories
are functorial in the generating polygraph. -/
def free : Polygraph.{u,max u v} ⥤ StrictMonoidal.{u,v} :=
  Adjunction.leftAdjointOfEquiv termsHomEquiv termsHomEquiv_natural

/-- The algebraic adjunction in Theorem 3.6. Its domain is the polygraph
category and the left adjoint uses the quotient of typed monoidal terms. -/
def freeAdjunction : free.{u,v} ⊣ forget.{u,v} :=
  Adjunction.adjunctionOfEquivLeft termsHomEquiv termsHomEquiv_natural

end Silmaril.RuntimeWires.StrictMonoidal
