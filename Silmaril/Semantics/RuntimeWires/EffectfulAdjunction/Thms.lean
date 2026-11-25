module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Unit
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Universal

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Bundled

open CategoryTheory

universe u v

/-- The hom equivalence given by restricting to the generator map and extending
the resulting assignment. -/
def runtimeHomEquiv (G : EffectfulPolygraph.{u,max u v}) (X : Bundled.{u,v}) :
    (runtime G ⟶ X) ≃ (G ⟶ forget.obj X) where
  toFun := restrict
  invFun f := (assignment f).extension
  left_inv H := by exact Proofs.EffectfulAdjunction.restriction_left_inverse H
  right_inv f := by exact Proofs.EffectfulAdjunction.restriction_right_inverse f

theorem runtimeHomEquiv_natural (G : EffectfulPolygraph.{u,max u v})
    (X Y : Bundled.{u,v}) (K : X ⟶ Y) (H : runtime G ⟶ X) :
    runtimeHomEquiv G Y (H ≫ K) = runtimeHomEquiv G X H ≫ forget.map K := by
  let unit : G ⟶ forget.obj (runtime G) := generatorUnit G
  change unit ≫ forget.map (H ≫ K) = (unit ≫ forget.map H) ≫ forget.map K
  rw [Functor.map_comp, Category.assoc]

/-- The free strict effectful runtime model, functorial in the polygraph. -/
def free : EffectfulPolygraph.{u,max u v} ⥤ Bundled.{u,v} :=
  Adjunction.leftAdjointOfEquiv runtimeHomEquiv runtimeHomEquiv_natural

/-- Corollary 5.4. The free runtime category is left adjoint to forgetting to
the effectful polygraph of all pure and computation generators. -/
def freeAdjunction : free.{u,v} ⊣ forget.{u,v} :=
  Adjunction.adjunctionOfEquivLeft runtimeHomEquiv runtimeHomEquiv_natural

end Silmaril.RuntimeWires.StrictEffectful.Bundled
