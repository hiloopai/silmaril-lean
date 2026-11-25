module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulExtension

open CategoryTheory Diagram Presentation
open DiagramInterpretation
open scoped MonoidalCategory SameArrow

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

theorem map_computation (X Y : Computations G) (f : X ⟶ Y) :
    F.computationMap f ≈ₐ F.evaluate (show X.boundary ⟶ Y.boundary from f)
      (Nat.le_of_eq (StrictEffectful.Assignment.computation_count X)) :=
  transport_eq _ _ _

theorem computation_id (X : Computations G) :
    F.computationMap (𝟙 X) = 𝟙 (F.computationObject X) :=
  ((map_computation F X X (𝟙 X)).trans
    ((SameArrow.of_eq (F.evaluate_id X.boundary _)).trans
      (.id (F.computation_boundary X)))).eq

theorem computation_comp {X Y Z : Computations G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.computationMap (f ≫ g) = F.computationMap f ≫ F.computationMap g :=
  ((map_computation F X Z (f ≫ g)).trans
    ((SameArrow.of_eq (F.evaluate_comp (show X.boundary ⟶ Y.boundary from f)
      (show Y.boundary ⟶ Z.boundary from g) _ (Nat.le_of_eq
        (StrictEffectful.Assignment.computation_count Y)))).trans
      ((map_computation F X Y f).symm.comp (map_computation F Y Z g).symm))).eq

end Silmaril.RuntimeWires.Proofs.EffectfulExtension
