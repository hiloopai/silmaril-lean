module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulExtension.Maps

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Assignment

open CategoryTheory Diagram Presentation

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

/-- The functor on computations obtained by applying the graded quotient interpreter
at the leftmost runtime boundary. -/
def computationExtension (F : T.Assignment G) : Computations G ⥤ C where
  obj := F.computationObject
  map f := F.computationMap f
  map_id X := by exact Proofs.EffectfulExtension.computation_id F X
  map_comp f g := by exact Proofs.EffectfulExtension.computation_comp F f g

end Silmaril.RuntimeWires.StrictEffectful.Assignment
