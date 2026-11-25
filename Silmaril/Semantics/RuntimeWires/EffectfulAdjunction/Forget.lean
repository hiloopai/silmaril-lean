module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.ForgetMap
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Forget

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Bundled

open CategoryTheory

universe u v

/-- The forgetful functor in Corollary 5.4. Edges are all typed arrows of the
chosen pure category and the computation category at the corresponding words. -/
def forget : Bundled.{u,v} ⥤ EffectfulPolygraph.{u,max u v} where
  obj := polygraph
  map H := forgetMap H
  map_id X := by exact Proofs.EffectfulAdjunction.forget_id X
  map_comp H K := by exact Proofs.EffectfulAdjunction.forget_comp H K

end Silmaril.RuntimeWires.StrictEffectful.Bundled
