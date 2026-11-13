module

public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Logic.Institution.Hets.StructuredSpec

@[expose] public section
namespace Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths
open CategoryTheory Silmaril.Logic.Institution
universe u₀ v₀ u v w m₁ m₂

/-- The actual flattened corridor has model expansion when every edge does. -/
theorem corridor_modelExpansive
    (L : LogicGraph.{u₀,v₀,u,v,w,m₁,m₂}) {a b : L.Idx}
    (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign) :
    Corridor.ModelExpansive ((IndexedCoInst.flat L.indexed).map
      (IndexedCoInst.lift L.indexed (L.pathHom p) S)) := by
  rw [IndexedCoInst.flat_map_lift]
  exact L.modelExpansive_path p hp S

end Silmaril.Proofs.Logic.Institution.Hets.StructuredPaths
