module

public import Silmaril.Calculi.LambdaCube.Hets.Defs

@[expose] public section

namespace Silmaril.Proofs.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution Silmaril.Calculi.LambdaCube

namespace RestrictionGraph

variable {top : Corner} (N : Semantics top)

theorem path_modelExpansive {c d : (Silmaril.Calculi.LambdaCube.RestrictionGraph.graph N).Idx}
    (p : Quiver.Path c d) : (Silmaril.Calculi.LambdaCube.RestrictionGraph.graph N).PathModelExpansive p := by
  induction p with
  | nil => trivial
  | cons p e ih => exact ⟨ih, fun _ X => ⟨X, rfl⟩⟩

end RestrictionGraph

end Silmaril.Proofs.Calculi.LambdaCube
