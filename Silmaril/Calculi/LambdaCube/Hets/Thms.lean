module

public import Silmaril.Calculi.LambdaCube.Hets.Defs
import Silmaril.Proofs.Calculi.LambdaCube.Hets

@[expose] public section

namespace Silmaril.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution

namespace RestrictionGraph

variable {top : Corner} (N : Semantics top)

/-- The satisfaction law uses the same raw PTS judgment on both sides. -/
theorem satisfaction {c d : Node top} (h : c.val ≤ d.val) (X : N.Model) (j : PTSJudgment) :
    (semantics N d).sat X j ↔ (semantics N c).sat ((inclusion N h).reduct.obj X) j :=
  (inclusion N h).satisfaction X j

/-- Every target model already is a source model; no expansion premise is needed. -/
theorem comorphism_modelExpansive {c d : Node top} (h : c.val ≤ d.val) :
    (comorphism N h).ModelExpansive := fun _ X => ⟨X, rfl⟩

/-- Semantic consequence is preserved and reflected in the shared semantics.
This is not reflection of derivability between the corner typing calculi. -/
theorem entails_iff {c d : Node top} (_h : c.val ≤ d.val)
    (Γ : Set PTSJudgment) (j : PTSJudgment) :
    (semantics N c).room.Entails Γ j ↔ (semantics N d).room.Entails Γ j := Iff.rfl

/-- Every graph path supports the library's Hets consequence-borrowing theorem. -/
theorem path_modelExpansive {c d : (graph N).Idx} (p : Quiver.Path c d) :
    (graph N).PathModelExpansive p :=
  Silmaril.Proofs.Calculi.LambdaCube.RestrictionGraph.path_modelExpansive N p

/-- The actual composite institution comorphism of any path has model expansion. -/
theorem composite_modelExpansive {c d : (graph N).Idx} (p : Quiver.Path c d) :
    (IndexedCoInst.coHom (graph N).indexed ((graph N).pathHom p)).ModelExpansive :=
  (graph N).modelExpansive_path p (path_modelExpansive N p)

end RestrictionGraph

namespace PERGraph

/-- The nondependent square commutes as institution comorphisms, including
sentence translation and model reducts, rather than only as edge labels. -/
theorem diamond :
    IndexedCoInst.coHom graph.indexed (graph.pathHom viaSystemF) =
      IndexedCoInst.coHom graph.indexed (graph.pathHom viaOmega) := rfl

/-- Restricting Fω to the System F corner implies the native System F
parametric satisfaction predicate. No converse is asserted. -/
theorem nativeSystemF_of_restriction (X : Discrete PERModel.CombAlg.{0}) (j : PTSJudgment)
    (h : (RestrictionGraph.semantics PERModel.SystemFOmega.paramSemantics systemF).sat X j) :
    PERModel.SystemF.paramSemantics.sat X j :=
  PERModel.SystemF.paramSemantics_of_omega X j h

end PERGraph

end Silmaril.Calculi.LambdaCube
