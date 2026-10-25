module

public import Silmaril.Calculi.LambdaCube.Hets.Thms

@[expose] public section

namespace Silmaril.Calculi.LambdaCube.PERGraph

open CategoryTheory Silmaril.Logic.Institution

/-- The concrete parametric model family contains a nondegenerate algebra. -/
theorem model_nontrivial : PERModel.termModel.k ≠ PERModel.termModel.s :=
  PERModel.termModel_k_ne_s

/-- The polymorphic identity judgment is satisfied in the nondegenerate term
model; soundness is supplied by the proved System F-to-Fω PTS inclusion. -/
theorem polymorphicIdentity_termModel :
    PERModel.SystemFOmega.paramSemantics.sat (Discrete.mk PERModel.termModel)
      (.typing [] Corner.polymorphicIdentity Corner.polymorphicIdentityType) :=
  PERModel.SystemFOmega.paramSemantics.sound
    (j := .typing [] Corner.polymorphicIdentity Corner.polymorphicIdentityType)
    (Corner.typing_inclusion PERModel.SystemFOmega.systemF_le_systemFOmega Corner.systemF_identity)
    (Discrete.mk PERModel.termModel)

/-- The two-edge route through System F is an actual model-expansive
institution comorphism; `graph.entails_lift_path_iff` can borrow consequence along it. -/
theorem viaSystemF_modelExpansive :
    (IndexedCoInst.coHom graph.indexed (graph.pathHom viaSystemF)).ModelExpansive :=
  RestrictionGraph.composite_modelExpansive PERModel.SystemFOmega.paramSemantics viaSystemF

/-- The alternative route through the constructor-only corner has the same guarantee. -/
theorem viaOmega_modelExpansive :
    (IndexedCoInst.coHom graph.indexed (graph.pathHom viaOmega)).ModelExpansive :=
  RestrictionGraph.composite_modelExpansive PERModel.SystemFOmega.paramSemantics viaOmega

end Silmaril.Calculi.LambdaCube.PERGraph
