module

public import Silmaril.Calculi.LambdaCube.PER.CubeMorphisms.Defs
import Silmaril.Proofs.Calculi.LambdaCube.PER.CubeMorphisms

@[expose] public section

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemF

open CategoryTheory

/-- The Fω parametric semantics, restricted to λ2, implies the System F
parametric semantics: every System F decoding is an Fω decoding, and the PER
(`interp_ofF`) and relational (`rinterp_ofF`) interpretations agree on it. -/
theorem paramSat_of_omega (M : CombAlg.{0}) (j : PTSJudgment)
    (h : SystemFOmega.ParamSat M j) : ParamSat M j :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.CubeMorphisms.paramSat_of_omega M j h

/-- The same, as a statement about the two semantics of the λ2 corner. -/
theorem paramSemantics_of_omega (X : Discrete CombAlg.{0}) (j : PTSJudgment)
    (h : (SystemFOmega.paramSemantics.restrict SystemFOmega.systemF_le_systemFOmega).sat X j) :
    paramSemantics.sat X j :=
  paramSat_of_omega X.as j h


end Silmaril.Calculi.LambdaCube.PERModel.SystemF
