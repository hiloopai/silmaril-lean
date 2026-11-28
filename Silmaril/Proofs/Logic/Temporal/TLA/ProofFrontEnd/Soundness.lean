module

public import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Defs

namespace Silmaril.Proofs.Logic.Temporal.TLA.ProofFrontEnd

open Silmaril.Logic.Temporal.TLA.ProofFrontEnd
open Silmaril.Logic.Temporal.TLA.DataElab

universe u

private theorem holds_of_termEq {V : Type u} {premise goal : Proposition}
    {model : Interpretation V} {valuation : Valuation V}
    (termEq : premise.term = goal.term) (holds : premise.holds model valuation) :
    goal.holds model valuation := by
  unfold Proposition.holds CheckedExpr.eval at holds ⊢
  rw [← termEq]
  exact holds

public theorem exact_sound {V : Type u} {obligation : Obligation}
    (certificate : ExactCertificate obligation) (model : Interpretation V) :
    obligation.Valid model := by
  induction certificate with
  | assumption premise inScope termEq =>
    intro valuation assumptions _
    exact holds_of_termEq termEq (assumptions premise inScope)
  | hypothesis premise inScope termEq =>
    intro valuation _ hypotheses
    exact holds_of_termEq termEq (hypotheses premise inScope)
  | theoremDecl earlier _ _ inScope closed termEq proved =>
    intro valuation assumptions _
    have holds := proved valuation (fun fact member => assumptions fact (inScope member))
      (fun hypothesis member => by simp [closed] at member)
    exact holds_of_termEq termEq holds
  | applyRule earlier _ _ inScope _ termEq proved premisesProved =>
    intro valuation assumptions hypotheses
    have holds := proved valuation (fun fact member => assumptions fact (inScope member))
      (fun premise member =>
        Obligation.holds_of_valid_withGoal (premisesProved premise member) assumptions hypotheses)
    exact holds_of_termEq termEq holds

end Silmaril.Proofs.Logic.Temporal.TLA.ProofFrontEnd
