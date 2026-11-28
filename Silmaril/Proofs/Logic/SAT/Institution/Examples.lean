module

public import Silmaril.Logic.SAT.Institution.Thms

public section

namespace Silmaril.Proofs.Logic.SAT.Institution

open Silmaril.Logic.SAT.Institution Silmaril.Logic.ManyValued

theorem identification_counterexample :
    let F : Problem Bool := [[⟨false, true⟩, ⟨true, false⟩]]
    let f : Bool → Unit := fun _ => ()
    ¬ Function.Injective f ∧
      F.superEval (reduct f (fun _ => none)) = none ∧
      (F.rename f).superEval (fun _ => none) = some true ∧
      (F.rename f).evalK3 (fun _ => K3.unknown) = K3.unknown ∧
      (F.rename f).evalK3Option (fun _ => none) = none := by
  dsimp only
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro hf
    have h : false = true := hf rfl
    exact Bool.noConfusion h
  · apply (Problem.superEval_eq_none _ _).2
    have hc (t : TotalValuation Bool) : Completes (fun _ => none) t :=
      fun _ _ h => nomatch h
    exact ⟨⟨fun _ => true, hc _, rfl⟩, ⟨id, hc _, rfl⟩⟩
  · apply (Problem.superEval_eq_some _ _ _).2
    intro t _
    cases h : t () <;> simp [Problem.rename, Literal.rename, Problem.eval, h]

end Silmaril.Proofs.Logic.SAT.Institution
