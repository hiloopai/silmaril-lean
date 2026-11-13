module

public import Silmaril.Cerberus.Core.Run.Defs

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

/-- A reported ending is the actual final control state. Fuel exhaustion has
no ending; this lemma never treats a finite prefix as termination. -/
theorem runWith_ending (choice : Nat) (file : Program) (labels : Labels)
    (fuel : Nat) (start : State) (outcome : Outcome)
    (ended : (runWith choice file labels fuel start).ending = some outcome) :
    (runWith choice file labels fuel start).finalState.control = .halt outcome := by
  induction fuel generalizing start with
  | zero => cases ended
  | succ fuel ih =>
    show (runWith choice file labels (fuel + 1) start).finalState.control = .halt outcome
    cases selected : stepWith choice file labels start with
    | step transition =>
      have restEnded :
          (runWith choice file labels fuel transition.after).ending = some outcome := by
        simpa only [runWith, selected] using ended
      simpa only [runWith, selected] using ih transition.after restEnded
    | ended actual halt =>
      have same : actual = outcome := by
        simpa only [runWith, selected, Option.some.injEq] using ended
      simpa only [runWith, selected, same] using halt

/-- The default runner is one schedule of the genuine Core LTS. -/
theorem run_ending (file : Program) (labels : Labels) (fuel : Nat)
    (start : State) (outcome : Outcome)
    (ended : (run file labels fuel start).ending = some outcome) :
    (run file labels fuel start).finalState.control = .halt outcome :=
  runWith_ending 0 file labels fuel start outcome ended

end Silmaril.Cerberus.Core.Dynamics
