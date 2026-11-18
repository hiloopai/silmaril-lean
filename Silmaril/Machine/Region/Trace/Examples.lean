module

import Silmaril.Machine.Region.Trace.Thms

namespace Silmaril.Machine.Region

open Silmaril.Semantics.Region

private def emits : TransitionSystem Nat Nat Nat Empty where
  pc := id
  step before events after :=
    (before = 0 ∧ events = [1, 2] ∧ after = 1) ∨ (before = 1 ∧ events = [3] ∧ after = 2)
  halt _ _ := False

example : Trace.Runs emits.step 0 [1, 2, 3] 2 :=
  (show FirstExit emits (· < 2) 0 ([1, 2] ++ [3]) 2 from
    .step (by decide) (.inl ⟨rfl, rfl, rfl⟩)
      (.leave (by decide) (.inr ⟨rfl, rfl, rfl⟩) (by decide))).toTraceRuns

end Silmaril.Machine.Region
