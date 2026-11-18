module

public import Silmaril.Machine.Trace
public import Silmaril.Semantics.Region.Semantic.Defs

public section

namespace Silmaril.Machine.Region.TraceProofs

open Silmaril.Semantics.Region

theorem firstExitRuns {State Lab Event Stop : Type*} {system : TransitionSystem State Lab Event Stop}
    {support : Lab → Prop} {initial final : State} {events : List Event}
    (run : FirstExit system support initial events final) :
    Trace.Runs system.step initial events final := by
  induction run with
  | leave _ edge _ => simpa only [List.append_nil] using Trace.Runs.cons edge (Trace.Runs.refl _)
  | step _ edge _ ih => exact .cons edge ih

end Silmaril.Machine.Region.TraceProofs
