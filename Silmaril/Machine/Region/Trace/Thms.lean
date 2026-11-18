module

public import Silmaril.Machine.Trace
public import Silmaril.Semantics.Region.Simulation.Defs
import Silmaril.Proofs.Machine.Region.Trace

/-! # Finite traces at Region boundaries

These results forget the cut on a finite first exit, not on arbitrary runs.
They do not establish `Machine.Trace.Refines`, which matches every step.
-/

public section

namespace Silmaril.Semantics.Region

open Silmaril.Machine

/-- Forget the cut, keeping the entire list of observations and both endpoints. -/
theorem FirstExit.toTraceRuns {State Lab Event Stop : Type*} {system : TransitionSystem State Lab Event Stop}
    {support : Lab → Prop} {initial final : State} {events : List Event}
    (run : FirstExit system support initial events final) :
    Trace.Runs system.step initial events final := Region.TraceProofs.firstExitRuns run

/-- Match an admitted full first exit with a simple first exit. Both executions
give finite machine traces with literally the same events and related endpoints. -/
theorem Realizes.RefinesExits.matchTraceRuns {Small Full Lab Event SmallStop FullStop : Type*}
    {small : TransitionSystem Small Lab Event SmallStop} {full : TransitionSystem Full Lab Event FullStop}
    {map : Realizes small full} {admit : Small → Prop} {admitFull : Full → Prop} {support : Lab → Prop}
    (refines : map.RefinesExits admit admitFull support) {initial final : Full} {events : List Event}
    (admitted : admitFull initial) (run : FirstExit full support initial events final) :
    Trace.Runs full.step initial events final ∧
      ∃ before after, admit before ∧ map.relates before initial ∧ map.relates after final ∧
        FirstExit small support before events after ∧ Trace.Runs small.step before events after := by
  obtain ⟨before, after, ok, left, matched, right⟩ := refines initial events final admitted run
  exact ⟨run.toTraceRuns, before, after, ok, left, right, matched, matched.toTraceRuns⟩

end Silmaril.Semantics.Region
