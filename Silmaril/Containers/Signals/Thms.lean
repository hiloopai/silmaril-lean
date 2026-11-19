module

public import Silmaril.Containers.Signals.Defs

public section
namespace Silmaril.Containers.Signals

/-- Residual behaviour after a signal is evaluated from the *resulting state*, including its
handler, pending calls and effects. No fairness/progress assumption is smuggled into this law. -/
theorem execute_append (s : State) (before after : List Action) :
    execute s (before ++ after) = execute (execute s before) after := by
  simp [execute, List.foldl_append]

/-- Arrival and default termination are different: a masked or undelivered arrival is pending. -/
theorem arrival_pending (sig : Nat) :
    (step {} (.arrive sig)).pending = [sig] ∧ (step {} (.arrive sig)).stop = none :=
  ⟨rfl, rfl⟩

end Silmaril.Containers.Signals
