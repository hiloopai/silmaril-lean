module

public import Silmaril.Compiler.Native.Correctness.Execution.Defs
/-! Finite completion of the actual fetched-byte machine determines every
native observation. The result includes absence of stopped and divergent
observations, rather than only uniqueness among returning runs. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Execution
open Silmaril Silmaril.X86

/-- A successful run of the canonical feature machine is a path of the exact
retirement relation used by native correctness. -/
theorem run_reaches (exit : Word) (n : Nat) {a b : NativeState}
    (executed : Features.run Features.FeatureSet.baseline64
      [Features.floatExt, Features.Fpu.ext] exit n a = some b) :
    Relation.ReflTransGen (Retires exit) a b := by
  induction n generalizing a with
  | zero =>
    simp only [Features.run_zero] at executed
    cases executed
    exact .refl
  | succ n ih =>
    rw [Features.run_succ] at executed
    cases hs : Features.stepOpt Features.FeatureSet.baseline64
        [Features.floatExt, Features.Fpu.ext] exit a with
    | none => simp [hs] at executed
    | some mid =>
      simp only [hs, Option.bind_some] at executed
      have retired : Retires exit a mid := Features.stepOpt_eq_some_iff.mp hs
      exact (Relation.ReflTransGen.single retired).trans (ih executed)

/-- Removing one retirement preserves any later observation, including an
infinite execution. -/
theorem realises_after_retired {exit : Word} {initial next : NativeState}
    (retired : Retires exit initial next) {observation : Observation}
    (realised : Realises exit initial observation) : Realises exit next observation := by
  change step exit initial = .retired next at retired
  cases observation with
  | returned final =>
    show Realises exit next (.returned final)
    obtain ⟨before, reaches, returned⟩ := realised
    rcases reaches.cases_head with same | ⟨first, transition, rest⟩
    next =>
      subst before
      rw [retired] at returned
      contradiction
    next =>
      change step exit initial = .retired first at transition
      have same : first = next := Features.Outcome.retired.inj (transition.symm.trans retired)
      subst first
      exact ⟨before, rest, returned⟩
  | stopped state outcome =>
    show Realises exit next (.stopped state outcome)
    obtain ⟨reaches, stopped, nonretired, nonreturned⟩ := realised
    rcases reaches.cases_head with same | ⟨first, transition, rest⟩
    next =>
      subst state
      exact False.elim (nonretired next (stopped.symm.trans retired))
    next =>
      change step exit initial = .retired first at transition
      have same : first = next := Features.Outcome.retired.inj (transition.symm.trans retired)
      subst first
      exact ⟨rest, stopped, nonretired, nonreturned⟩
  | diverges =>
    obtain ⟨states, start, transitions⟩ := realised
    refine ⟨fun n => states (n + 1), ?_, fun n => transitions (n + 1)⟩
    have first : Retires exit (states 0) (states 1) := transitions 0
    change step exit (states 0) = .retired (states 1) at first
    rw [start, retired] at first
    exact (Features.Outcome.retired.inj first).symm

theorem realises_at_return {exit : Word} {initial final : NativeState}
    (returned : step exit initial = .returned final) {observation : Observation}
    (realised : Realises exit initial observation) : observation = .returned final := by
  cases observation with
  | returned other =>
    show Observation.returned other = .returned final
    obtain ⟨before, reaches, returnedOther⟩ := realised
    rcases reaches.cases_head with same | ⟨first, transition, rest⟩
    next =>
      subst before
      have same : final = other := Features.Outcome.returned.inj (returned.symm.trans returnedOther)
      exact congrArg Observation.returned same.symm
    next =>
      change step exit initial = .retired first at transition
      rw [returned] at transition
      contradiction
  | stopped state outcome =>
    show Observation.stopped state outcome = .returned final
    obtain ⟨reaches, stopped, nonretired, nonreturned⟩ := realised
    rcases reaches.cases_head with same | ⟨first, transition, rest⟩
    next =>
      subst state
      exact False.elim (nonreturned final (stopped.symm.trans returned))
    next =>
      change step exit initial = .retired first at transition
      rw [returned] at transition
      contradiction
  | diverges =>
    obtain ⟨states, start, transitions⟩ := realised
    have first : Retires exit (states 0) (states 1) := transitions 0
    change step exit (states 0) = .retired (states 1) at first
    rw [start, returned] at first
    contradiction

theorem realises_completed_iff {exit : Word} {initial before final : NativeState}
    (reaches : Relation.ReflTransGen (Retires exit) initial before)
    (returned : step exit before = .returned final) (observation : Observation) :
    Realises exit initial observation ↔ observation = .returned final := by
  constructor
  · refine Relation.ReflTransGen.head_induction_on
      (motive := fun state _ => Realises exit state observation → observation = .returned final)
      reaches (realises_at_return returned) ?_
    intro state next transition tail ih realised
    exact ih (realises_after_retired transition realised)
  · rintro rfl
    exact ⟨before, reaches, returned⟩

/-- A finite actual run followed by a return completely characterizes the
unbounded native observation relation from the same initial state. -/
theorem realises_iff_returned_of_run {exit : Word} {initial before final : NativeState}
    {count : Nat}
    (executed : Features.run Features.FeatureSet.baseline64
      [Features.floatExt, Features.Fpu.ext] exit count initial = some before)
    (returned : step exit before = .returned final) (observation : Observation) :
    Realises exit initial observation ↔ observation = .returned final :=
  realises_completed_iff (run_reaches exit count executed) returned observation

/-- The return value and the fixed native observation projection determine
all observations after a checked completion. -/
theorem observe_of_run {exit : Word} {initial before final : NativeState}
    {count : Nat}
    (executed : Features.run Features.FeatureSet.baseline64
      [Features.floatExt, Features.Fpu.ext] exit count initial = some before)
    (returned : step exit before = .returned final) {observation : Observation}
    (realised : Realises exit initial observation) :
    observe observation = observe (.returned final) :=
  congrArg observe ((realises_iff_returned_of_run executed returned observation).mp realised)

end Silmaril.Compiler.Native.Correctness.Execution
