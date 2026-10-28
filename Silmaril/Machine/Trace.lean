module

public import Silmaril.Foundations.InfiniteTrace

/-! # Finite observable executions of nondeterministic machines

A transition emits a finite list of observations, possibly empty. Refinement
quantifies over every implementation transition; it cannot choose away an
unfavorable environment response. These finite-trace results make no progress
or fairness claim about a blocked operating-system interaction.
-/

@[expose] public section

namespace Silmaril.Machine.Trace

universe u v w

/-- A finite execution concatenates the observations of its actual transitions. -/
inductive Runs {State : Type u} {Event : Type v}
    (step : State → List Event → State → Prop) : State → List Event → State → Prop
  | refl (state) : Runs step state [] state
  | cons {initial next final events rest} :
      step initial events next → Runs step next rest final →
      Runs step initial (events ++ rest) final

namespace Runs

variable {State : Type u} {Event : Type v}
variable {step : State → List Event → State → Prop}

theorem single {initial final : State} {events : List Event}
    (transition : step initial events final) : Runs step initial events final := by
  simpa using Runs.cons transition (Runs.refl final)

theorem append {initial middle final : State} {first last : List Event}
    (firstRun : Runs step initial first middle) (suffix : Runs step middle last final) :
    Runs step initial (first ++ last) final := by
  induction firstRun with
  | refl => exact suffix
  | cons head _ ih => simpa only [List.append_assoc] using Runs.cons head (ih suffix)

/-- An invariant must hold after every possible local transition. -/
theorem preserves (invariant : State → Prop)
    (preserved : ∀ s events t, invariant s → step s events t → invariant t)
    {initial final : State} {events : List Event}
    (execution : Runs step initial events final) (valid : invariant initial) :
    invariant final := by
  induction execution with
  | refl => exact valid
  | cons transition _ ih => exact ih (preserved _ _ _ valid transition)

/-- Every emitted event obeys the stated local policy. -/
theorem events_allowed (invariant : State → Prop) (allowed : Event → Prop)
    (preserved : ∀ s events t, invariant s → step s events t → invariant t)
    (emitted : ∀ s events t, invariant s → step s events t → ∀ e ∈ events, allowed e)
    {initial final : State} {events : List Event}
    (execution : Runs step initial events final) (valid : invariant initial) :
    ∀ e ∈ events, allowed e := by
  induction execution with
  | refl => simp
  | cons transition _ ih =>
    intro e member
    rcases List.mem_append.mp member with head | tail
    · exact emitted _ _ _ valid transition e head
    · exact ih (preserved _ _ _ valid transition) e tail

end Runs

/-- One implementation transition may correspond to several specification steps.
The relation must match every implementation/environment choice. -/
def Refines {Implementation : Type u} {Specification : Type w} {Event : Type v}
    (implementation : Implementation → List Event → Implementation → Prop)
    (specification : Specification → List Event → Specification → Prop)
    (related : Implementation → Specification → Prop) : Prop :=
  ∀ impl spec events next, related impl spec → implementation impl events next →
    ∃ target, Runs specification spec events target ∧ related next target

/-- All finite implementation traces are admitted by the specification. -/
theorem Refines.runs {Implementation : Type u} {Specification : Type w} {Event : Type v}
    {implementation : Implementation → List Event → Implementation → Prop}
    {specification : Specification → List Event → Specification → Prop}
    {related : Implementation → Specification → Prop}
    (simulation : Refines implementation specification related)
    {initial final : Implementation} {source : Specification} {events : List Event}
    (execution : Runs implementation initial events final) (initially : related initial source) :
    ∃ target, Runs specification source events target ∧ related final target := by
  induction execution generalizing source with
  | refl => exact ⟨source, .refl _, initially⟩
  | cons transition _ ih =>
    obtain ⟨middle, first, relation⟩ := simulation _ _ _ _ initially transition
    obtain ⟨target, last, relation⟩ := ih relation
    exact ⟨target, first.append last, relation⟩

/-- Compose independently proved implementation layers, retaining every
environment choice and the complete observable trace. -/
theorem Refines.trans {Implementation : Type u} {Intermediate : Type w}
    {Specification : Type*} {Event : Type v}
    {implementation : Implementation → List Event → Implementation → Prop}
    {intermediate : Intermediate → List Event → Intermediate → Prop}
    {specification : Specification → List Event → Specification → Prop}
    {firstRelation : Implementation → Intermediate → Prop}
    {secondRelation : Intermediate → Specification → Prop}
    (first : Refines implementation intermediate firstRelation)
    (second : Refines intermediate specification secondRelation) :
    Refines implementation specification
      (fun impl spec => ∃ middle, firstRelation impl middle ∧ secondRelation middle spec) := by
  intro impl spec events next relation transition
  obtain ⟨middle, firstRelated, secondRelated⟩ := relation
  obtain ⟨nextMiddle, middleRun, nextFirstRelated⟩ := first _ _ _ _ firstRelated transition
  obtain ⟨target, targetRun, nextSecondRelated⟩ := second.runs middleRun secondRelated
  exact ⟨target, targetRun, nextMiddle, nextFirstRelated, nextSecondRelated⟩

/-- An observation of a finished implementation must satisfy any matching
specification contract, including explicit failure and partial-output cases. -/
theorem Refines.contract {Implementation : Type u} {Specification : Type w} {Event : Type v}
    {implementation : Implementation → List Event → Implementation → Prop}
    {specification : Specification → List Event → Specification → Prop}
    {related : Implementation → Specification → Prop}
    (simulation : Refines implementation specification related)
    (finished : Implementation → Prop) (accepted : List Event → Prop)
    {initial : Implementation} {source : Specification}
    (initially : related initial source)
    (contract : ∀ events target impl, Runs specification source events target →
      related impl target → finished impl → accepted events)
    {events : List Event} {final : Implementation}
    (execution : Runs implementation initial events final) (stopped : finished final) :
    accepted events := by
  obtain ⟨target, trace, relation⟩ := simulation.runs execution initially
  exact contract events target final trace relation stopped

/-- Erasing observations still requires an actual transition at every step. -/
def Moves {State : Type u} {Event : Type v}
    (step : State → List Event → State → Prop) (before after : State) : Prop :=
  ∃ events, step before events after

/-- Divergence is an infinite path, independent of finite safety and contracts. -/
def Diverges {State : Type u} {Event : Type v}
    (step : State → List Event → State → Prop) (initial : State) : Prop :=
  InfiniteTrace (Moves step) initial

end Silmaril.Machine.Trace
