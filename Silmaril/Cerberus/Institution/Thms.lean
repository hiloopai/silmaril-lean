module

public import Silmaril.Cerberus.Institution.Defs

@[expose] public section
namespace Silmaril.Cerberus.Institution

open CategoryTheory
open Silmaril.Cerberus.Core.Dynamics

/-- The institution satisfaction condition for a vocabulary inclusion. -/
theorem satisfaction {source target : Signature} (inclusion : source ⟶ target)
    (model : (room target).Mod) (sentence : (room source).Sen) :
    (room target).Sat model ((inst.map inclusion).sen sentence) ↔
      (room source).Sat ((inst.map inclusion).mod.obj model) sentence :=
  (inst.map inclusion).sat model sentence

/-- Certified bounded executions produce genuine finite behaviors, including
resumable states on fuel exhaustion. -/
theorem run_realises (model : Model) (fuel : Nat) :
    model.realises (.finite
      (run model.program model.labels fuel model.initialState).actions
      (run model.program model.labels fuel model.initialState).finalState) :=
  run_sound model.program model.labels fuel model.initialState

/-- Any universally satisfied specification holds of the runner's certified
trace. A successful check of one runner trace alone proves no converse. -/
theorem run_satisfies {model : Model} {sentence : Sentence}
    (valid : Satisfies model sentence) (fuel : Nat) :
    sentence (.finite
      (run model.program model.labels fuel model.initialState).actions
      (run model.program model.labels fuel model.initialState).finalState) :=
  valid _ (run_realises model fuel)

/-- A same-language refinement preserves every universally satisfied Core
specification, including UB safety, output postconditions and termination. -/
theorem satisfies_of_refines {target source : Model} {sentence : Sentence}
    (refinement : target.Refines source) (valid : Satisfies source sentence) :
    Satisfies target sentence :=
  fun behavior trace => valid behavior (refinement behavior trace)

/-- Refinements compose without selecting a runner or a fuel bound. -/
theorem Model.Refines.trans {first second third : Model}
    (firstSecond : first.Refines second) (secondThird : second.Refines third) :
    first.Refines third :=
  fun behavior trace => secondThird behavior (firstSecond behavior trace)

/-- The empty trace is a real behavior; specifications can constrain startup. -/
theorem initial_realises (model : Model) :
    model.realises (.finite [] model.initialState) :=
  .refl

/-- Logical conjunction distributes through universal behavior satisfaction. -/
theorem satisfies_and (model : Model) (left right : Sentence) :
    Satisfies model (fun behavior => left behavior ∧ right behavior) ↔
      Satisfies model left ∧ Satisfies model right := by
  constructor
  · intro valid
    exact ⟨fun behavior trace => (valid behavior trace).1,
      fun behavior trace => (valid behavior trace).2⟩
  · rintro ⟨hl, hr⟩ behavior trace
    exact ⟨hl behavior trace, hr behavior trace⟩

/-- A Core safety proof excludes UB from every finite certified execution. -/
theorem run_noUndefinedBehaviour {model : Model}
    (safe : Satisfies model noUndefinedBehaviour) (fuel : Nat) :
    ∀ location ub,
      (run model.program model.labels fuel model.initialState).finalState.control ≠
        .halt (.ub location ub) :=
  run_satisfies safe fuel

/-- A terminal stdout specification applies to every certified returned state. -/
theorem run_terminalOutput {model : Model} {allowed : String → Prop}
    (valid : Satisfies model (terminalOutput allowed)) (fuel : Nat) (outcome : Outcome)
    (ended : (run model.program model.labels fuel model.initialState).finalState.control =
      .halt outcome) :
    allowed (run model.program model.labels fuel model.initialState).finalState.memory.stdout :=
  run_satisfies valid fuel outcome ended

/-- A halted Core configuration admits no infinite execution, independently
of the runner and its fuel. -/
theorem terminal_terminates (model : Model) (outcome : Outcome)
    (halted : model.initialState.control = .halt outcome) :
    Satisfies model terminates := by
  intro behavior valid
  cases behavior with
  | finite => trivial
  | infinite states actions =>
    rcases valid with ⟨starts, steps⟩
    have step := steps 0
    rw [starts] at step
    cases step with
    | respond live _ => exact live outcome halted

/-- A termination proof excludes every infinite labeled execution of the LTS. -/
theorem no_infinite_execution {model : Model}
    (terminating : Satisfies model terminates) (states : Nat → State)
    (actions : Nat → Label) (starts : states 0 = model.initialState)
    (steps : ∀ n, (lts model.program model.labels).Tr (states n) (actions n) (states (n + 1))) :
    False :=
  terminating (.infinite states actions) ⟨starts, steps⟩

end Silmaril.Cerberus.Institution
