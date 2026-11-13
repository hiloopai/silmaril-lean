module

public import Silmaril.Cerberus.Core.Forced.Defs

@[expose] public section

namespace Silmaril.Cerberus.Core.Forced

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics

variable {file : Program} {labels : Labels}

/-- One genuine edge with local uniqueness is a forced execution. -/
theorem Reaches.single {source target : State} {action : Label}
    (edge : Step file labels source action target)
    (unique : ∀ otherAction otherTarget, Step file labels source otherAction otherTarget →
      otherAction = action ∧ otherTarget = target) :
    Reaches file labels source target :=
  .cons edge unique .refl

/-- Forced executions compose without any determinism assumption elsewhere. -/
theorem Reaches.trans {first middle last : State}
    (left : Reaches file labels first middle)
    (right : Reaches file labels middle last) : Reaches file labels first last := by
  induction left with
  | refl => exact right
  | cons edge unique _ ih => exact .cons edge unique (ih right)

/-- Forget local uniqueness to obtain ordinary reachability in the actual LTS. -/
theorem Reaches.erase {source target : State} (path : Reaches file labels source target) :
    Relation.ReflTransGen (fun s t => ∃ a, Step file labels s a t) source target := by
  induction path with
  | refl => exact .refl
  | cons edge _ _ ih => exact ih.head ⟨_, edge⟩

/-- A request whose responses are unique gives a forced singleton transition. -/
theorem step {source target : State} {action : Label} {response : Request}
    (live : ∀ outcome, source.control ≠ .halt outcome)
    (requestEq : request file labels source = response)
    (responds : Respond source.memory response action target)
    (unique : ∀ otherAction otherTarget,
      Respond source.memory response otherAction otherTarget →
        otherAction = action ∧ otherTarget = target) :
    Reaches file labels source target := by
  apply Reaches.single (Step.respond live (by rw [requestEq]; exact responds))
  intro otherAction otherTarget other
  cases other with
  | respond _ responseProof =>
    rw [requestEq] at responseProof
    exact unique _ _ responseProof

/-- Administrative continuation is forced. This has the same premises as
`PureEval.next_reaches`, with the stronger forced-execution conclusion. -/
theorem next {c c' : Control} {k k' : List Frame}
    {m : Mem.Concrete.State} (live : ∀ outcome, c ≠ .halt outcome)
    (requestEq : request file labels ⟨c, k, m⟩ = .next c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ := by
  apply step live requestEq Respond.next
  intro otherAction otherTarget response
  cases response
  exact ⟨rfl, rfl⟩

/-- An unlabelled memory update is forced. -/
theorem update {source : State} {after : Mem.Concrete.State} {control : Control}
    {frames : List Frame} (live : ∀ outcome, source.control ≠ .halt outcome)
    (requestEq : request file labels source = .update after control frames) :
    Reaches file labels source ⟨control, frames, after⟩ := by
  apply step live requestEq Respond.update
  intro otherAction otherTarget response
  cases response
  exact ⟨rfl, rfl⟩

/-- A labelled memory update is forced. -/
theorem memory {source : State} {name : String} {after : Mem.Concrete.State}
    {control : Control} {frames : List Frame}
    (live : ∀ outcome, source.control ≠ .halt outcome)
    (requestEq : request file labels source = .memory name after control frames) :
    Reaches file labels source ⟨control, frames, after⟩ := by
  apply step live requestEq Respond.memory
  intro otherAction otherTarget response
  cases response
  exact ⟨rfl, rfl⟩

/-- A terminal response is forced; halted states themselves have no edge. -/
theorem end_ {source : State} {outcome : Outcome}
    (live : ∀ result, source.control ≠ .halt result)
    (requestEq : request file labels source = .end_ outcome) :
    Reaches file labels source ⟨.halt outcome, [], source.memory⟩ := by
  apply step live requestEq Respond.end_
  intro otherAction otherTarget response
  cases response
  exact ⟨rfl, rfl⟩

/-- A singleton genuine choice is forced. -/
theorem choose {source : State} {control : Control} {frames : List Frame}
    (live : ∀ outcome, source.control ≠ .halt outcome)
    (requestEq : request file labels source = .choose [(control, frames)]) :
    Reaches file labels source ⟨control, frames, source.memory⟩ := by
  apply step live requestEq (Respond.choose (by simp))
  intro otherAction otherTarget response
  cases response with
  | choose member =>
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- A singleton scheduling choice is forced. -/
theorem scheduled {source : State} {control : Control} {frames : List Frame}
    (live : ∀ outcome, source.control ≠ .halt outcome)
    (requestEq : request file labels source = .scheduled [(control, frames)]) :
    Reaches file labels source ⟨control, frames, source.memory⟩ := by
  apply step live requestEq (Respond.scheduled (by simp))
  intro otherAction otherTarget response
  cases response with
  | scheduled member =>
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Every reachable halted state agrees with a forced halted endpoint, even
when the rest of the Core machine has nondeterministic choices. -/
theorem terminal_unique {source finish state : State} {outcome other : Outcome}
    (path : Reaches file labels source finish) (halted : finish.control = .halt outcome)
    (reachable : Relation.ReflTransGen (fun s t => ∃ a, Step file labels s a t) source state)
    (stateHalted : state.control = .halt other) : state = finish := by
  induction path generalizing state with
  | refl =>
    rcases reachable.cases_head with equal | ⟨_, ⟨_, edge⟩, _⟩
    · exact equal.symm
    · cases edge with
      | respond live _ => exact False.elim (live outcome halted)
  | cons edge unique _ ih =>
    rcases reachable.cases_head with equal | ⟨nextState, ⟨action, otherEdge⟩, tail⟩
    · cases edge with
      | respond live _ => exact False.elim (live other (equal.symm ▸ stateHalted))
    · obtain ⟨_, rfl⟩ := unique action nextState otherEdge
      exact ih halted tail stateHalted

/-- No infinite labelled Core execution can start at a state with a forced
finite execution to a halted endpoint. -/
theorem no_infinite {source finish : State} {outcome : Outcome}
    (path : Reaches file labels source finish) (halted : finish.control = .halt outcome)
    (states : Nat → State) (actions : Nat → Label) (starts : states 0 = source)
    (steps : ∀ n, Step file labels (states n) (actions n) (states (n + 1))) : False := by
  induction path generalizing states actions with
  | refl =>
    have first := steps 0
    rw [starts] at first
    cases first with
    | respond live _ => exact live outcome halted
  | cons _ unique _ ih =>
    have first := steps 0
    rw [starts] at first
    have nextState := (unique _ _ first).2
    apply ih halted (fun n => states (n + 1)) (fun n => actions (n + 1)) nextState
    intro n
    exact steps (n + 1)

end Silmaril.Cerberus.Core.Forced
