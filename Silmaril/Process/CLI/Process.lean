module

public import Silmaril.Process.CLI.Isa
public import Silmaril.Process.CLI.Env
public import Silmaril.Machine.Trace

/-! # A CLI process: one user-mode thread in a syscall environment

`Proc.Step I E` composes an instruction-set model with an environment over
the environment's memory. A retirement emits no event; a completed system call
emits exactly its `Syscall.Event`; `exit` is a completed call after which the
environment reports `exited`. A call the environment does not complete has no
transition (blocking is not divergence). `Proc.Stop` gives the outcomes of
states with no further transition that a statement may observe.

`Proc.refines` is the transfer theorem: a simulation of models
(`Isa.Sim`, `Env.Sim`) is a lockstep simulation of processes, preserving every
event list, stop and infinite run. It is what lets a proof at a large model
point be reused at every smaller one (`CLI.Spec`).
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall Silmaril.Machine.Trace

structure PState (I : Isa) (E : Env) where
  core : I.Core
  env : E.State

namespace Proc

variable {I : Isa} {E : Env}

inductive Step (I : Isa) (E : Env) : PState I E → List Event → PState I E → Prop where
  | retire {c c' : I.Core} {s : E.State} {m : Memory}
      (running : E.exited s = none) (step : I.step c (E.memory s) (.retired c' m)) :
      Step I E ⟨c, s⟩ [] ⟨c', E.withMemory s m⟩
  | call {c c' c'' : I.Core} {s s' : E.State} {q : Request} {ev : Event} {r : Result}
      (running : E.exited s = none) (step : I.step c (E.memory s) (.syscall c'))
      (request : I.request c' = some q) (effect : E.step s q ev (.returned r) s')
      (resume : I.resume c' r c'') :
      Step I E ⟨c, s⟩ [ev] ⟨c'', s'⟩
  | exit {c c' : I.Core} {s s' : E.State} {q : Request} {ev : Event} {status : Nat}
      (running : E.exited s = none) (step : I.step c (E.memory s) (.syscall c'))
      (request : I.request c' = some q) (effect : E.step s q ev (.exited status) s') :
      Step I E ⟨c, s⟩ [ev] ⟨c', s'⟩

def Fault.outcome : Fault → Outcome
  | .unmodeled => .unmodeled
  | f => .crashed f

/-- Observable stops. A blocked call and a gap in a model are not stops. -/
inductive Stop (I : Isa) (E : Env) : PState I E → Outcome → Prop where
  | exited {c : I.Core} {s : E.State} {status : Nat} (exited : E.exited s = some status) :
      Stop I E ⟨c, s⟩ (.exited status)
  | fault {c : I.Core} {s : E.State} {f : Fault} (running : E.exited s = none)
      (step : I.step c (E.memory s) (.fault f)) :
      Stop I E ⟨c, s⟩ (Fault.outcome f)
  | unsupported {c c' : I.Core} {s : E.State} (running : E.exited s = none)
      (step : I.step c (E.memory s) (.syscall c')) (request : I.request c' = none) :
      Stop I E ⟨c, s⟩ .unmodeled

/-- An exit stop is exactly an exited environment. -/
theorem Stop.exited_status {y : PState I E} {status : Nat} (stop : Stop I E y (.exited status)) :
    E.exited y.env = some status := by
  generalize outcome : Outcome.exited status = o at stop
  cases stop with
  | exited h => cases outcome; exact h
  | @fault _ _ f _ _ => cases f <;> cases outcome
  | unsupported => cases outcome

/-- Every finite run from `initial`, with its events, ending at `final`. -/
abbrev Runs (I : Isa) (E : Env) := Machine.Trace.Runs (Step I E)

/-- An infinite run of completed steps. -/
abbrev Diverges (I : Isa) (E : Env) := Machine.Trace.Diverges (Step I E)

/-- Every event of a step is one the environment admits. -/
theorem Step.events_admitted {x y : PState I E} {events : List Event}
    (step : Step I E x events y) : ∀ e ∈ events, ∃ s q r s', E.step s q e r s' := by
  cases step with
  | retire => simp
  | call _ _ _ effect _ =>
    intro e member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨_, _, _, _, effect⟩
  | exit _ _ _ effect =>
    intro e member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨_, _, _, _, effect⟩

theorem runs_events_admitted {x y : PState I E} {events : List Event} (run : Runs I E x events y) :
    ∀ e ∈ events, ∃ s q r s', E.step s q e r s' := by
  induction run with
  | refl => simp
  | cons step _ ih =>
    intro e member
    rcases List.mem_append.mp member with head | tail
    · exact step.events_admitted e head
    · exact ih e tail

/-! ## Transfer along model simulations -/

variable {J : Isa} {F : Env}

/-- Related process states. -/
def Related (si : Isa.Sim I J) (se : Env.Sim E F) (x : PState I E) (y : PState J F) : Prop :=
  si.rel x.core y.core ∧ se.rel x.env y.env

theorem step_sim (si : Isa.Sim I J) (se : Env.Sim E F)
    {x x' : PState I E} {y : PState J F} {events : List Event}
    (related : Related si se x y) (step : Step I E x events x') :
    ∃ y', Step J F y events y' ∧ Related si se x' y' := by
  obtain ⟨rc, re⟩ := related
  cases step with
  | retire running step =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step)
    cases rel with
    | retired h =>
      exact ⟨_, .retire ((se.exited re) ▸ running) step', h, se.withMemory _ re⟩
  | call running step request effect resume =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step)
    cases rel with
    | syscall h =>
      obtain ⟨t', effect', re'⟩ := se.step re effect
      obtain ⟨d', resume', rc'⟩ := si.resume h resume
      exact ⟨_, .call ((se.exited re) ▸ running) step' ((si.request h) ▸ request) effect' resume',
        rc', re'⟩
  | exit running step request effect =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step)
    cases rel with
    | syscall h =>
      obtain ⟨t', effect', re'⟩ := se.step re effect
      exact ⟨_, .exit ((se.exited re) ▸ running) step' ((si.request h) ▸ request) effect', h, re'⟩

/-- A model simulation is a (lockstep) trace refinement of processes. -/
theorem refines (si : Isa.Sim I J) (se : Env.Sim E F) :
    Machine.Trace.Refines (Step I E) (Step J F) (Related si se) := by
  intro x y events x' related step
  obtain ⟨y', step', related'⟩ := step_sim si se related step
  exact ⟨y', .single step', related'⟩

theorem stop_sim (si : Isa.Sim I J) (se : Env.Sim E F) {x : PState I E} {y : PState J F}
    {o : Outcome} (related : Related si se x y) (stop : Stop I E x o) : Stop J F y o := by
  obtain ⟨rc, re⟩ := related
  cases stop with
  | exited exited => exact .exited ((se.exited re) ▸ exited)
  | fault running step =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step)
    cases rel with
    | fault f => exact .fault ((se.exited re) ▸ running) step'
  | unsupported running step request =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step)
    cases rel with
    | syscall h => exact .unsupported ((se.exited re) ▸ running) step' ((si.request h) ▸ request)

theorem diverges_sim (si : Isa.Sim I J) (se : Env.Sim E F)
    {x : PState I E} {y : PState J F} (related : Related si se x y)
    (diverges : Diverges I E x) : Diverges J F y := by
  apply InfiniteTrace.coinduct (fun y => ∃ x, Related si se x y ∧ Diverges I E x) ?_
    ⟨x, related, diverges⟩
  rintro y ⟨x, related, diverges⟩
  obtain ⟨x', ⟨events, step⟩, tail⟩ := diverges.unfold
  obtain ⟨y', step', related'⟩ := step_sim si se related step
  exact ⟨y', ⟨events, step'⟩, x', related', tail⟩

end Proc

end Silmaril.Process.CLI
