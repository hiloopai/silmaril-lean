module

public import Silmaril.Process.CLI.X86Linux

/-! # Invert actual supported syscalls and completed exit continuations

The instruction result fixes a syscall's trapped core and request. Its
environment reply and resumed core remain arbitrary. An exited environment
admits no later process step; a completed run from it retains its exact status.
These are safety facts, with no syscall availability or termination premise.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

namespace Proc

variable {I : Isa} {E : Env}

/-- Every actual process transition starts in a running environment. -/
theorem Step.running {initial final : PState I E} {events : List Event}
    (transition : Step I E initial events final) : E.exited initial.env = none := by
  cases transition <;> assumption

/-- A reported exit excludes every later process transition. -/
theorem no_step_after_exit {initial final : PState I E} {events : List Event} {status : Nat}
    (exited : E.exited initial.env = some status) : ¬ Step I E initial events final := by
  intro transition
  have running := transition.running
  rw [exited] at running
  cases running

/-- A finite process run from an exited state is the zero-step run. -/
theorem runs_from_exited {initial final : PState I E} {events : List Event} {status : Nat}
    (exited : E.exited initial.env = some status) (execution : Runs I E initial events final) :
    events = [] ∧ final = initial := by
  cases execution with
  | refl => exact ⟨rfl, rfl⟩
  | cons first _ => exact False.elim (no_step_after_exit exited first)

/-- An exited state has exactly its reported stop outcome. -/
theorem Stop.eq_exited {initial : PState I E} {outcome : Outcome} {status : Nat}
    (exited : E.exited initial.env = some status) (stopped : Stop I E initial outcome) :
    outcome = .exited status := by
  cases stopped with
  | exited reported =>
    have same := Option.some.inj (reported.symm.trans exited)
    cases same
    rfl
  | fault running _ => rw [exited] at running; cases running
  | unsupported running _ _ => rw [exited] at running; cases running

/-- Completed observations after exit retain the empty trace, exact state and
status. In particular an exit-1 continuation cannot become successful exit 0. -/
theorem completed_from_exited {initial final : PState I E} {events : List Event}
    {outcome : Outcome} {status : Nat} (exited : E.exited initial.env = some status)
    (execution : Runs I E initial events final) (stopped : Stop I E final outcome) :
    events = [] ∧ final = initial ∧ outcome = .exited status := by
  obtain ⟨empty, rfl⟩ := runs_from_exited exited execution
  exact ⟨empty, rfl, Stop.eq_exited exited stopped⟩

end Proc

namespace X86Linux

variable {E : Env}

/-- A known supported syscall has exactly the environment-return and
environment-exit alternatives. The reply, emitted event and `Resume` choice
are retained rather than selected by this inversion theorem. -/
theorem step_iff_of_syscall {c trapped : Core} {s : E.State} {q : Request}
    {events : List Event} {final : PState isa E}
    (trappedStep : step c (E.memory s) = .syscall trapped)
    (requested : request trapped = some q) :
    Proc.Step isa E ⟨c, s⟩ events final ↔
      E.exited s = none ∧
        ((∃ event result, events = [event] ∧
          E.step s q event (.returned result) final.env ∧ Resume trapped result final.core) ∨
         (∃ event status, events = [event] ∧
          E.step s q event (.exited status) final.env ∧ final.core = trapped)) := by
  constructor
  · intro transition
    cases transition with
    | retire running retired =>
      change CLI.Step.retired _ _ = step c (E.memory s) at retired
      rw [trappedStep] at retired
      cases retired
    | @call _ after _ _ _ req event result running called request effect resume =>
      change CLI.Step.syscall after = step c (E.memory s) at called
      rw [trappedStep] at called
      cases called
      have same := Option.some.inj (request.symm.trans requested)
      cases same
      exact ⟨running, .inl ⟨event, result, rfl, effect, resume⟩⟩
    | @exit _ after _ _ req event status running called request effect =>
      change CLI.Step.syscall after = step c (E.memory s) at called
      rw [trappedStep] at called
      cases called
      have same := Option.some.inj (request.symm.trans requested)
      cases same
      exact ⟨running, .inr ⟨event, status, rfl, effect, rfl⟩⟩
  · rintro ⟨running, returned | exited⟩
    · obtain ⟨event, result, rfl, effect, resume⟩ := returned
      exact .call running trappedStep.symm requested effect resume
    · obtain ⟨event, status, rfl, effect, core⟩ := exited
      cases final with
      | mk finalCore finalEnv =>
        dsimp at core
        subst finalCore
        exact .exit running trappedStep.symm requested effect

/-- A running state whose exact instruction is a supported syscall cannot
already be an exit, fault or unsupported-instruction stop. Blocking still
remains possible because this does not construct an environment reply. -/
theorem not_stop_of_syscall {c trapped : Core} {s : E.State} {q : Request}
    {outcome : Outcome} (running : E.exited s = none)
    (trappedStep : step c (E.memory s) = .syscall trapped)
    (requested : request trapped = some q) : ¬ Proc.Stop isa E ⟨c, s⟩ outcome := by
  intro stopped
  cases stopped with
  | exited exited => rw [running] at exited; cases exited
  | fault _ faulted =>
    change CLI.Step.fault _ = step c (E.memory s) at faulted
    rw [trappedStep] at faulted
    cases faulted
  | unsupported _ called unsupported =>
    change CLI.Step.syscall _ = step c (E.memory s) at called
    rw [trappedStep] at called
    cases called
    change request trapped = none at unsupported
    rw [requested] at unsupported
    cases unsupported

/-- Every completed run at a known Linux exit syscall emits its one exact
exit event and retains that status. No instruction or syscall availability is
assumed, and the theorem does not assert that a completed run exists. -/
theorem completed_exit {c trapped : Core} {s : Syscall.State} {status observed : Nat}
    {events : List Event} {final : PState isa Env.linux}
    (running : s.exited = none)
    (trappedStep : step c s.memory = .syscall trapped)
    (requested : request trapped = some (.exit status))
    (execution : Proc.Runs isa Env.linux ⟨c, s⟩ events final)
    (stopped : Proc.Stop isa Env.linux final (.exited observed)) :
    events = [.exit (status % 256)] ∧ observed = status % 256 := by
  cases execution with
  | refl => exact False.elim (not_stop_of_syscall running trappedStep requested stopped)
  | @cons _ next _ _ _ first rest =>
    obtain ⟨nextCore, nextEnv⟩ := next
    obtain ⟨_, returned | exiting⟩ := (step_iff_of_syscall trappedStep requested).mp first
    · obtain ⟨_, _, _, effect, _⟩ := returned
      change Syscall.Step _ (.exit status) _ (.returned _) _ at effect
      cases effect
    · obtain ⟨event, code, headEvents, effect, _⟩ := exiting
      change Syscall.Step _ (.exit status) event (.exited code) _ at effect
      cases effect
      obtain ⟨empty, _, sameStatus⟩ := Proc.completed_from_exited rfl rest stopped
      exact ⟨by simp only [headEvents, empty, List.append_nil], Outcome.exited.inj sameStatus⟩

end X86Linux

end Silmaril.Process.CLI
