module

public import Silmaril.Process.CLI.X86Linux.Silent

/-! # Transport across completed silent instruction segments

A finite internal segment can be inserted or removed from a completed process
execution without changing its events, final state, or outcome. Only the ISA's
one-step result is deterministic: syscall replies and `resume` may remain
nondeterministic. A run ending inside the segment need not reach its endpoint;
the separate prefix-policy theorem therefore requires acceptance of `[]`.

These are partial-correctness transport results. They assert neither global
termination nor coverage of instructions outside the supplied actual segment.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

namespace Proc

variable {I : Isa} {E : Env}

/-- An actual silent transition is a retirement, so every transition from its
source has the same empty trace and the same exact endpoint. -/
theorem Step.unique_of_silent
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle final : PState I E} {events : List Event}
    (silent : Step I E initial [] middle) (other : Step I E initial events final) :
    events = [] ∧ final = middle := by
  cases silent with
  | retire running retired =>
    cases other with
    | retire running' retired' =>
      have same := deterministic _ _ _ _ retired retired'
      cases same
      exact ⟨rfl, rfl⟩
    | call running' trapped request effect resume =>
      have impossible := deterministic _ _ _ _ retired trapped
      cases impossible
    | exit running' trapped request effect =>
      have impossible := deterministic _ _ _ _ retired trapped
      cases impossible

/-- A state with an actual silent retirement cannot already be an observable
stop, including a crash or unsupported syscall. -/
theorem not_stop_of_silent_step
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle : PState I E} {outcome : Outcome}
    (silent : Step I E initial [] middle) : ¬ Stop I E initial outcome := by
  cases silent with
  | retire running retired =>
    intro stopped
    cases stopped with
    | exited exited => rw [running] at exited; cases exited
    | fault running' faulted =>
      have impossible := deterministic _ _ _ _ retired faulted
      cases impossible
    | unsupported running' trapped request =>
      have impossible := deterministic _ _ _ _ retired trapped
      cases impossible

/-- Cancel a single internal instruction from a completed execution. A
zero-step run cannot stop at its source, and every first step is this retire. -/
theorem completed_iff_of_silent_step
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle final : PState I E} {events : List Event} {outcome : Outcome}
    (silent : Step I E initial [] middle) :
    (Runs I E initial events final ∧ Stop I E final outcome) ↔
      (Runs I E middle events final ∧ Stop I E final outcome) := by
  constructor
  · rintro ⟨execution, stopped⟩
    cases execution with
    | refl => exact False.elim (not_stop_of_silent_step deterministic silent stopped)
    | cons first rest =>
      obtain ⟨rfl, rfl⟩ := silent.unique_of_silent deterministic first
      exact ⟨rest, stopped⟩
  · rintro ⟨continuation, stopped⟩
    exact ⟨.cons silent continuation, stopped⟩

/-- Insert or cancel a finite silent instruction segment for completed runs.
The exact final process state, event list, and stop outcome are retained. -/
theorem completed_iff_of_silent
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle final : PState I E} {events : List Event} {outcome : Outcome}
    (silent : Runs I E initial [] middle) :
    (Runs I E initial events final ∧ Stop I E final outcome) ↔
      (Runs I E middle events final ∧ Stop I E final outcome) := by
  generalize empty : ([] : List Event) = segmentEvents at silent
  induction silent with
  | refl => rfl
  | cons first rest ih =>
    obtain ⟨firstEmpty, restEmpty⟩ := List.append_eq_nil_iff.mp empty.symm
    subst firstEmpty
    exact (completed_iff_of_silent_step deterministic first).trans (ih restEmpty.symm)

/-- A finite run may stop before finishing the supplied silent segment. Its
trace is then empty; otherwise it is a run from the segment's endpoint. -/
theorem runs_empty_or_after_silent
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle final : PState I E} {events : List Event}
    (silent : Runs I E initial [] middle) (execution : Runs I E initial events final) :
    events = [] ∨ Runs I E middle events final := by
  generalize empty : ([] : List Event) = segmentEvents at silent
  rw [← empty]
  induction silent generalizing events final with
  | refl => exact .inr execution
  | cons first rest ih =>
    obtain ⟨firstEmpty, restEmpty⟩ := List.append_eq_nil_iff.mp empty.symm
    subst firstEmpty
    cases execution with
    | refl => exact .inl rfl
    | cons head tail =>
      obtain ⟨rfl, rfl⟩ := first.unique_of_silent deterministic head
      exact ih tail restEmpty.symm

/-- Completed-result contracts transport independently of prefix safety and
without any progress or crash-freedom premise. -/
theorem completed_contract_iff_of_silent
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle : PState I E} (silent : Runs I E initial [] middle)
    (accepted : List Event → Outcome → Prop) :
    (∀ events final outcome, Runs I E initial events final → Stop I E final outcome →
      accepted events outcome) ↔
    (∀ events final outcome, Runs I E middle events final → Stop I E final outcome →
      accepted events outcome) := by
  constructor
  · intro contract events final outcome continuation stopped
    obtain ⟨execution, stopped⟩ :=
      (completed_iff_of_silent deterministic silent).mpr ⟨continuation, stopped⟩
    exact contract events final outcome execution stopped
  · intro contract events final outcome execution stopped
    obtain ⟨continuation, stopped⟩ :=
      (completed_iff_of_silent deterministic silent).mp ⟨execution, stopped⟩
    exact contract events final outcome continuation stopped

/-- Prefix-policy transport additionally handles every early finite endpoint
inside the silent segment by requiring the empty trace to be permitted. -/
theorem prefix_policy_iff_of_silent
    (deterministic : ∀ c m a b, I.step c m a → I.step c m b → a = b)
    {initial middle : PState I E} (silent : Runs I E initial [] middle)
    (permitted : List Event → Prop) (empty : permitted []) :
    (∀ events final, Runs I E initial events final → permitted events) ↔
      (∀ events final, Runs I E middle events final → permitted events) := by
  constructor
  · intro policy events final continuation
    exact policy events final (silent.append continuation)
  · intro policy events final execution
    rcases runs_empty_or_after_silent deterministic silent execution with rfl | continuation
    · exact empty
    · exact policy events final continuation

end Proc

namespace X86Linux

open Silmaril.X86 (MState Word)
open Silmaril.Machine.Execution (run)

/-- The Linux wrapper's instruction-result relation is functional; this does
not constrain its deliberately nondeterministic syscall `R11` resume. -/
theorem instruction_deterministic (c : Core) (m : Memory) (a b : CLI.Step Core)
    (first : isa.step c m a) (second : isa.step c m b) : a = b :=
  first.trans second.symm

variable {E : Env}

/-- Concrete no-syscall finite execution transport for the Linux ISA. -/
theorem completed_iff_of_silent
    {initial middle final : PState isa E} {events : List Event} {outcome : Outcome}
    (silent : Proc.Runs isa E initial [] middle) :
    (Proc.Runs isa E initial events final ∧ Proc.Stop isa E final outcome) ↔
      (Proc.Runs isa E middle events final ∧ Proc.Stop isa E final outcome) :=
  Proc.completed_iff_of_silent instruction_deterministic silent

/-- Cancel exactly the successful Ext retirements, retaining the lawful
memory-lens endpoint and the unchanged completed observation. -/
theorem completed_iff_of_ext_run (lens : E.MemoryLens) {exit : Word} {n : Nat}
    {initial final : MState} {s : E.State} {target : PState isa E}
    {events : List Event} {outcome : Outcome}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (executed : run (X86.Ext.stepOpt exit) n initial = some final) :
    (Proc.Runs isa E ⟨initial.core, s⟩ events target ∧ Proc.Stop isa E target outcome) ↔
      (Proc.Runs isa E ⟨final.core, E.withMemory s final.memory⟩ events target ∧
        Proc.Stop isa E target outcome) :=
  completed_iff_of_silent (runs_of_ext_run lens running memory executed)

/-- A completed Ext call includes its final RET as a retirement. Removing this
segment never mistakes that function return for a process exit. -/
theorem completed_iff_of_ext_returns (lens : E.MemoryLens) {exit : Word}
    {initial final : MState} {s : E.State} {target : PState isa E}
    {events : List Event} {outcome : Outcome}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (returned : X86.Ext.Returns exit initial final) :
    (Proc.Runs isa E ⟨initial.core, s⟩ events target ∧ Proc.Stop isa E target outcome) ↔
      (Proc.Runs isa E ⟨final.core, E.withMemory s final.memory⟩ events target ∧
        Proc.Stop isa E target outcome) :=
  completed_iff_of_silent (runs_of_ext_returns lens running memory returned)

/-- Any predicate on completed observations can be proved at the post-RET
continuation. This interface imposes no prefix-output or termination promise. -/
theorem completed_contract_iff_of_ext_returns (lens : E.MemoryLens) {exit : Word}
    {initial final : MState} {s : E.State}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (returned : X86.Ext.Returns exit initial final)
    (accepted : List Event → Outcome → Prop) :
    (∀ events target outcome, Proc.Runs isa E ⟨initial.core, s⟩ events target →
      Proc.Stop isa E target outcome → accepted events outcome) ↔
    (∀ events target outcome,
      Proc.Runs isa E ⟨final.core, E.withMemory s final.memory⟩ events target →
      Proc.Stop isa E target outcome → accepted events outcome) :=
  Proc.completed_contract_iff_of_silent instruction_deterministic
    (runs_of_ext_returns lens running memory returned) accepted

end X86Linux

end Silmaril.Process.CLI
