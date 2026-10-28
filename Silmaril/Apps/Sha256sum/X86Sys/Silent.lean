module

public import Silmaril.Apps.Sha256sum.X86Sys
public import Silmaril.Process.CLI.X86Linux.ExtStep

/-! # Finite silent extended-x86 executions in the `sha256sum` process machine

A successful finite `X86.Ext` execution gives an actual sequence of internal
`X86Sys.x86Machine` steps, for every choice of syscall `r11Of`. The kernel is
unchanged throughout, as are the heap bookkeeping and fault flag. The final
`RET` of `X86.Ext.Returns` is included as an internal instruction; it does not
exit the process.

These are completed-execution and continuation lemmas. They do not require
termination, progress, or a particular environment outside the supplied segment.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.Apps.Sha256sum.Sys
open Silmaril.X86 (MState Word)

/-- The core and memory observed by the extended instruction model. -/
def toExtState (s : XState) : MState := ⟨s.core, s.memory⟩

/-- Replace precisely the core and memory, retaining the process bookkeeping. -/
def withExtState (s : XState) (m : MState) : XState :=
  { s with core := m.core, memory := m.memory }

@[simp] theorem toExtState_withExtState (s : XState) (m : MState) :
    toExtState (withExtState s m) = m := by
  cases m
  rfl

@[simp] theorem withExtState_toExtState (s : XState) :
    withExtState s (toExtState s) = s := by
  cases s
  rfl

@[simp] theorem withExtState_withExtState (s : XState) (m n : MState) :
    withExtState (withExtState s m) n = withExtState s n := rfl

@[simp] theorem withExtState_core (s : XState) (m : MState) :
    (withExtState s m).core = m.core := rfl

@[simp] theorem withExtState_memory (s : XState) (m : MState) :
    (withExtState s m).memory = m.memory := rfl

@[simp] theorem withExtState_brkStart (s : XState) (m : MState) :
    (withExtState s m).brkStart = s.brkStart := rfl

@[simp] theorem withExtState_brk (s : XState) (m : MState) :
    (withExtState s m).brk = s.brk := rfl

@[simp] theorem withExtState_faulted (s : XState) (m : MState) :
    (withExtState s m).faulted = s.faulted := rfl

/-- Exactly `n` internal process steps, carrying no system calls or exits. -/
inductive TauRun (r11Of : Core → Word) : Nat → XState → XState → Prop where
  | refl {s} : TauRun r11Of 0 s s
  | cons {n s mid final} : (x86Machine r11Of).step s = .tau mid →
      TauRun r11Of n mid final → TauRun r11Of (n + 1) s final

namespace TauRun

theorem single {r11Of : Core → Word} {s t : XState}
    (head : (x86Machine r11Of).step s = .tau t) : TauRun r11Of 1 s t :=
  .cons head .refl

theorem append {r11Of : Core → Word} {n m : Nat} {s t u : XState}
    (first : TauRun r11Of n s t) (second : TauRun r11Of m t u) :
    TauRun r11Of (n + m) s u := by
  induction first with
  | refl => simpa using second
  | cons head _ ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using TauRun.cons head (ih second)

/-- A silent segment is a reachability witness with exactly the same kernel state. -/
theorem reach {r11Of : Core → Word} {n : Nat} {s t : XState}
    (run : TauRun r11Of n s t) (E : Env) (k : KState) :
    Reach (x86Machine r11Of) E n s k t k := by
  induction run with
  | refl => exact .refl
  | cons head _ ih => exact .tau head ih

private theorem exec_tau_iff {M : Machine} {s t : M.State}
    (head : M.step s = .tau t) {E : Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec M E s k events status ↔ Exec M E t k events status := by
  constructor
  · intro run
    cases run with
    | exit exited => rw [head] at exited; cases exited
    | tau stepped tail =>
      rw [head] at stepped
      cases stepped
      exact tail
    | call called _ _ => rw [head] at called; cases called
  · exact .tau head

/-- The completed continuation has precisely the same calls, replies and exit status
before and after a finite silent segment. -/
theorem exec_iff {r11Of : Core → Word} {n : Nat} {s t : XState}
    (run : TauRun r11Of n s t) {E : Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec (x86Machine r11Of) E s k events status ↔
      Exec (x86Machine r11Of) E t k events status := by
  induction run with
  | refl => rfl
  | cons head _ ih => exact (exec_tau_iff head).trans ih

end TauRun

/-- A supported Ext retirement is an internal step for every syscall R11 policy. -/
theorem step_of_ext_retired {r11Of : Core → Word} {exit : Word} {s : XState}
    {final : MState} (running : s.faulted = false)
    (retired : X86.Ext.step exit (toExtState s) = .retired final) :
    (x86Machine r11Of).step s = .tau (withExtState s final) := by
  have coreStep : Process.CLI.X86Linux.step s.core s.memory =
      .retired final.core final.memory := Process.CLI.X86Linux.step_of_ext_retired retired
  simp [x86Machine, step, running, coreStep, withExtState]

/-- The designated function return is another internal process step, not an exit. -/
theorem step_of_ext_returned {r11Of : Core → Word} {exit : Word} {s : XState}
    {final : MState} (running : s.faulted = false)
    (returned : X86.Ext.step exit (toExtState s) = .returned final) :
    (x86Machine r11Of).step s = .tau (withExtState s final) := by
  have coreStep : Process.CLI.X86Linux.step s.core s.memory =
      .retired final.core final.memory := Process.CLI.X86Linux.step_of_ext_returned returned
  simp [x86Machine, step, running, coreStep, withExtState]

/-- Exactly `n` successful Ext retirements give exactly `n` internal process steps. -/
theorem ext_run_tauRun {r11Of : Core → Word} {exit : Word} {n : Nat}
    {s : XState} {final : MState} (running : s.faulted = false)
    (executed : Silmaril.Machine.Execution.run (X86.Ext.stepOpt exit) n (toExtState s) =
      some final) :
    TauRun r11Of n s (withExtState s final) := by
  induction n generalizing s with
  | zero =>
    simp only [Silmaril.Machine.Execution.run_zero, Option.some.injEq] at executed
    subst final
    simpa using (TauRun.refl : TauRun r11Of 0 s s)
  | succ n ih =>
    simp only [Silmaril.Machine.Execution.run_succ] at executed
    cases head : X86.Ext.stepOpt exit (toExtState s) with
    | none => simp [head] at executed
    | some mid =>
      simp only [head, Option.bind_some] at executed
      have first := step_of_ext_retired (r11Of := r11Of) running
        (X86.Ext.stepOpt_eq_some_iff.mp head)
      have rest := ih (s := withExtState s mid) running (by simpa using executed)
      simpa only [withExtState_withExtState] using TauRun.cons first rest

/-- `Returns` includes its last `RET`: the process segment has `n + 1` internal
steps, for the `n` retirements witnessed by the Ext contract. -/
theorem ext_returns_tauRun {r11Of : Core → Word} {exit : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (returned : X86.Ext.Returns exit (toExtState s) final) :
    ∃ n, TauRun r11Of (n + 1) s (withExtState s final) := by
  obtain ⟨n, mid, executed, last⟩ := returned
  refine ⟨n, ?_⟩
  have first := ext_run_tauRun (r11Of := r11Of) running executed
  have lastStep := step_of_ext_returned (r11Of := r11Of)
    (s := withExtState s mid) running (by simpa using last)
  simpa only [withExtState_withExtState] using first.append (TauRun.single lastStep)

/-- A completed Ext function call may be replaced by its exact final core and memory
inside every environment and completed process continuation. -/
theorem exec_iff_of_ext_returns {r11Of : Core → Word} {exit : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (returned : X86.Ext.Returns exit (toExtState s) final) {E : Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec (x86Machine r11Of) E s k events status ↔
      Exec (x86Machine r11Of) E (withExtState s final) k events status := by
  obtain ⟨_, segment⟩ := ext_returns_tauRun (r11Of := r11Of) running returned
  exact segment.exec_iff

end Silmaril.Apps.Sha256sum.X86Sys
