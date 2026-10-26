module

public import Silmaril.Process.CLI.X86Linux.SyscallInversion

/-! # Finite observations at an actual exit syscall

Unlike completed-run inversion, this also admits a finite run that ends before
the exit call. No syscall availability or termination assertion is required.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.Process.Syscall

/-- Every finite trace at a known Linux exit instruction is empty or its exact
exit event. The environment cannot admit a later process transition. -/
theorem runs_exit {c trapped : Core} {s : Syscall.State} {status : Nat}
    {events : List Event} {final : PState isa Env.linux}
    (trappedStep : step c s.memory = .syscall trapped)
    (requested : request trapped = some (.exit status))
    (execution : Proc.Runs isa Env.linux ⟨c, s⟩ events final) :
    events = [] ∨ events = [.exit (status % 256)] := by
  cases execution with
  | refl => exact .inl rfl
  | @cons _ next _ _ _ first rest =>
    obtain ⟨nextCore, nextEnv⟩ := next
    obtain ⟨_, returned | exiting⟩ := (step_iff_of_syscall trappedStep requested).mp first
    · obtain ⟨_, _, _, effect, _⟩ := returned
      change Syscall.Step _ (.exit status) _ (.returned _) _ at effect
      cases effect
    · obtain ⟨event, code, headEvents, effect, _⟩ := exiting
      change Syscall.Step _ (.exit status) event (.exited code) _ at effect
      cases effect
      obtain ⟨empty, _⟩ := Proc.runs_from_exited rfl rest
      exact .inr (by simp only [headEvents, empty, List.append_nil])

end Silmaril.Process.CLI.X86Linux
