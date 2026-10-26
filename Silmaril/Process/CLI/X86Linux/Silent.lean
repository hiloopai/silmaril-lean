module

public import Silmaril.Process.CLI.X86Linux.ExtStep
public import Silmaril.Process.CLI.Env.MemoryLens

/-! # Completed Ext executions as silent CLI process segments

These adapters consume actual finite retirements. `Ext.Returns` includes a
final RET, which is another internal process instruction, not a process exit.
The endpoint is exactly the environment's memory replacement through an
explicit lawful lens. No syscall, reply or observation is introduced. For a
generic environment, hidden state is specified only by that exact endpoint;
the concrete Linux replacement also preserves every descriptor.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.X86 (MState Word)
open Silmaril.Machine.Execution (run)

variable {E : Env}

/-- Adapt exactly the successful Ext retirements, with no observable events. -/
theorem runs_of_ext_run (lens : E.MemoryLens) {exit : Word} {n : Nat}
    {initial final : MState} {s : E.State}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (executed : run (X86.Ext.stepOpt exit) n initial = some final) :
    Proc.Runs isa E ⟨initial.core, s⟩ [] ⟨final.core, E.withMemory s final.memory⟩ := by
  induction n generalizing initial s with
  | zero =>
    simp only [run] at executed
    cases Option.some.inj executed
    rw [← memory, lens.withMemory_self]
    exact .refl _
  | succ n ih =>
    simp only [run] at executed
    cases first : X86.Ext.stepOpt exit initial with
    | none => simp [first] at executed
    | some next =>
      simp only [first, Option.bind_some] at executed
      have head : Proc.Step isa E ⟨initial.core, s⟩ []
          ⟨next.core, E.withMemory s next.memory⟩ := by
        apply Proc.Step.retire running
        rw [memory]
        exact (step_of_ext_retired (X86.Ext.stepOpt_eq_some_iff.mp first)).symm
      have tail := ih
        ((lens.exited_withMemory s next.memory).trans running)
        (lens.memory_withMemory s next.memory) executed
      rw [lens.withMemory_withMemory] at tail
      exact .cons head tail

/-- Include the final RET, retaining the exact post-return core and memory. -/
theorem runs_of_ext_returns (lens : E.MemoryLens) {exit : Word}
    {initial final : MState} {s : E.State}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (returned : X86.Ext.Returns exit initial final) :
    Proc.Runs isa E ⟨initial.core, s⟩ [] ⟨final.core, E.withMemory s final.memory⟩ := by
  obtain ⟨n, mid, executed, returned⟩ := returned
  have firstRun := runs_of_ext_run lens running memory executed
  have last : Proc.Step isa E ⟨mid.core, E.withMemory s mid.memory⟩ []
      ⟨final.core, E.withMemory (E.withMemory s mid.memory) final.memory⟩ := by
    apply Proc.Step.retire ((lens.exited_withMemory s mid.memory).trans running)
    rw [lens.memory_withMemory]
    exact (step_of_ext_returned returned).symm
  rw [lens.withMemory_withMemory] at last
  exact firstRun.append (.single last)

/-- A continuation observes precisely its own trace after a completed callee. -/
theorem continue_of_ext_returns (lens : E.MemoryLens) {exit : Word}
    {initial final : MState} {s : E.State} {target : PState isa E}
    {events : List Syscall.Event}
    (running : E.exited s = none) (memory : E.memory s = initial.memory)
    (returned : X86.Ext.Returns exit initial final)
    (continuation : Proc.Runs isa E ⟨final.core, E.withMemory s final.memory⟩ events target) :
    Proc.Runs isa E ⟨initial.core, s⟩ events target :=
  (runs_of_ext_returns lens running memory returned).append continuation

/-- For the concrete Linux environment the endpoint changes no descriptors or
exit state. The other Linux ladder environments use this same record update. -/
theorem linux_endpoint_preserved (s : Syscall.State) (memory : Memory) :
    (Env.linux.withMemory s memory).descriptors = s.descriptors ∧
      (Env.linux.withMemory s memory).exited = s.exited :=
  ⟨rfl, rfl⟩

end Silmaril.Process.CLI.X86Linux
