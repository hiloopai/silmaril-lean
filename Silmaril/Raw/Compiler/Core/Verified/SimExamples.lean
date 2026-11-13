module

public import Silmaril.Compiler.Core.Verified.Sim.Defs
/-! # A nonterminating simulation instance

This check prevents the framework from relying on empty matches, bounded fuel,
empty memory, or termination. It relates a real Lir backedge to a Core self-step.
A source `run` backedge supplies the latter through `step_run_empty`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Sim.Examples

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open Spec
open Relation

/-- A real jump, executed at runtime on every iteration. -/
def loop : Lir.Prog Nat := ⟨[⟨[], 0, [⟨[], .jump 0⟩]⟩]⟩

def loopState (memory : Lir.Memory) : Lir.State Nat :=
  ⟨⟨0, 0, 0⟩, Lir.Frame.empty, [], memory⟩

theorem loop_step (memory : Lir.Memory) :
    Lir.Step loop (loopState memory) (loopState memory) := rfl

/-- Any actual source self-step admits a nonempty relation to the Lir loop.
The relation is witnessed at the stated pair, and all terminal obligations are
impossible because the target executes its backedge. -/
def loopSimulation (file : Program) (labels : Labels) (c : CState)
    (memory : Lir.Memory) (source : coreStep file labels c c) :
    Simulation file labels loop :=
  Simulation.ofSteps file labels loop
    (fun s t => s = loopState memory ∧ t = c) (fun _ => 0)
    (by
      rintro s t s' ⟨rfl, rfl⟩ step
      have same := Lir.Step.deterministic step (loop_step memory)
      subst s'
      exact ⟨_, .inl ⟨rfl, rfl⟩, .inl (.single source)⟩)
    (by
      rintro s t vs mem ⟨rfl, rfl⟩ halt
      rw [show Lir.step loop (loopState memory) = .running (loopState memory) from loop_step memory] at halt
      cases halt)
    (by
      rintro s t mem ⟨rfl, rfl⟩ halt
      rw [show Lir.step loop (loopState memory) = .running (loopState memory) from loop_step memory] at halt
      cases halt)
    (by
      rintro s t ⟨rfl, rfl⟩ halt
      rw [show Lir.step loop (loopState memory) = .running (loopState memory) from loop_step memory] at halt
      cases halt)

/-- This instance actually transfers an infinite trace; the premise is one
Core step, not the desired infinite trace or whole-program correctness. -/
theorem loop_allowed (file : Program) (labels : Labels) (c : CState)
    (memory : Lir.Memory) (source : coreStep file labels c c) :
    AllowedFrom file labels c .diverges := by
  have target : Lir.Behaves loop (loopState memory) .diverges :=
    ⟨fun _ => loopState memory, rfl, fun _ => loop_step memory⟩
  exact (loopSimulation file labels c memory source).behaves (.inl ⟨rfl, rfl⟩) target rfl

def coreBody (label : Sym) : EE := .mk [] (.run () label [])

def coreLabels (label : Sym) : Labels := Map.ofList [(label, ([], coreBody label))]

/-- Include a procedure boundary, so the check exercises the saved-label
environment belonging to a procedure rather than a hard-coded empty stack. -/
def coreLoopState (label : Sym) (memory : Mem.Concrete.State) (env : Env) : CState :=
  ⟨.effectExpr (coreBody label) env, [.procedureReturn (coreLabels label)], memory⟩

theorem core_loop_step (file : Program) (label : Sym) (memory : Mem.Concrete.State) (env : Env) :
    coreStep file (coreLabels label) (coreLoopState label memory env) (coreLoopState label memory env) := by
  refine ⟨.tau, ?_⟩
  apply step_run_empty
  simp [jumpDestination, procedureContext, coreLabels, Map.ofList, extendEnv]

/-- All premises of the generic simulation are inhabited by actual Core/Lir
program steps, for arbitrary source objects, environments and target memory. -/
theorem saved_label_loop_allowed (file : Program) (label : Sym)
    (memory : Mem.Concrete.State) (env : Env) (linear : Lir.Memory) :
    AllowedFrom file (coreLabels label) (coreLoopState label memory env) .diverges :=
  loop_allowed file (coreLabels label) (coreLoopState label memory env) linear
    (core_loop_step file label memory env)

end Silmaril.Compile.Core.Verified.Sim.Examples
