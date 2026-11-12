module

public import Silmaril.Problems.Models.ProcX.Defs
public import Silmaril.Process.CLI.GapSim
public import Silmaril.X86.Str9FsXN.Thms

/-!
# `musl-str9fsx` fills the gaps of `musl-str9`

The longer proofs behind `Silmaril/Problems/Models/ProcX/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Problems.Models.ProcX

open Silmaril.Process.CLI
open Silmaril.Problems.Models.ProcX
open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.Process (Memory)

open Silmaril.Problems.Models

theorem userStep_of_proc {c : State} (x : XFile) {m : Memory}
    (h : Proc.userStep c m ≠ .fault .unmodeled) :
    userStep ⟨c, x⟩ m = liftStep x (Proc.userStep c m) := by
  unfold userStep Proc.userStep at *
  by_cases trap : m.fetchBytes c.rip.toNat 2 = some X86Linux.syscallBytes
  · simp [trap, liftStep]
  · simp only [trap, ite_false] at h ⊢
    cases hs : Silmaril.X86.Str9.step ⟨c, m⟩ with
    | none => rw [hs] at h; exact absurd rfl h
    | some n =>
      have := Silmaril.X86.Str9FsXN.step_of_str9fsx
        (Silmaril.X86.Str9FsX.step_of_str9fs (x := ⟨⟨c, m⟩, x⟩)
          (Silmaril.X86.Str9Fs.step_of_str9 hs))
      simp [this, liftStep]

theorem isa_step_of_proc {c : State} (x : XFile) {m : Memory} {o : Step State}
    (h : Proc.isa.step c m o) (ho : o ≠ .fault .unmodeled) :
    isa.step ⟨c, x⟩ m (liftStep x o) := by
  have hstep : Proc.isa.step c m o = match Proc.userStep c m with
      | .syscall trapped =>
        if Proc.isStartup trapped then ∃ core', Proc.Startup trapped core' ∧ o = .retired core' m
        else o = .syscall trapped
      | r => o = r := rfl
  have gstep : isa.step ⟨c, x⟩ m (liftStep x o) = match userStep ⟨c, x⟩ m with
      | .syscall trapped =>
        if Proc.isStartup trapped.core then
          ∃ c', Startup trapped c' ∧ liftStep x o = .retired c' m
        else liftStep x o = .syscall trapped
      | r => liftStep x o = r := rfl
  rw [hstep] at h
  rw [gstep]
  cases hu : Proc.userStep c m with
  | retired c' m' =>
    rw [hu] at h
    rw [userStep_of_proc x (by rw [hu]; exact nofun), hu]
    subst h; rfl
  | fault f =>
    rw [hu] at h
    subst h
    rw [userStep_of_proc x (by rw [hu]; exact ho), hu]
    rfl
  | syscall t =>
    rw [hu] at h
    rw [userStep_of_proc x (by rw [hu]; exact nofun), hu]
    simp only [liftStep]
    by_cases st : Proc.isStartup t
    · simp only [st, ite_true] at h ⊢
      obtain ⟨core', startup, rfl⟩ := h
      exact ⟨⟨core', x⟩, ⟨startup, rfl⟩, rfl⟩
    · simp only [st] at h ⊢
      subst h; rfl

theorem stepRel_liftStep (x : XFile) (o : Step State) :
    Isa.StepRel (fun (c : State) (d : Core) => d.core = c) o (liftStep x o) := by
  cases o with
  | retired c m => exact .retired rfl
  | syscall c => exact .syscall rfl
  | fault f => exact .fault f

/-- `musl-str9fsx` fills the gaps of `musl-str9`'s instruction set: related cores have the
same integer core. -/
def isaGapSim : Isa.GapSim Proc.isa isa where
  rel c d := d.core = c
  step := by
    rintro c ⟨c', x⟩ m o rfl h ho
    exact ⟨liftStep x o, isa_step_of_proc x h ho, stepRel_liftStep x o⟩
  request := by
    rintro c ⟨c', x⟩ rfl
    rfl
  resume := by
    rintro c ⟨c', x⟩ r c'' rfl resume
    exact ⟨⟨c'', x⟩, ⟨resume, rfl⟩, rfl⟩

/-- The model-level gap simulation: same environment, the loader with a zero XMM file. -/
def gapSim : Model.GapSim Proc.model model where
  isa := isaGapSim
  env := Env.Sim.id _
  envInit {_ _ s} init := ⟨s, init, rfl⟩
  load {_ _ c _} load := ⟨⟨c, fun _ => 0⟩, load, rfl⟩

theorem exitsOn_of_proc {image : Image} {stdin : List Silmaril.Process.Byte}
    (h : Proc.ExitsOn Proc.model image stdin) : Proc.ExitsOn model image stdin := by
  obtain ⟨input, x, events, y, valid, stdinEq, init, run, stop⟩ := h
  obtain ⟨x', y', init', run', stop'⟩ := gapSim.exits init run stop
  exact ⟨input, x', events, y', valid, stdinEq, init', run', stop'⟩

/-- A non-trapping `Str9FsXN` step is a step of `userStep`. -/
theorem userStep_of_step {c : Core} {m : Memory} {y : XState}
    (nontrap : m.fetchBytes c.core.rip.toNat 2 ≠ some X86Linux.syscallBytes)
    (h : Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩ = some y) :
    userStep c m = .retired ⟨y.m.core, y.xmm⟩ y.m.memory := by
  simp [userStep, nontrap, h]

theorem isa_step_of_step {c : Core} {m : Memory} {y : XState}
    (nontrap : m.fetchBytes c.core.rip.toNat 2 ≠ some X86Linux.syscallBytes)
    (h : Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩ = some y) :
    isa.step c m (.retired ⟨y.m.core, y.xmm⟩ y.m.memory) := by
  simp only [isa, userStep_of_step nontrap h]

end Silmaril.Proofs.Problems.Models.ProcX
