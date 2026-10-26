module

public import Silmaril.Process.CLI.Observation

/-! # User-mode instruction sets with a system-call ABI

An `Isa` is a user-mode thread model: a core state (registers, program
counter, flags), one-step behaviour on a core and a process memory, and the
system-call ABI (how a trapping core encodes a request, and how the reply
resumes it). The step is a relation, so a model may leave values
nondeterministic (undefined flags, an unspecified `r11` after `syscall`).

As for environments, ISA models are ordered by simulation (`Isa.Le`): a
smaller model has fewer behaviours. The trusted assumption behind a proof at
model `J` is *hardware ≼ J*; `X86.Ext` today, a Sail-derived x86 later, and
the transcription agreement of `CLI.Transcript` are points in this order.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

/-- The result of one user-mode step. `syscall core` is the core after the
trapping instruction (its program counter already past it). -/
inductive Step (Core : Type) where
  | retired (core : Core) (memory : Memory)
  | syscall (core : Core)
  | fault (fault : Fault)

structure Isa where
  Core : Type
  step : Core → Memory → Step Core → Prop
  /-- `none`: a system call outside the modeled profile (a coverage failure). -/
  request : Core → Option Request
  /-- The core after the kernel returns `result` to the trapped `core`. -/
  resume : Core → Result → Core → Prop

namespace Isa

/-- Related step results: the same memory and fault, related cores. -/
inductive StepRel {C D : Type} (rel : C → D → Prop) : Step C → Step D → Prop where
  | retired {c d m} : rel c d → StepRel rel (.retired c m) (.retired d m)
  | syscall {c d} : rel c d → StepRel rel (.syscall c) (.syscall d)
  | fault (f : Fault) : StepRel rel (.fault f) (.fault f)

structure Sim (I J : Isa) where
  rel : I.Core → J.Core → Prop
  step : ∀ {c d m o}, rel c d → I.step c m o → ∃ o', J.step d m o' ∧ StepRel rel o o'
  request : ∀ {c d}, rel c d → I.request c = J.request d
  resume : ∀ {c d r c'}, rel c d → I.resume c r c' → ∃ d', J.resume d r d' ∧ rel c' d'

def Le (I J : Isa) : Prop := Nonempty (Sim I J)

@[inherit_doc] scoped infix:50 " ≼ " => Le

def Sim.id (I : Isa) : Sim I I where
  rel := Eq
  step {c d m o} h step := ⟨o, h ▸ step, by
    cases o with
    | retired => exact .retired rfl
    | syscall => exact .syscall rfl
    | fault f => exact .fault f⟩
  request h := by rw [h]
  resume {c d r c'} h resume := ⟨c', h ▸ resume, rfl⟩

theorem StepRel.comp {C D E : Type} {r₁ : C → D → Prop} {r₂ : D → E → Prop}
    {a : Step C} {b : Step D} {c : Step E} (h₁ : StepRel r₁ a b) (h₂ : StepRel r₂ b c) :
    StepRel (fun x z => ∃ y, r₁ x y ∧ r₂ y z) a c := by
  cases h₁ with
  | retired h => cases h₂ with | retired h' => exact .retired ⟨_, h, h'⟩
  | syscall h => cases h₂ with | syscall h' => exact .syscall ⟨_, h, h'⟩
  | fault f => cases h₂ with | fault => exact .fault f

def Sim.comp {I J K : Isa} (first : Sim I J) (second : Sim J K) : Sim I K where
  rel c e := ∃ d, first.rel c d ∧ second.rel d e
  step := fun ⟨_, h₁, h₂⟩ step => by
    obtain ⟨o', step', r₁⟩ := first.step h₁ step
    obtain ⟨o'', step'', r₂⟩ := second.step h₂ step'
    exact ⟨o'', step'', r₁.comp r₂⟩
  request := fun ⟨_, h₁, h₂⟩ => (first.request h₁).trans (second.request h₂)
  resume := fun ⟨_, h₁, h₂⟩ resume => by
    obtain ⟨d', resume', r₁⟩ := first.resume h₁ resume
    obtain ⟨e', resume'', r₂⟩ := second.resume h₂ resume'
    exact ⟨e', resume'', _, r₁, r₂⟩

theorem le_refl (I : Isa) : I ≼ I := ⟨Sim.id I⟩

theorem le_trans {I J K : Isa} (h₁ : I ≼ J) (h₂ : J ≼ K) : I ≼ K :=
  let ⟨s₁⟩ := h₁
  let ⟨s₂⟩ := h₂
  ⟨s₁.comp s₂⟩

/-- Same cores and ABI, fewer step results. -/
def restrict (I : Isa) (keep : I.Core → Memory → Step I.Core → Prop) : Isa :=
  { I with step := fun c m o => I.step c m o ∧ keep c m o }

theorem restrict_le (I : Isa) (keep : I.Core → Memory → Step I.Core → Prop) :
    I.restrict keep ≼ I := by
  refine ⟨{ rel := Eq, step := ?_, request := ?_, resume := ?_ }⟩
  · intro c d m o h step
    subst h
    refine ⟨o, step.1, ?_⟩
    cases o with
    | retired => exact .retired rfl
    | syscall => exact .syscall rfl
    | fault f => exact .fault f
  · intro c d h; subst h; rfl
  · intro c d r c' h resume; subst h; exact ⟨c', resume, rfl⟩

/-- Every core and memory has some step result: the model has no gaps. Needed
for halting statements, and not inherited downward. -/
def Total (I : Isa) : Prop := ∀ c m, ∃ o, I.step c m o

end Isa

end Silmaril.Process.CLI
