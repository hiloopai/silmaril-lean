module

public import Silmaril.Machine.RiscV.Ext.Machine.Defs
public import Silmaril.Machine.Behaviour.Semantics

/-!
# The `RiscV.Ext` machine as a `Behaviour.Semantics`

`Ext.sem halt trap overflow` presents the fetch/decode/execute machine
`MState.step` in the shared vocabulary of `Silmaril.Machine.Behaviour` ,
for a stub convention: the program ends by executing `EBREAK` at one of three
designated addresses. It does not depend on any compiler.

A step is a retirement, `m.step = .retired m'`. Where the machine stops, the
outcome is:

* for `EBREAK` (`Outcome.stopped`) with the PC at `halt`: `returned m`, the
  machine state at the stub;
* with the PC at `trap` (and not at `halt`): `trapped m`;
* with the PC at `overflow` (and at neither of the others): `exhausted`;
* at any other PC: `faulted .strayStop`;
* every other outcome of `MState.step` is `faulted φ` with `φ : Fault` naming
  it (fetch fault, undecodable word, misaligned target or data address, data
  fault).

The addresses are tested in the order `halt`, `trap`, `overflow`, so the
semantics is deterministic (`sem_deterministic`) even if two of them coincide.
A stop at `overflow` counts as exhaustion whatever the stack pointer is: the
stub convention does not record why the code jumped there. Every state steps or
stops (`sem_progress`).
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

open Silmaril.Machine
open Relation

/-- The outcomes of `MState.step` that neither retire nor stop, and a stop at an
undesignated address. -/
inductive Fault where
  | fetchFault
  | undecodable (word : BitVec 32)
  | targetMisaligned (instr : Instr) (target : Word)
  | dataMisaligned (instr : Instr) (address : Word)
  | dataFault (instr : Instr) (address : Word)
  /-- `EBREAK` at an address that is none of the three stubs. -/
  | strayStop

/-- The fault of an outcome other than a retirement or a stop. -/
def Outcome.fault? : Outcome → Option Fault
  | .fetchFault => some .fetchFault
  | .undecodable w => some (.undecodable w)
  | .targetMisaligned i a => some (.targetMisaligned i a)
  | .dataMisaligned i a => some (.dataMisaligned i a)
  | .dataFault i a => some (.dataFault i a)
  | .retired _ | .stopped => none

/-- The outcome shown by a state where the machine stops. -/
inductive FinalOutcome (halt trap overflow : Word) :
    MState → Behaviour.Outcome MState MState Fault → Prop where
  | returned {m : MState} (h : m.step = .stopped) (hpc : m.core.pc = halt) :
      FinalOutcome halt trap overflow m (.returned m)
  | trapped {m : MState} (h : m.step = .stopped) (hpc : m.core.pc = trap) (hh : m.core.pc ≠ halt) :
      FinalOutcome halt trap overflow m (.trapped m)
  | exhausted {m : MState} (h : m.step = .stopped) (hpc : m.core.pc = overflow)
      (hh : m.core.pc ≠ halt) (ht : m.core.pc ≠ trap) :
      FinalOutcome halt trap overflow m .exhausted
  | strayStop {m : MState} (h : m.step = .stopped) (hh : m.core.pc ≠ halt) (ht : m.core.pc ≠ trap)
      (ho : m.core.pc ≠ overflow) :
      FinalOutcome halt trap overflow m (.faulted .strayStop)
  | faulted {m : MState} {φ : Fault} (h : m.step.fault? = some φ) :
      FinalOutcome halt trap overflow m (.faulted φ)

/-- The machine with the stub convention at `halt`, `trap` and `overflow`. -/
def sem (halt trap overflow : Word) : Behaviour.Semantics MState MState MState Fault where
  step m m' := m.step = .retired m'
  final := FinalOutcome halt trap overflow

section Sem

variable {halt trap overflow : Word}

@[simp] theorem sem_step : (sem halt trap overflow).step = fun m m' => m.step = .retired m' := rfl

@[simp] theorem sem_final : (sem halt trap overflow).final = FinalOutcome halt trap overflow := rfl

theorem finalOutcome_not_retired {m : MState} {o : Behaviour.Outcome MState MState Fault}
    (h : FinalOutcome halt trap overflow m o) {m' : MState} : m.step ≠ .retired m' := by
  cases h with
  | returned h | trapped h | exhausted h | strayStop h => rw [h]; nofun
  | faulted h =>
    intro e
    rw [e] at h
    cases h

theorem sem_deterministic : (sem halt trap overflow).Deterministic where
  step_unique := RightUnique.of_injective MState.step Outcome.retired
    (fun _ _ h => Outcome.retired.inj h)
  final_unique s o o' h h' := by
    cases h with
    | returned h hpc =>
      cases h' with
      | returned => rfl
      | trapped _ _ hh | exhausted _ _ hh | strayStop _ hh => exact absurd hpc hh
      | faulted h' => rw [h] at h'; cases h'
    | trapped h hpc hh =>
      cases h' with
      | returned _ hpc' => exact absurd hpc' hh
      | trapped => rfl
      | exhausted _ _ _ ht | strayStop _ _ ht => exact absurd hpc ht
      | faulted h' => rw [h] at h'; cases h'
    | exhausted h hpc hh ht =>
      cases h' with
      | returned _ hpc' => exact absurd hpc' hh
      | trapped _ hpc' => exact absurd hpc' ht
      | exhausted => rfl
      | strayStop _ _ _ ho => exact absurd hpc ho
      | faulted h' => rw [h] at h'; cases h'
    | strayStop h hh ht ho =>
      cases h' with
      | returned _ hpc' => exact absurd hpc' hh
      | trapped _ hpc' => exact absurd hpc' ht
      | exhausted _ hpc' => exact absurd hpc' ho
      | strayStop => rfl
      | faulted h' => rw [h] at h'; cases h'
    | faulted h =>
      cases h' with
      | returned h' | trapped h' | exhausted h' | strayStop h' => rw [h'] at h; cases h
      | faulted h' => rw [h] at h'; cases h'; rfl
  final_stop _ _ h _ hs := finalOutcome_not_retired h hs

theorem sem_progress : (sem halt trap overflow).Progress := by
  classical
  intro m
  cases h : m.step with
  | retired m' => exact .inl ⟨m', h⟩
  | stopped =>
    by_cases hh : m.core.pc = halt
    · exact .inr ⟨_, .returned h hh, nofun⟩
    by_cases ht : m.core.pc = trap
    · exact .inr ⟨_, .trapped h ht hh, nofun⟩
    by_cases ho : m.core.pc = overflow
    · exact .inr ⟨_, .exhausted h ho hh ht, nofun⟩
    · exact .inr ⟨_, .strayStop h hh ht ho, nofun⟩
  | fetchFault => exact .inr ⟨_, .faulted (φ := .fetchFault) (by rw [h]; rfl), nofun⟩
  | undecodable w => exact .inr ⟨_, .faulted (φ := .undecodable w) (by rw [h]; rfl), nofun⟩
  | targetMisaligned i a =>
    exact .inr ⟨_, .faulted (φ := .targetMisaligned i a) (by rw [h]; rfl), nofun⟩
  | dataMisaligned i a =>
    exact .inr ⟨_, .faulted (φ := .dataMisaligned i a) (by rw [h]; rfl), nofun⟩
  | dataFault i a => exact .inr ⟨_, .faulted (φ := .dataFault i a) (by rw [h]; rfl), nofun⟩

end Sem

end Silmaril.RiscV.Ext
