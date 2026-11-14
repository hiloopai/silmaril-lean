module

public import Silmaril.Machine.Abi.FsBase.Defs
/-! # The FFI thread pointer and the machine's FS base: theorems

* `ffiExecute_carried`, `callModel_carried` (PROVED, by construction): every final state of
  `Open.ffiExecute` / `OpenMachine.callModel` carries the FFI-only state of the initial one,
  whatever the code does. These are the obligations met **by the model**.
* `reaches_fsBase`, `ffiExecute_fsBase`, `callModel_fsBase` (conditional on
  `Task.openStepKeepsFs`): the machine FS base is preserved, and a coherent initial state
  (`FsCoherent`) gives a coherent final state, so `Ffi.Return.threadPointer` is then a fact
  about the register `%fs:` operands read.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.FsBase

open Silmaril.X86 (MState)
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.Machine.Abi.OpenMachine (callModel RunsIn FirstReturn)

theorem ffiExecute_carried {call : Ffi.Call} {final : Ffi.State}
    (h : Open.ffiExecute call final) : Carried call.initial final := by
  obtain ⟨-, e⟩ := h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem callModel_carried {s t : Ffi.State} (h : t ∈ callModel s) : Carried s t := by
  obtain ⟨-, e⟩ := h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reaches_fsBase (task : Task.openStepKeepsFs) :
    ∀ (n : Nat) (m m' : MState), Silmaril.Machine.Execution.run Open.step n m = some m' →
      m'.core.fsBase = m.core.fsBase := by
  intro n
  induction n with
  | zero => intro m m' h; cases h; rfl
  | succ n ih =>
    intro m m' h
    simp only [Silmaril.Machine.Execution.run_succ] at h
    cases hs : Open.step m with
    | none => simp [hs] at h
    | some m₁ =>
      rw [hs, Option.bind_some] at h
      rw [ih m₁ m' h, task m m₁ hs]

theorem runsIn_fsBase (task : Task.openStepKeepsFs) {P : MState → Prop} {m t : MState}
    (h : RunsIn P m t) : t.core.fsBase = m.core.fsBase := by
  induction h with
  | refl => rfl
  | step _ hs _ ih => rw [ih, task _ _ hs]

/-- Conditional on `Task.openStepKeepsFs`: the typed FFI execution keeps the machine FS base,
and keeps the entry invariant. -/
theorem ffiExecute_fsBase (task : Task.openStepKeepsFs) {call : Ffi.Call} {final : Ffi.State}
    (coh : FsCoherent call.initial) (h : Open.ffiExecute call final) :
    final.machine.core.fsBase = call.initial.machine.core.fsBase ∧ FsCoherent final := by
  have hc := ffiExecute_carried h
  obtain ⟨⟨n, hrun⟩, -⟩ := h
  have hm := reaches_fsBase task n _ _ hrun
  refine ⟨hm, ?_⟩
  unfold FsCoherent
  rw [hc.fsBase, hm]
  exact coh

/-- Conditional on `Task.openStepKeepsFs`: the open machine's call relation keeps the machine
FS base, and keeps the entry invariant. -/
theorem callModel_fsBase (task : Task.openStepKeepsFs) {s t : Ffi.State}
    (coh : FsCoherent s) (h : t ∈ callModel s) :
    t.machine.core.fsBase = s.machine.core.fsBase ∧ FsCoherent t := by
  have hm := runsIn_fsBase task h.1.1
  refine ⟨hm, ?_⟩
  unfold FsCoherent
  rw [(callModel_carried h).fsBase, hm]
  exact coh

end Silmaril.Machine.Abi.FsBase
