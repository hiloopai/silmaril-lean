module

public import Silmaril.Proofs.Process.LpsBridge.Syscall
public import Silmaril.Proofs.Process.LpsBridge.Launch
public import Silmaril.Process.LPS.Equivalence

/-!
# Proofs: total correctness across the bridge (`MustExitInAt`)

LPS's must-exit tier (`Silmaril.Process.LPS.MustExitInAt`, LPS `MustExit.v:929`) is inductive:
every execution exits normally with a status in the allowed list, never errors and never
stalls. This file gives the program-independent bridge for exit-only tails:

* `mustExit_exit`: an aligned configuration at `0F 05` with `rax ∈ {60, 231}` must exit with
  status `rdi &&& 255` (the trap step, then the `exit` step).
* **`mustExit_of_run`**: if the open machine runs in `k` steps from the state of an aligned
  configuration to such an `exit` request, the configuration must exit with that status. Each
  open step is LPS's only step (`sstep_open`), so the induction is on `k`.
* `mustExit_of_launch`: the whole-process form (for every oracle), from a terminating open run
  of the launch state.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Process.LpsBridge

variable {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}

theorem run_succ {k : Nat} {m m' : MState}
    (h : Silmaril.Machine.Execution.run Silmaril.X86.Open.step (k + 1) m = some m') :
    ∃ m₁, Silmaril.X86.Open.step m = some m₁ ∧
      Silmaril.Machine.Execution.run Silmaril.X86.Open.step k m₁ = some m' := by
  simp only [Silmaril.Machine.Execution.run] at h
  cases hs : Silmaril.X86.Open.step m with
  | none => simp [hs] at h
  | some m₁ => simp only [hs] at h; exact ⟨m₁, rfl, h⟩

/-- **The `exit` request must exit.** -/
theorem mustExit_exit {c : Config (machine oracle)} {m : MState} (al : Aligned c m)
    (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231) :
    MustExitInAt segs spec refused [m.core.read .rdi &&& 255] c := by
  obtain ⟨hstep, uniq⟩ := sstep_trap (segs := segs) (refused := refused) al ht
  have hno : (trapRequest (segs := segs) c m).sysno.toNat = 60 ∨
      (trapRequest (segs := segs) c m).sysno.toNat = 231 := number
  have harg : (trapRequest (segs := segs) c m).arg 0 = m.core.read .rdi := rfl
  have svc : (machine oracle).svcPending (trapCfg c m).ms = some (m.core.read .rax) := rfl
  have disp := fun o => exit_dispatch (trapRequest (segs := segs) c m) c.model o hno
  have halive := al.alive
  refine .running al.alive ⟨_, _, hstep⟩ (fun evs herr => by cases (uniq _ _ herr).2) ?_
  intro evs c' hs
  obtain ⟨-, e⟩ := uniq _ _ hs
  cases e
  -- the trap configuration
  refine .running al.alive ⟨_, _, SStep.exit (code := m.core.read .rdi &&& 255) al.alive svc
    ((disp _).2 (by rw [harg])) (by simp [Model.withHalted, Model.halted])
    (by simp [Model.withHalted, Model.killedBy])⟩ ?_ ?_
  · intro evs herr
    cases herr with
    | instrFault _ p => rw [svc] at p; cases p
    | instrUnmodeled _ p => rw [svc] at p; cases p
    | syscallMaterializationFault _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.halted] at hh
    | syscallUnmodeled _ p hs =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
  · intro evs c'' hs
    cases hs with
    | instr _ p => rw [svc] at p; cases p
    | syscall _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.halted] at hh
    | exit _ p hs hh hk =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      refine .halted hh ?_ hk
      simp only [Model.withHalted, Model.halted, Option.some.injEq] at hh
      rw [← hh, harg]; exact List.mem_singleton_self _
    | killed _ p hs hk =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.killedBy] at hk

/-- **A terminating open run to an `exit` request must exit.** -/
theorem mustExit_of_run : ∀ (k : Nat) {c : Config (machine oracle)} {m m' : MState},
    Aligned c m → Silmaril.Machine.Execution.run Silmaril.X86.Open.step k m = some m' → AtSyscall m' →
    ((m'.core.read .rax).toNat = 60 ∨ (m'.core.read .rax).toNat = 231) →
    MustExitInAt segs spec refused [m'.core.read .rdi &&& 255] c
  | 0, c, m, m', al, hr, ht, hn => by
    simp only [Silmaril.Machine.Execution.run, Option.some.injEq] at hr
    subst hr
    exact mustExit_exit al ht hn
  | k + 1, c, m, m', al, hr, ht, hn => by
    obtain ⟨m₁, hs, hr'⟩ := run_succ hr
    obtain ⟨hstep, uniq⟩ := sstep_open (segs := segs) (refused := refused) al hs
    refine .running al.alive ⟨_, _, hstep⟩ (fun evs herr => by cases (uniq _ _ herr).2) ?_
    intro evs c' hs'
    obtain ⟨-, e⟩ := uniq _ _ hs'
    cases e
    exact mustExit_of_run k ⟨rfl, al.alive, al.lazy⟩ hr' ht hn

/-- **The must-exit tier of a launch**, from a terminating open run of its launch state to an
`exit(code)` request: for every flag oracle and refusal filter, the launched configuration
must exit with `code`. -/
theorem mustExit_of_launch {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput}
    {limit : Int} {k : Nat} {m' : MState}
    (hr : Silmaril.Machine.Execution.run Silmaril.X86.Open.step k (launchState snapshot en inp) = some m')
    (ht : AtSyscall m') (hn : (m'.core.read .rax).toNat = 60 ∨ (m'.core.read .rax).toNat = 231)
    (oracle : Oracle) (refused : RefusalFilter) :
    MustExitInAt snapshot.image.segments spec refused [m'.core.read .rdi &&& 255]
      (X86Launch.init (machine oracle) snapshot en limit inp) :=
  mustExit_of_run k (init_aligned oracle snapshot en limit inp) hr ht hn

end Silmaril.Proofs.Process.LpsBridge
