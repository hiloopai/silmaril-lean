module

public import Silmaril.Proofs.Machine.Process.LpsBridge.Instr
public import Silmaril.Process.LPS.ExitBridge

/-!
# Proofs: the syscall half of the open-machine/LPS bridge, and the `exit` arm

* `halted_no_step`, `star_halted`: a halted configuration has no successor.
* **`psafe_syscall`** (the generic syscall half): an aligned configuration at `0F 05` is
  process-safe if the request LPS reads there is modelled, every outcome of the syscall table
  leaves the process unkilled, every resumed outcome keeps no lazy reservation and continues
  process-safe from the state LPS resumes with (`resume`), and every halting outcome's trace is
  allowed. It holds for every syscall number; the arms below only characterise the outcomes.
* `exit_dispatch`: numbers 60 and 231 of the native table are LPS `exit_spec` (copied from
  silmaril-lean `Process/LPS/Problems/Sha256Cli/Syscalls.lean` at rev `35a6f60`, which is not
  imported because its module pulls in the `sha256` filter's middle model).
* **`psafe_exit`** (the `exit` arm): an aligned configuration at `0F 05` with `rax ∈ {60, 231}`
  is process-safe whenever `[]` and `[exitEv (rdi &&& 255) fs]` are allowed: its only
  executions are the trap and the exit.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge

variable {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}

/-- A halted configuration has no successor. -/
theorem halted_no_step {c : Config (machine oracle)} (h : c.model.halted ≠ none)
    {evs : List Event} {st : StepTo (machine oracle)} : ¬ SStep segs spec refused c evs st := by
  intro s
  cases s with
  | instr a _ _ => exact h a
  | instrFault a _ _ => exact h a
  | instrUnmodeled a _ _ => exact h a
  | syscall a _ _ _ _ _ => exact h a
  | syscallMaterializationFault a _ _ _ _ _ => exact h a
  | exit a _ _ _ _ => exact h a
  | killed a _ _ _ => exact h a
  | syscallUnmodeled a _ _ => exact h a

theorem star_halted {c c' : Config (machine oracle)} {tr : List Event}
    (h : c.model.halted ≠ none) (s : Star segs spec refused c tr c') : tr = [] ∧ c' = c := by
  cases s with
  | refl => exact ⟨rfl, rfl⟩
  | step s₁ _ => exact absurd s₁ (halted_no_step h)

/-- The trap configuration of an aligned configuration. -/
abbrev trapCfg (c : Config (machine oracle)) (m : MState) : Config (machine oracle) :=
  ⟨⟨trapped ⟨m, none⟩ (oracle c.ms.counter), c.ms.counter + 1⟩, c.model⟩

/-- The request LPS reads at the trap of an aligned configuration. -/
abbrev trapRequest (c : Config (machine oracle)) (m : MState) : SyscallInput :=
  request (oracle := oracle) segs (trapCfg c m).ms

/-- The outcome obligations of a syscall from an aligned trap (`psafe_syscall`). -/
def Outcomes (segs : List Segment) (refused : RefusalFilter) (Allowed : List Event → Prop)
    (c : Config (machine oracle)) (m : MState) : Prop :=
  ∀ eff model' evs, spec (trapRequest (segs := segs) c m) c.model (.ok eff model' evs) →
    model'.killedBy = none ∧
    (model'.halted = none → model'.vmLazy = [] ∧
      (¬ refused (trapRequest (segs := segs) c m) c.model eff →
        ∀ c' : Config (machine oracle),
          Aligned c' (resume (trapped ⟨m, none⟩ (oracle c.ms.counter)) eff) → c'.model = model' →
          PSafe segs refused (fun tr => Allowed (evs ++ tr)) c')) ∧
    (∀ code, model'.halted = some code → Allowed (evs ++ [.exitEv code model'.fs]))

/-- Steps from the trap configuration. -/
theorem trap_steps {Allowed : List Event → Prop} {c : Config (machine oracle)} {m : MState}
    (hunmod : ¬ spec (trapRequest (segs := segs) c m) c.model .unmodeled)
    (hok : Outcomes segs refused Allowed c m) (hA : Allowed []) :
    (∀ tr c', Star segs spec refused (trapCfg c m) tr c' → Allowed tr) ∧
      ∀ tr c' evs, Star segs spec refused (trapCfg c m) tr c' →
        ¬ SStep segs spec refused c' evs .error := by
  have svc : (machine oracle).svcPending (trapCfg c m).ms = some (m.core.read .rax) := rfl
  constructor
  · intro tr c' hstar
    cases hstar with
    | refl => exact hA
    | step s rest =>
      cases s with
      | instr _ p => rw [svc] at p; cases p
      | @syscall _ _ x8 eff model' model'' evs _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        obtain ⟨lazy, cont⟩ := hres hh
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ lazy] at hmat
        cases hmat
        exact (cont hr _ ⟨rfl, hh, lazy⟩ rfl).1 _ _ rest
      | @exit _ _ x8 eff model' evs code _ p hs hh hk =>
        rw [svc] at p; cases p
        obtain ⟨rfl, rfl⟩ := star_halted (by simp [hh]) rest
        rw [List.append_nil]
        exact (hok _ _ _ hs).2.2 code hh
      | @killed _ _ x8 eff model' evs sig _ p hs hk =>
        rw [svc] at p; cases p
        rw [(hok _ _ _ hs).1] at hk; cases hk
  · intro tr c' evs hstar herr
    cases hstar with
    | refl =>
      cases herr with
      | instrFault _ p => rw [svc] at p; cases p
      | instrUnmodeled _ p => rw [svc] at p; cases p
      | @syscallMaterializationFault _ _ x8 eff model' evs _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ (hres hh).1] at hmat
        cases hmat
      | syscallUnmodeled _ p hs => rw [svc] at p; cases p; exact hunmod hs
    | step s rest =>
      cases s with
      | instr _ p => rw [svc] at p; cases p
      | @syscall _ _ x8 eff model' model'' evs' _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        obtain ⟨lazy, cont⟩ := hres hh
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ lazy] at hmat
        cases hmat
        exact (cont hr _ ⟨rfl, hh, lazy⟩ rfl).2 _ _ _ rest herr
      | @exit _ _ x8 eff model' evs' code _ p hs hh hk =>
        obtain ⟨-, rfl⟩ := star_halted (by simp [hh]) rest
        exact halted_no_step (by simp [hh]) herr
      | @killed _ _ x8 eff model' evs' sig _ p hs hk =>
        rw [svc] at p; cases p
        rw [(hok _ _ _ hs).1] at hk; cases hk

/-- **The generic syscall half of the bridge.** An aligned configuration at `0F 05` is
process-safe if the request is modelled and the outcome obligations hold (`Outcomes`). -/
theorem psafe_syscall {Allowed : List Event → Prop} {c : Config (machine oracle)} {m : MState}
    (al : Aligned c m) (ht : AtSyscall m) (hA : Allowed [])
    (hunmod : ¬ spec (trapRequest (segs := segs) c m) c.model .unmodeled)
    (hok : Outcomes segs refused Allowed c m) : PSafe segs refused Allowed c := by
  obtain ⟨-, uniq⟩ := sstep_trap (segs := segs) (refused := refused) al ht
  have T := trap_steps hunmod hok hA
  constructor
  · intro tr c' hstar
    cases hstar with
    | refl => exact hA
    | step s rest =>
      obtain ⟨rfl, e⟩ := uniq _ _ s
      cases e
      exact T.1 _ _ rest
  · intro tr c' evs hstar herr
    cases hstar with
    | refl => cases (uniq _ _ herr).2
    | step s rest =>
      obtain ⟨rfl, e⟩ := uniq _ _ s
      cases e
      exact T.2 _ _ _ rest herr

/-! ## The `exit` arm -/

/-- Numbers 60 and 231 of the native table are LPS `exit_spec` (silmaril-lean
`Sha256Cli.exit_dispatch`, rev `35a6f60`, copied). -/
theorem exit_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 60 ∨ i.sysno.toNat = 231) :
    NativeX86.extendedSyscallSpec i m o ↔
      o = .ok (mkEffect 0 [] []) (m.withHalted (i.arg 0 &&& 255)) [] := by
  rcases number with number | number
  · simp only [NativeX86.extendedSyscallSpec, dispatch, number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o
  · simp only [NativeX86.extendedSyscallSpec, dispatch, number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o

/-- **The `exit` arm.** An aligned configuration at `0F 05` with `rax ∈ {60, 231}` is
process-safe whenever the empty trace and `[exitEv (rdi &&& 255) fs]` are allowed. -/
theorem psafe_exit {Allowed : List Event → Prop} {c : Config (machine oracle)} {m : MState}
    (al : Aligned c m) (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231)
    (hA : Allowed []) (hE : Allowed [.exitEv (m.core.read .rdi &&& 255) c.model.fs]) :
    PSafe segs refused Allowed c := by
  have hno : (trapRequest (segs := segs) c m).sysno.toNat = 60 ∨
      (trapRequest (segs := segs) c m).sysno.toNat = 231 := number
  have harg : (trapRequest (segs := segs) c m).arg 0 = m.core.read .rdi := rfl
  refine psafe_syscall al ht hA ?_ ?_
  · intro hs
    have := (exit_dispatch _ _ _ hno).1 hs
    cases this
  · intro eff model' evs hs
    have := (exit_dispatch _ _ _ hno).1 hs
    cases this
    refine ⟨?_, fun hh => by simp [Model.withHalted, Model.halted] at hh, ?_⟩
    · simp [Model.withHalted, Model.killedBy]
    · intro code hc
      simp only [Model.withHalted, Model.halted, Option.some.injEq] at hc
      subst hc
      rw [harg, List.nil_append]
      exact hE

end Silmaril.Proofs.Machine.Process.LpsBridge
