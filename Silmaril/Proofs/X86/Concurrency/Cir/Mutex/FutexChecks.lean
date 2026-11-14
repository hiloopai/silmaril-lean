module

public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms

/-!
# Proofs: the Boolean checks by kernel evaluation

One `decide +kernel` per fact:

* translation validation of `fmutex_lock`, `fmutex_unlock` and `fmutex_unlock_dec` with the
  checker `TvCfg.Fx.tvFx`;
* three mutant certificates are rejected: the wait claimed to be a wake, the lock without known
  register values, and the exchange release claimed to be a plain store;
* the C11 shapes: the lock is a futex lock, the exchange unlock a futex unlock, and Drepper's
  original unlock (a release store) is not;
* the explorer (TSO store buffers, loop bound 2): one thread running `lock; unlock` on an
  unlocked mutex finishes with the lock word `0`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Futex
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (tvFx)
open Silmaril.X86.Concurrency.Cir.Prim (thr)

theorem tv_fmLock : tvFx (thr Code.fmutexLock) Lock.cert = true := by decide +kernel
theorem tv_fmUnlock : tvFx (thr Code.fmutexUnlock) Unlock.cert = true := by decide +kernel
theorem tv_fmUnlockDec : tvFx (thr Code.fmutexUnlockDec) UnlockDec.cert = true := by
  decide +kernel

theorem tv_fmLockWake : tvFx (thr Code.fmutexLock) Mutants.lockWake = false := by decide +kernel
theorem tv_fmLockNoKn : tvFx (thr Code.fmutexLock) Mutants.lockNoKn = false := by decide +kernel
theorem tv_fmUnlockStore : tvFx (thr Code.fmutexUnlock) Mutants.unlockStore = false := by
  decide +kernel

theorem tv_codeMutants :
    tvFx (thr Mutants.unlockWaitOp) Unlock.cert = false ∧
    tvFx (thr Mutants.unlockMov) Unlock.cert = false ∧
    tvFx (thr Mutants.unlockCmp1) Unlock.cert = false ∧
    tvFx (thr Mutants.lockNr203) Lock.cert = false ∧
    tvFx (thr Mutants.lockNoLock) Lock.cert = false ∧
    tvFx (thr Mutants.lockVal1) Lock.cert = false ∧
    tvFx (thr Mutants.lockJe) Lock.cert = false ∧
    tvFx (thr Mutants.decSub2) UnlockDec.cert = false := by decide +kernel

theorem shape_fmLock : c11FLockB (Tv.chain Lock.cert.start) = true := by decide +kernel
theorem shape_fmUnlock : c11FUnlockB (Tv.chain Unlock.cert.start) = true := by decide +kernel
theorem shape_fmUnlockDec : c11FUnlockB (Tv.chain UnlockDec.cert.start) = false := by
  decide +kernel

set_option maxRecDepth 100000

theorem fm_one_fin : (tsoStates 1 Prim.Clients.fuel Futex.Inst.one).any
    (fun c => c.doneB 1 && c.drainedB && Futex.Inst.unlockedB c) = true := by decide +kernel

/-! ## A contended two-thread TSO run, by schedule -/

theorem walk_reach {N : Nat} : ∀ (l : List Nat) (c : CSt),
    Csl.OReach .tso N c.ocfg (Futex.Inst.walk N c l).ocfg
  | [], _ => .refl
  | t :: ts, c => by
    simp only [Futex.Inst.walk]
    split
    · rename_i h
      rw [List.getD_eq_getElem?_getD]
      cases hc : (tsoStepT c t)[0]? with
      | none => exact walk_reach ts c
      | some e =>
        exact .step (tsoStepT_sound h.1 h.2 (List.mem_of_getElem? hc)) (walk_reach ts e)
    · exact .refl

set_option maxRecDepth 100000 in
theorem cont_checks :
    (Futex.Inst.evenC.buf.all List.isEmpty && Futex.Inst.evenC.buf.length == 2 &&
      Futex.Inst.atWait (Futex.Inst.cont1.th 1).1 &&
      memOf Futex.Inst.cont1.mem Even.m == some 2 &&
      Futex.Inst.atWake (Futex.Inst.cont2.th 0).1 && Futex.Inst.atWait (Futex.Inst.cont2.th 1).1 &&
      TvCfg.sbeq (Futex.Inst.cont3.th 0).1 .skip && TvCfg.sbeq (Futex.Inst.cont3.th 1).1 .skip &&
      Futex.Inst.cont3.buf == [[], []] &&
      memOf Futex.Inst.cont3.mem (Even.out 0) == some 0 &&
      memOf Futex.Inst.cont3.mem (Even.out 1) == some 0 &&
      memOf Futex.Inst.cont3.mem Even.m == some 0) = true := by
  decide +kernel

/-! ## A concrete x86 run of `fmutex_unlock` through its `syscall` -/

open Silmaril.X86.Concurrency.Cir.TvCfg (XStep)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (SysStep FRun Returned)

theorem wit_xs (k : Nat)
    (h : ∃ rest, Silmaril.X86.Litmus.stepSym Wit.thread [2] (Wit.core k) =
      some (Wit.nxt (Wit.core k) :: rest)) :
    XStep Wit.thread (Wit.core k) (Wit.nxt (Wit.core k)).1 (Wit.core (k + 1)) := by
  obtain ⟨rest, h⟩ := h
  exact ⟨[2], _, h, List.mem_cons_self ..⟩

theorem wit_sys : SysStep Wit.thread (Wit.core 8) (Lab.fwake 0x2000 1 0).acts Wit.fin := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, .fwake 0x2000 1 0, 0, 0, 0, _,
    Or.inr ⟨by decide +kernel, 0, by decide, ?_⟩, rfl, rfl⟩
  decide +kernel

theorem wit_run : FRun Wit.thread Wit.thread.init Wit.acts Wit.fin := by
  refine .cons (.inl (wit_xs 0 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 1 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 2 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 3 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 4 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 5 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 6 ⟨_, rfl⟩)) ?_
  refine .cons (.inl (wit_xs 7 ⟨_, rfl⟩)) ?_
  exact .cons (.inr wit_sys) .nil

theorem wit_ret : Returned Wit.thread Wit.fin := Or.inl (by decide +kernel)

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
