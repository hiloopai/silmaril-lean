module

public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-!
# Proofs: the Boolean checks by kernel evaluation

One `decide +kernel` per fact:

* translation validation of `mutex_lock`, `mutex_unlock`, `mutex_unlock_sc` (the checker), and
  `mutex_lock`'s bytes are `spin_lock`'s;
* the C11 modes of the three certificates are implemented by their instructions (`modeOk1`), and a
  `seq_cst` claim on a plain `mov` store is rejected although TV accepts it;
* the C11 shapes of lock and unlock (and their failure for a relaxed exchange and a `mov`);
* the explorer (TSO store buffers, loop bound 2) on three instances of `Even`: linked with
  the spin mutex it finishes with even outputs; with empty holes (racy) it finishes with an odd
  output; with the `mov`-release unlock every finished state has even outputs and one exists.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.TvCfg (tvCfg)
open Silmaril.X86.Concurrency.Cir.Prim (thr)

/-! ## Translation validation and modes -/

theorem lock_bytes : Code.mutexLock = Prim.Code.spinLock := by decide +kernel

theorem tv_lock : tvCfg (thr Code.mutexLock) Prim.SpinLock.cert = true := by decide +kernel
theorem tv_unlock : tvCfg (thr Code.mutexUnlock) Spin.unlockCert = true := by decide +kernel
theorem tv_unlockSc : tvCfg (thr Code.mutexUnlockSc) Spin.unlockScCert = true := by
  decide +kernel

theorem modes_lock : cfgModesOk (thr Code.mutexLock) Prim.SpinLock.cert = true := by
  decide +kernel
theorem modes_unlock : cfgModesOk (thr Code.mutexUnlock) Spin.unlockCert = true := by
  decide +kernel
theorem modes_unlockSc : cfgModesOk (thr Code.mutexUnlockSc) Spin.unlockScCert = true := by
  decide +kernel

theorem movSc_tv : tvCfg (thr Prim.Code.spinUnlock) ModeMutants.movSc = true := by
  decide +kernel
theorem movSc_modes : cfgModesOk (thr Prim.Code.spinUnlock) ModeMutants.movSc = false := by
  decide +kernel

/-! ## C11 shapes -/

/-- Loop bounds do not change the accesses. -/
theorem accessesOf_setB (L : Nat) (s : Stmt) : accessesOf (TvCfg.setB L s) = accessesOf s := by
  induction s with
  | seq s t ihs iht => simp only [TvCfg.setB, accessesOf, ihs, iht]
  | ite c s t ihs iht => simp only [TvCfg.setB, accessesOf, ihs, iht]
  | loop n c b ih => simp only [TvCfg.setB, accessesOf, ih]
  | _ => rfl

theorem shape_lock : c11LockB (Tv.chain Prim.SpinLock.cert.start) = true := by decide +kernel
theorem shape_unlock : c11UnlockB (Tv.chain Spin.unlockCert.start) = true := by decide +kernel
theorem shape_unlockSc : c11UnlockB (Tv.chain Spin.unlockScCert.start) = true := by
  decide +kernel
theorem shape_mov : c11UnlockB (Tv.chain Prim.SpinUnlock.cert.start) = false := by
  decide +kernel
theorem shape_lockRlx : c11LockB ModeMutants.lockRlx = false := by decide +kernel

/-! ## The explorer -/

set_option maxRecDepth 100000

theorem link_fin : (tsoStates 2 Prim.Clients.fuel Inst.linkC).any
    (fun c => c.doneB 2 && c.drainedB && Inst.evenOuts c) = true := by decide +kernel

theorem racy_odd : (tsoStates 2 Prim.Clients.fuel Inst.racyC).any
    (fun c => c.doneB 2 && c.drainedB && !Inst.evenOuts c) = true := by decide +kernel

theorem mov_even : tsoCheck 2 Prim.Clients.fuel Inst.movC Inst.evenOuts = true := by
  decide +kernel

theorem mov_fin : (tsoStates 2 Prim.Clients.fuel Inst.movC).any
    (fun c => c.doneB 2 && c.drainedB && Inst.evenOuts c) = true := by decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
