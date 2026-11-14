module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Frame

/-!
# Proofs: adversarial checks of the spin mutex

* **TV rejects mutated code** (kernel `decide`): the exchange certificate of `mutex_unlock`
  against the `mov` bytes of `spin_unlock`, the `mov` certificate against the exchange bytes,
  and byte mutants of `mutex_lock` (acquire `xchg` → plain `mov`) and of `mutex_unlock`
  (`xchg` → `mov`) against their own certificates.
* **The interface constrains its code**: no `Iface` has a lock that is `skip`
  (`lockCode_ne_skip`), because the lock's postcondition must hold of the empty heap at every
  resource, including `False`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.TvCfg (tvCfg)
open Silmaril.X86.Concurrency.Cir.Prim (thr)

/-- `mutex_lock` with its acquire `xchg [rdi],eax` (`87 07`) replaced by `mov [rdi],eax`
(`89 07`). -/
def lockMovMut : List (BitVec 8) := Code.mutexLock.set 10 0x89

/-- `mutex_unlock` with `xchg [rdi],eax` replaced by `mov [rdi],eax`. -/
def unlockMovMut : List (BitVec 8) := Code.mutexUnlock.set 2 0x89

theorem rev_tv_xchgCert_movBytes :
    tvCfg (thr Prim.Code.spinUnlock) Spin.unlockCert = false := by decide +kernel
theorem rev_tv_movCert_xchgBytes :
    tvCfg (thr Code.mutexUnlock) Prim.SpinUnlock.cert = false := by decide +kernel
theorem rev_tv_lockMovMut : tvCfg (thr lockMovMut) Prim.SpinLock.cert = false := by
  decide +kernel
theorem rev_tv_unlockMovMut : tvCfg (thr unlockMovMut) Spin.unlockCert = false := by
  decide +kernel

/-- **No interface lock is `skip`.** -/
theorem rev_lockCode_ne_skip (M : Iface) (L : Nat) : M.lockCode L ≠ .skip := by
  intro e
  obtain ⟨R, hR, hF⟩ := M.lock_spec 0 (fun _ => False) hemp L Regs.zero rfl
  rw [e] at hR
  obtain ⟨_, _, _, _, h, _⟩ := sep_iff.mp ((hF _ _ _ hR).1 rfl)
  exact h

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
