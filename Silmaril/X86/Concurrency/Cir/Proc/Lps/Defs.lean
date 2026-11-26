module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
public import Silmaril.Process.LpsBridge.Defs

/-!
# Process-level threads and LPS: the arms they share

The thread layer (`Proc.PStep`) is an extension of LPS's
single-task model (silmaril's port, which cannot be edited here). On the numbers it owns, LPS's
native x86-64 table (`LpsBridge.spec`) either

* agrees with the single-threaded view `Proc.SoloStep`: `gettid` (186) and
  `set_tid_address` (218) return the pinned thread id and change nothing (`TidArm`; LPS does
  not record the `clear_child_tid` address, and with one thread the clear never happens,
  since Linux clears only when the address space has other users); at the first observation
  LPS picks an id in `(0, 2^22)` and pins it (`TidArmFresh`); `exit` (60) and `exit_group`
  (231) halt with the low eight bits of the status (`ExitArm`);
* or has the `unmodeled` outcome: `clone` (56), `futex` (202), `clone3` (435)
  (`PendingArms`), which is what `LpsBridge.no_thread_of_psafe` uses.

The theorems are in `Proc/Lps/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Proc.Lps

open Silmaril.Process.LPS
open Silmaril.Process.LpsBridge (spec)

/-- At number `n`, with a pinned thread id, LPS returns it and changes nothing. -/
def TidArm (n : Nat) : Prop :=
  ∀ (i : SyscallInput) (m : Model) (tid : Word) (o : Silmaril.Process.LPS.Outcome SyscallEffect),
    i.sysno.toNat = n → m.tid = some tid → (spec i m o ↔ o = .ok (mkEffect tid [] []) m [])

/-- At number `n`, at the first observation, LPS picks an id in `(0, 2^22)` and pins it. -/
def TidArmFresh (n : Nat) : Prop :=
  ∀ (i : SyscallInput) (m : Model) (o : Silmaril.Process.LPS.Outcome SyscallEffect), i.sysno.toNat = n →
    m.tid = none → (spec i m o ↔ ∃ tid : Word, 0 < uns tid ∧ uns tid < PID_MAX_ENVELOPE ∧
      o = .ok (mkEffect tid [] []) (m.withTid tid) [])

/-- `exit` and `exit_group` halt with the low eight bits of the status. -/
def ExitArm : Prop :=
  ∀ (i : SyscallInput) (m : Model) (o : Silmaril.Process.LPS.Outcome SyscallEffect),
    (i.sysno.toNat = nrExit ∨ i.sysno.toNat = nrExitGroup) →
      (spec i m o ↔ o = .ok (mkEffect 0 [] []) (m.withHalted (i.arg 0 &&& 255)) [])

/-- `clone`, `futex` and `clone3` have the `unmodeled` outcome. -/
def PendingArms : Prop :=
  ∀ (i : SyscallInput) (m : Model),
    (i.sysno.toNat = nrClone ∨ i.sysno.toNat = nrFutex ∨ i.sysno.toNat = nrClone3) →
      spec i m .unmodeled

end Silmaril.X86.Concurrency.Cir.Proc.Lps
