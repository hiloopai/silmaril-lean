module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Sys.AccessGate

/-!
# LPS in Lean: `futex`

Translation of LPS `Sys/Kernel/Futex/Syscalls.v` (upstream commit `f1006fe8`), the
specification of Linux `kernel/futex/syscalls.c`.

The waiter set of a private futex key is empty in this model (one task, and no `clone` that
grants `CLONE_VM`, `Sys/Kernel/Futex/Syscalls.v:21-67`). So:

* `FUTEX_WAKE_PRIVATE` answers 0 (no waiter to wake) once `get_futex_key` has passed: the
  address is aligned (`-EINVAL` otherwise) and passes `access_ok` (`-EFAULT` otherwise). The
  word itself is never read, so an aligned in-range address with nothing mapped answers 0.
* `FUTEX_WAIT_PRIVATE` with a NULL timeout reads the word: `-EAGAIN` when it does not hold
  `val`, and `unmodeled` when it does (the caller would block forever) or when the word is not
  readable (an absent byte is an absent fact).
* every other op word, and a WAIT with a timeout, is `unmodeled`. The op word is compared
  whole (all 64 bits), stricter than the kernel's `int` reading: fail closed.

## x86-64

`futex` is number 202 on x86-64 (`arch/x86/entry/syscalls/syscall_64.tbl`) and takes the same
arguments; the op words, `FUTEX_PRIVATE_FLAG` and the 4-byte word are the same
(`include/uapi/linux/futex.h`). The one difference is `access_ok`: `get_futex_key` calls
`access_ok(uaddr, size)` with `size = futex_size(flags) <= 8`, the small constant-size case of
x86-64 `__access_ok`, so `futexSpecX86` gates with `accessGateSmallX86` (see
`Silmaril.Process.LPS.Sys.AccessGate`). For an aligned word that is the single address
`TASK_SIZE_MAX` (declined), and above it `-EFAULT`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Kernel/Futex/Syscalls.v:82` `futex_aligned_b`: `get_futex_key`'s
`address % size` test. -/
def futexAlignedB (uaddr : Word) : Bool := uns uaddr % FUTEX_WORD_SIZE == 0

/-- LPS `Sys/Kernel/Futex/Syscalls.v:117` `futex_key_check`, over the `access_ok` gate:
alignment (`-EINVAL`) first, then `access_ok` (`-EFAULT`), then the command. -/
def futexKeyCheckWith (gate : AccessGate) (uaddr : Word) (k : Sys SyscallEffect) :
    Sys SyscallEffect :=
  if !futexAlignedB uaddr then errRet EINVAL
  else gate uaddr FUTEX_WORD_SIZE k

/-- LPS `Sys/Kernel/Futex/Syscalls.v:117` `futex_key_check`. -/
def futexKeyCheck (uaddr : Word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  futexKeyCheckWith accessGateLps uaddr k

/-- LPS `Sys/Kernel/Futex/Syscalls.v:150` `futex_wake_private_spec`, over the gate: no waiter,
so 0 woken; the count argument is not read. -/
def futexWakePrivateSpecWith (gate : AccessGate) (uaddr : Word) : Sys SyscallEffect :=
  futexKeyCheckWith gate uaddr (retOnly 0)

/-- LPS `Sys/Kernel/Futex/Syscalls.v:156` `FUTEX_WORD_SIZE_nat`. -/
def FUTEX_WORD_SIZE_nat : Nat := 4

/-- LPS `Sys/Kernel/Futex/Syscalls.v:158` `futex_word_size_nat_ok`. -/
theorem futex_word_size_nat_ok : (FUTEX_WORD_SIZE_nat : Int) = FUTEX_WORD_SIZE := rfl

/-- LPS `Sys/Kernel/Futex/Syscalls.v:201` `futex_wait_private_spec`, over the gate: `-EAGAIN`
when the word does not hold `val`; `unmodeled` when it does (the caller blocks and nothing
wakes it) and when the word is not readable. The read is recorded as a copy-in. -/
def futexWaitPrivateSpecWith (gate : AccessGate) (uaddr val : Word) : Sys SyscallEffect :=
  futexKeyCheckWith gate uaddr do
    let i ← input
    match readBytesMap i.mem uaddr (zw FUTEX_WORD_SIZE) with
    | none => unmodeled
    | some uval =>
      recordCopyins [(uaddr, FUTEX_WORD_SIZE_nat)]
        (if leBytesToWord uval == val then unmodeled else errRet EAGAIN)

/-- LPS `Sys/Kernel/Futex/Syscalls.v:269` `futex_spec`, over the gate: the op word decides,
compared whole; the timeout is read only for a wait. -/
def futexSpecWith (gate : AccessGate) (uaddr op val utime : Word) : Sys SyscallEffect :=
  if op == zw FUTEX_WAKE_PRIVATE then futexWakePrivateSpecWith gate uaddr
  else if op == zw FUTEX_WAIT_PRIVATE then
    (if !wIs0 utime then unmodeled else futexWaitPrivateSpecWith gate uaddr (abiLow32 val))
  else unmodeled

/-- LPS `Sys/Kernel/Futex/Syscalls.v:150` `futex_wake_private_spec`. -/
def futexWakePrivateSpec (uaddr : Word) : Sys SyscallEffect :=
  futexWakePrivateSpecWith accessGateLps uaddr

/-- LPS `Sys/Kernel/Futex/Syscalls.v:201` `futex_wait_private_spec`. -/
def futexWaitPrivateSpec (uaddr val : Word) : Sys SyscallEffect :=
  futexWaitPrivateSpecWith accessGateLps uaddr val

/-- LPS `Sys/Kernel/Futex/Syscalls.v:269` `futex_spec`. -/
def futexSpec (uaddr op val utime : Word) : Sys SyscallEffect :=
  futexSpecWith accessGateLps uaddr op val utime

/-- x86-64 `futex` (202): LPS's `futex_spec` with the x86-64 small-access `access_ok` gate. -/
def futexSpecX86 (uaddr op val utime : Word) : Sys SyscallEffect :=
  futexSpecWith accessGateSmallX86 uaddr op val utime

/-- LPS `Sys/Kernel/Futex/Syscalls.v:296` `futex_wait_reads_b`, over the `access_ok` test:
the arguments of a call that reads the futex word. -/
def futexWaitReadsBWith (ok : Word → Int → Bool) (uaddr op utime : Word) : Bool :=
  (op == zw FUTEX_WAIT_PRIVATE) && wIs0 utime && futexAlignedB uaddr && ok uaddr FUTEX_WORD_SIZE

/-- LPS `Sys/Kernel/Futex/Syscalls.v:296` `futex_wait_reads_b`. -/
def futexWaitReadsB (uaddr op utime : Word) : Bool := futexWaitReadsBWith accessOkb uaddr op utime

/-- x86-64 form of `futex_wait_reads_b`: the word is read only when the whole range passes
(`accessGateSmallX86` declines the band where only the base does). -/
def futexWaitReadsBX86 (uaddr op utime : Word) : Bool :=
  futexWaitReadsBWith accessOkbX86 uaddr op utime

/-- LPS `Sys/Kernel/Futex/Syscalls.v:303` `futex_wake_not_wait`. -/
theorem futex_wake_not_wait (op : Word) (h : (op == zw FUTEX_WAKE_PRIVATE) = true) :
    (op == zw FUTEX_WAIT_PRIVATE) = false := by
  have : op = zw FUTEX_WAKE_PRIVATE := by simpa using h
  subst this
  decide

/-! ## Table arms -/

/-- LPS `Sys/SyscallTable.v:77`: the `futex` arm, asm-generic number 98. -/
def futexLpsArms : List SpecArm :=
  [arm 98 "futex" fun i => futexSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)]

/-- The `futex` arm at its native x86-64 number, 202, with the x86-64 `access_ok` gate. -/
def futexX86Arms : List SpecArm :=
  [arm 202 "futex" fun i => futexSpecX86 (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)]

end Silmaril.Process.LPS
