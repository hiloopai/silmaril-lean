module

public import Silmaril.Process.LPS.Uaccess

/-!
# LPS in Lean: the `access_ok` gate of a small constant-size user access

LPS tests `access_ok` before the fixed-size user accesses of `futex` (four bytes,
`Sys/Kernel/Futex/Syscalls.v:120`) and of `rt_sigprocmask`'s `oset` copy-out (eight bytes,
`Sys/Kernel/Signal.v:938`) with `State.access_okb`, the riscv64 `__access_ok`
(`include/asm-generic/access_ok.h`): `size <= limit && addr <= limit - size`.

An `AccessGate` is that test written as a continuation: it runs the rest of the call when the
range passes, and answers otherwise. `accessGateLps` is LPS's gate.

## x86-64 difference

x86-64 `__access_ok` (`arch/x86/include/asm/uaccess_64.h`) has had two branches since
"x86-64: make access_ok() independent of LAM" (around v6.4):

    if (__builtin_constant_p(size <= PAGE_SIZE) && size <= PAGE_SIZE) {
            return valid_user_address(ptr);
    } else {
            unsigned long sum = size + (__force unsigned long)ptr;
            return valid_user_address(sum) && sum >= (__force unsigned long)ptr;
    }

From v6.12 onwards (86e6b1547b3d, "x86: fix user address masking non-canonical speculation
issue", together with the later `USER_PTR_MAX` off-by-one fix), `valid_user_address(x)` is
`x <= runtime_const_ptr(USER_PTR_MAX)`, which puts the limit at `TASK_SIZE_MAX` without LAM
(`arch/x86/kernel/cpu/common.c`). Earlier two-branch kernels (about v6.4 to v6.11) used the
sign test `(long)(x) >= 0`, under which a base between `TASK_SIZE_MAX` and `2^63` passes
`access_ok`. `accessGateSmallX86` targets the v6.12+ form, in particular the v6.18 kernel
that LPS's futex window cites (`Sys/Uapi.v:948`). The `rt_sigprocmask` window (v6.10 to
v6.15, `Sys/Kernel/Signal.v:180`) partly predates v6.12; there the `-EFAULT` answer for a
base above `TASK_SIZE_MAX` still holds, but from the copy rather than from `access_ok`,
since nothing is mapped above `TASK_SIZE_MAX`. For a size the compiler sees as constant and at
most a page, only the **base** is checked: the guard page above `TASK_SIZE_MAX` makes the
overhanging access fault later, inside the copy. Kernels before the two-branch form
test the whole range (`__chk_range_not_ok`), which is `Uaccess.accessOkbX86`.

Whether the first branch is taken is a compiler fact (constant propagation into the inlined
`access_ok`), and what the overhanging access then does (a fault after a partial copy, or a
fault before any byte) is a fact about the copy routine. Neither is a fact this model can
state, and the two kernels disagree on exactly one band of addresses: a base at most
`TASK_SIZE_MAX` whose range ends above it. `accessGateSmallX86` therefore answers

* the rest of the call when the whole range is below `TASK_SIZE_MAX` (both branches pass);
* `-EFAULT` when the base itself is above `TASK_SIZE_MAX` (both branches refuse on v6.12+;
  on earlier two-branch kernels the copy faults instead);
* `unmodeled` in the band between (fail closed: the branches disagree).

The arms whose fixed-size access is a `copy_to_user`/`copy_from_user` (uname, prlimit64,
fstat, pipe2, sched_setscheduler) use the whole-range `Uaccess.accessOkbX86` instead: on x86-64
those copies go through the out-of-line `_copy_to_user`/`_copy_from_user`, so their
`access_ok` sees a non-constant size and takes the second branch (see the `x86-64 access_ok`
section of `Uaccess.lean`). `rt_sigprocmask`'s `oset` copy-out is also a `copy_to_user`
(`kernel/signal.c:3218-3220` in v6.8), so it takes the whole-range gate `accessGateX86` as
well: `-EFAULT` with nothing written whenever `Uaccess.accessOkbX86` refuses, band included.
That answer holds only for kernels whose `valid_user_address` compares against
`USER_PTR_MAX = TASK_SIZE_MAX`, the x86-64 profile of the native table (v6.13 and later in
`x86-parity.json`). It is **not** v6.8's behaviour: there `valid_user_address(x)` is the sign
test `(long)(x) >= 0` (`arch/x86/include/asm/uaccess_64.h:57`), so an `oset` in the band passes
`access_ok`, `raw_copy_to_user` writes the bytes below `TASK_SIZE_MAX` and the call returns
`-EFAULT` after that partial copy. Probes on a v6.8 host (such as this repository's 6.8.0
build machines) are outside the profile for this band. The former `accessGateSmallX86` reading
declines the band, which is sound for both kernels; it restricts the whole-range one
(`NativeX86.GapSweep.rtSigprocmask_restricts`), and in the native table the band is declined
by the boundary guard under both.

`put_user` (for instance `arch_prctl`'s `ARCH_GET_FS`/`ARCH_GET_GS`) is a single store of at
most 8 bytes after a base-only range check (`arch/x86/lib/putuser.S`, `check_range`: a sign
mask on v6.8). In the band the store reaches the never-mapped guard page at `TASK_SIZE_MAX`
and faults as a whole, so nothing is written and the answer is `-EFAULT`: the whole-range
answer, on v6.8 and on the profile alike. `NativeX86.GapSweep.getBaseSpec` therefore uses
`Uaccess.accessOkbX86` and answers the band; `accessGateSmallX86` stays the gate for accesses
whose overhanging behaviour is not argued that way.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- An `access_ok` test before a fixed-size user access, written as a continuation. -/
abbrev AccessGate := Word → Int → Sys SyscallEffect → Sys SyscallEffect

/-- LPS's gate (`Sys/Kernel/Futex/Syscalls.v:120`, `Sys/Kernel/Signal.v:938`): run the rest of
the call when `State.access_okb` passes, `-EFAULT` otherwise. -/
def accessGateLps : AccessGate := fun base len k =>
  if accessOkb base len then k else errRet EFAULT

/-- x86-64 gate for a constant size of at most a page (see the module docstring): the rest of
the call when the whole range is below `TASK_SIZE_MAX`, `-EFAULT` when the base is above it,
and `unmodeled` for a base below it whose range ends above it, where the two branches of
x86-64 `__access_ok` disagree. -/
def accessGateSmallX86 : AccessGate := fun base len k =>
  if accessOkbX86 base len then k
  else if decide (uns base ≤ taskSizeMaxX86) then unmodeled
  else errRet EFAULT

/-- x86-64 gate for a `copy_to_user`/`copy_from_user` of a constant size: the out-of-line copy
sees a non-constant size, so `access_ok` checks the whole range (`Uaccess.accessOkbX86`). The
rest of the call when the range passes, `-EFAULT` otherwise. -/
def accessGateX86 : AccessGate := fun base len k =>
  if accessOkbX86 base len then k else errRet EFAULT

/-- The undecided band of `accessGateSmallX86` is not empty: the last word below
`TASK_SIZE_MAX` straddling it. -/
theorem accessGateSmallX86_band :
    accessOkbX86 (zw (taskSizeMaxX86 - 2)) 4 = false ∧
      decide (uns (zw (taskSizeMaxX86 - 2)) ≤ taskSizeMaxX86) = true := by
  decide

end Silmaril.Process.LPS
