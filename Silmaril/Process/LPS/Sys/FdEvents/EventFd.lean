module

public import Silmaril.Process.LPS.Sys.FdEvents.Common

/-!
# LPS in Lean: `eventfd2` (and x86-64 `eventfd`)

Translation of LPS `Sys/Fs/EventFd.v` (upstream commit `f1006fe8`).

The arm models the argument rejection and nothing else, exactly as LPS does: every input that
passes the gate creates a descriptor, and `FdEntry` has no eventfd kind, so the success (and
the `ENOMEM`, `EMFILE`, `ENOENT`, `ENODEV` that sit after the gate) is `unmodeled`.
`flags & ~EFD_FLAGS_SET` is `EINVAL` (`fs/eventfd.c` `do_eventfd`), before anything is
allocated: the arm touches no memory and no state, and does not read the model. `count` is
not read on any modeled path.

## x86-64

The constants are the same on x86-64 (`EFD_CLOEXEC`/`EFD_NONBLOCK` are `O_CLOEXEC`/`O_NONBLOCK`,
whose x86-64 values are the generic ones), and the arm consults no user memory, so the x86-64
`eventfd2` (number 290) is LPS's specification. x86-64 also has the legacy `eventfd`
(number 284): `SYSCALL_DEFINE1(eventfd, unsigned int, count)` is `do_eventfd(count, 0)`,
and `0` passes the gate, so `eventfdSpecX86` is LPS's `eventfd2_spec 0`, which is
`unmodeled` (the descriptor), never `EINVAL`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys FdEvents

/-- LPS `Sys/Fs/EventFd.v:232` `eventfd2_einval_b`: `flags & ~EFD_FLAGS_SET` is non-zero. -/
def eventfd2EinvalB (flags : Word) : Bool := !(zldiff (uns flags) EFD_FLAGS_SET == 0)

/-- LPS `Sys/Fs/EventFd.v:241` `eventfd2_spec`. `flags` arrives narrowed (`flag32`). -/
def eventfd2Spec (flags : Word) : Sys SyscallEffect :=
  if eventfd2EinvalB flags then errRet EINVAL else unmodeled

/-- x86-64 `eventfd` (number 284, no riscv64 counterpart): `do_eventfd(count, 0)`. -/
def eventfdSpecX86 : Sys SyscallEffect := eventfd2Spec 0

end Silmaril.Process.LPS
