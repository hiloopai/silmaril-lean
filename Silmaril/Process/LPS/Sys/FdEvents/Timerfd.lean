module

public import Silmaril.Process.LPS.Sys.FdEvents.Common

/-!
# LPS in Lean: `timerfd_create`

Translation of LPS `Sys/Fs/Timerfd.v` (upstream commit `f1006fe8`).

The arm models the argument rejection and nothing else, exactly as LPS does: every input that
passes the gate creates a descriptor, and `FdEntry` has no timerfd kind, so the success (and
the `EPERM` of the alarm clocks without `CAP_WAKE_ALARM`, `ENOMEM`, `EMFILE`, `ENOENT`,
`ENODEV`, all after the gate) is `unmodeled`. `flags & ~TFD_CREATE_FLAGS`, or a clock outside
`CLOCK_REALTIME`, `CLOCK_MONOTONIC`, `CLOCK_BOOTTIME`, `CLOCK_REALTIME_ALARM`,
`CLOCK_BOOTTIME_ALARM`, is `EINVAL` (`fs/timerfd.c`), one condition, before any allocation.
The alarm clocks are admitted (their answer is `EPERM` or a descriptor, both declined), not
refused.

## x86-64

`TFD_CLOEXEC`/`TFD_NONBLOCK` are `O_CLOEXEC`/`O_NONBLOCK`, with the generic values on x86-64,
the clock ids are the same, and the arm consults no user memory: the x86-64
`timerfd_create` (number 283) is LPS's specification.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys FdEvents

/-- LPS `Sys/Fs/Timerfd.v:162` `timerfd_create_einval_b`. -/
def timerfdCreateEinvalB (clkid flags : Word) : Bool :=
  !(zldiff (uns flags) TFD_CREATE_FLAGS == 0) ||
    !(uns clkid == CLOCK_REALTIME ||
      (uns clkid == CLOCK_MONOTONIC ||
        (uns clkid == CLOCK_BOOTTIME ||
          (uns clkid == CLOCK_REALTIME_ALARM || uns clkid == CLOCK_BOOTTIME_ALARM))))

/-- LPS `Sys/Fs/Timerfd.v:176` `timerfd_create_spec`. Both arguments arrive narrowed
(`clockid32`, `flag32`). -/
def timerfdCreateSpec (clkid flags : Word) : Sys SyscallEffect :=
  if timerfdCreateEinvalB clkid flags then errRet EINVAL else unmodeled

end Silmaril.Process.LPS
