module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.MonadExt

/-!
# LPS in Lean: clocks and sleeps (`gettimeofday`, `clock_gettime`, `nanosleep`)

Translations from LPS (upstream commit `f1006fe8`):

* `Sys/Kernel/Time/Time.v`: `timeval_ok_b`, `gettimeofday_spec` (169). The wall clock is
  chosen afresh at every call; a non-NULL `tz`, a NULL `tv` and a `tv` that is not wholly
  writable decline, except that a `tv` whose first 8-byte `put_user` is refused is `EFAULT`;
* `Sys/Kernel/Time/Hrtimer.v`: `timespec_valid_b`, `nanosleep_rem_ok_b`, `nanosleep_clock`,
  `nanosleep_spec` (101). Both the completed sleep and the interruption (`EINTR`, with an
  environment-chosen remainder) are admitted; the monotonic clock `m_clock` advances by what
  is known to have elapsed;
* `Sys/Kernel/Time/PosixTimers.v`: `timespec_ok_b`, `realtime_ok_b`, `cputime_ok_b`,
  `clockid_percall_b`, `clock_gettime_spec` (113). `CLOCK_MONOTONIC` is non-decreasing and
  recorded in `m_clock`; the wall-clock, raw, coarse and boot-time ids and the process CPU
  clock are chosen per call; every other id is `unmodeled`.

## x86-64

The three syscalls are `gettimeofday` 96, `nanosleep` 35 and `clock_gettime` 228 on x86-64
(`arch/x86/entry/syscalls/syscall_64.tbl`, all `common`). The structures are the same
(`struct __kernel_old_timeval` and `struct __kernel_timespec` are two 8-byte fields on both
LP64 targets), as are the clock ids, `timespec64_valid`, the `-ERESTART_RESTARTBLOCK` to `EINTR`
rewrite (x86's `handle_signal`, `arch/x86/kernel/signal.c`, rewrites it on delivery whatever
`SA_RESTART` says) and the forward, partial `copy_to_user` that makes a torn destination
decline. `nanosleep` and `clock_gettime` consult no `access_ok`, so their specifications are
used unchanged on x86-64.

`gettimeofday` is the one difference: its `EFAULT` arm asks `access_ok` of the first
`put_user`'s 8 bytes. On x86-64 `put_user` compares no range: its `check_range`
(`arch/x86/lib/putuser.S:36`, Linux v6.18.46) only turns an address with bit 63 set into
all-ones, so whether the store at `tv` is refused depends on whether it faults. It always faults
when it touches the never-mapped guard page at `TASK_SIZE_MAX`, a non-canonical address or a
kernel address, and an x86 store that faults writes nothing. When `accessOkbX86 tv 8` fails, the first store therefore faults with
nothing written and the call is `EFAULT`, as on riscv64. `gettimeofdaySpecX86` is
`gettimeofday_spec` with `accessOkbX86` (and `copyBytesMapX86`) in place of `access_okb`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! ## `gettimeofday` (LPS `Sys/Kernel/Time/Time.v`) -/

/-- LPS `Sys/Kernel/Time/Time.v:57` `timeval_ok_b`: 16 bytes, `tv_usec` below `10^6` and
`tv_sec` below `KTIME_SEC_MAX`. -/
def timevalOkB (bs : List Byte) : Bool :=
  bs.length == 16 && decide (tvFracOf bs < 1000000) && decide (tvSecOf bs < KTIME_SEC_MAX)

/-- LPS `Sys/Kernel/Time/Time.v:186` `gettimeofday_spec`, over the `access_ok` of the
architecture (`ok`). -/
def gettimeofdaySpecWith (ok : Word → Int → Bool) (copy : (Word → Option Byte) → Word → Int →
    Option (List Byte)) (tv tz : Word) : Sys SyscallEffect :=
  if !wIs0 tz then unmodeled
  else if wIs0 tv then unmodeled
  else do
    let i ← input
    match copy i.wmem tv 16 with
    | none => if !ok tv 8 then errRet EFAULT else unmodeled
    | some _ => do
      let bs ← Sys.choose fun bs : List Byte => timevalOkB bs = true
      Sys.pure (mkEffect 0 [(tv, bs)] [])

/-- LPS `Sys/Kernel/Time/Time.v:186` `gettimeofday_spec`. -/
def gettimeofdaySpec (tv tz : Word) : Sys SyscallEffect :=
  gettimeofdaySpecWith accessOkb copyBytesMap tv tz

/-- x86-64 form of LPS `Sys/Kernel/Time/Time.v:186` `gettimeofday_spec`: x86-64 `access_ok`
(see the module docstring). -/
def gettimeofdaySpecX86 (tv tz : Word) : Sys SyscallEffect :=
  gettimeofdaySpecWith accessOkbX86 copyBytesMapX86 tv tz

/-! ## `nanosleep` (LPS `Sys/Kernel/Time/Hrtimer.v`) -/

/-- LPS `Sys/Kernel/Time/Hrtimer.v:36` `timespec_valid_b`: `timespec64_valid`, `tv_sec` not
negative and `tv_nsec` below `NSEC_PER_SEC` read unsigned. -/
def timespecValidB (bs : List Byte) : Bool :=
  decide (tvSecOf bs < 2 ^ 63) && decide (tvFracOf bs < 1000000000)

/-- LPS `Sys/Kernel/Time/Hrtimer.v:43` `nanosleep_rem_ok_b`: a remainder is 16 bytes,
normalized, strictly positive and inside the `ktime_t` envelope (not bounded by the request:
the hard expiry is the timer slack past the soft one). -/
def nanosleepRemOkB (bs : List Byte) : Bool :=
  bs.length == 16 && decide (tvFracOf bs < 1000000000) && decide (0 < timespecNs bs)
    && decide (timespecNs bs < CLOCK_NS_ENVELOPE)

/-- LPS `Sys/Kernel/Time/Hrtimer.v:186` `nanosleep_clock`: the saturated deadline less the
remainder, never behind the previous clock. -/
def nanosleepClock (prev : Word) (req rem : List Byte) : Word :=
  zw (max (uns prev) (min (uns prev + timespecKtime req) KTIME_MAX - timespecNs rem))

/-- LPS `Sys/Kernel/Time/Hrtimer.v:419` `nanosleep_spec`. -/
def nanosleepSpec (rqtp rmtp : Word) : Sys SyscallEffect := do
  let i ← input
  match readBytesMap i.mem rqtp 16 with
  | none => unmodeled
  | some req =>
    recordCopyins [(rqtp, 16)]
      (if !timespecValidB req then errRet EINVAL
      else do
        let m ← getModel
        let slept : Sys SyscallEffect := do
          setClock (nanosleepClock m.clock req [])
          retOnly 0
        if wIs0 rmtp then Sys.alt slept (errRet EINTR)
        else
          match readBytesMap i.wmem rmtp 16 with
          | none => unmodeled
          | some _ =>
            Sys.alt slept do
              let rem ← Sys.choose fun rem : List Byte => nanosleepRemOkB rem = true
              setClock (nanosleepClock m.clock req rem)
              Sys.pure (mkEffect (errnoRet EINTR) [(rmtp, rem)] []))

/-! ## `clock_gettime` (LPS `Sys/Kernel/Time/PosixTimers.v`) -/

/-- LPS `Sys/Kernel/Time/PosixTimers.v:89` `timespec_ok_b`: a `CLOCK_MONOTONIC` reading is
16 bytes, normalized, not before `prev` and inside the envelope. -/
def timespecOkB (bs : List Byte) (prev : Word) : Bool :=
  bs.length == 16 && decide (tvFracOf bs < 1000000000) && decide (uns prev ≤ timespecNs bs)
    && decide (timespecNs bs < CLOCK_NS_ENVELOPE)

/-- LPS `Sys/Kernel/Time/PosixTimers.v:149` `realtime_ok_b`: `timespec_ok_b` without the
relation to a previous reading. -/
def realtimeOkB (bs : List Byte) : Bool :=
  bs.length == 16 && decide (tvFracOf bs < 1000000000)
    && decide (timespecNs bs < CLOCK_NS_ENVELOPE)

/-- LPS `Sys/Kernel/Time/PosixTimers.v:227` `cputime_ok_b`: the envelope on the signed
reading, two-sided. -/
def cputimeOkB (bs : List Byte) : Bool :=
  bs.length == 16 && decide (tvFracOf bs < 1000000000)
    && decide (-CLOCK_NS_ENVELOPE ≤ timespecNsSigned bs)
    && decide (timespecNsSigned bs < CLOCK_NS_ENVELOPE)

/-- LPS `Sys/Kernel/Time/PosixTimers.v:291` `clockid_percall_b`: the ids answered per call
(`REALTIME`, `MONOTONIC_RAW`, `REALTIME_COARSE`, `MONOTONIC_COARSE`, `BOOTTIME`). -/
def clockidPercallB (clkid : Word) : Bool :=
  uns clkid == CLOCK_REALTIME || uns clkid == CLOCK_MONOTONIC_RAW
    || uns clkid == CLOCK_REALTIME_COARSE || uns clkid == CLOCK_MONOTONIC_COARSE
    || uns clkid == CLOCK_BOOTTIME

/-- LPS `Sys/Kernel/Time/PosixTimers.v:546` `clock_gettime_spec`. -/
def clockGettimeSpec (clkid tp : Word) : Sys SyscallEffect :=
  if clockidPercallB clkid then do
    let i ← input
    match readBytesMap i.wmem tp 16 with
    | none => unmodeled
    | some _ => do
      let bs ← Sys.choose fun bs : List Byte => realtimeOkB bs = true
      Sys.pure (mkEffect 0 [(tp, bs)] [])
  else if uns clkid == CLOCK_PROCESS_CPUTIME_ID then do
    let i ← input
    match readBytesMap i.wmem tp 16 with
    | none => unmodeled
    | some _ => do
      let bs ← Sys.choose fun bs : List Byte => cputimeOkB bs = true
      Sys.pure (mkEffect 0 [(tp, bs)] [])
  else if !(uns clkid == CLOCK_MONOTONIC) then unmodeled
  else do
    let m ← getModel
    if !decide (uns m.clock < CLOCK_NS_ENVELOPE) then unmodeled
    else do
      let i ← input
      match readBytesMap i.wmem tp 16 with
      | none => unmodeled
      | some _ => do
        let bs ← Sys.choose fun bs : List Byte => timespecOkB bs m.clock = true
        setClock (zw (timespecNs bs))
        Sys.pure (mkEffect 0 [(tp, bs)] [])

end Silmaril.Process.LPS
