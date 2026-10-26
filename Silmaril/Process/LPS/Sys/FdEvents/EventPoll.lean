module

public import Silmaril.Process.LPS.Sys.FdEvents.Select
public import Silmaril.Process.LPS.MonadIff

/-!
# LPS in Lean: `epoll_create1`, `epoll_ctl`, `epoll_pwait` (and x86-64 `epoll_create`,
`epoll_wait`)

Translation of LPS `Sys/Fs/EventPoll.v` (upstream commit `f1006fe8`), the specification of
Linux `fs/eventpoll.c`.

No `FdEntry` is an epoll instance, so `is_file_epoll` is false for every descriptor the model
can hold: `epoll_ctl` and `epoll_pwait` reach their `EINVAL` on every input that gets that far,
and the interest-set machinery is unreachable. `epoll_create1`'s success (the epoll
descriptor) is declined.

* `epoll_create1(flags)`: `flags & ~EPOLL_CLOEXEC` (32-bit) is `EINVAL`, otherwise declined.
* `epoll_ctl(epfd, op, fd, event)`: the event copy (skipped for `EPOLL_CTL_DEL`) is first, so
  its `EFAULT` beats `EBADF`; then `EBADF` for `epfd`, `EBADF` for `fd`, `EPERM` for a target
  without `->poll` (before the epoll-ness of `epfd` is tested), else `EINVAL`. A channel target
  is declined (`fd_can_poll` cannot tell whether its far end polls).
* `epoll_pwait(epfd, events, maxevents, timeout, sigmask, sigsetsize)`: `set_user_sigmask`
  first (NULL, size, copy; an installed mask is declined), then `EBADF`, then
  `maxevents ∉ (0, EP_MAX_EVENTS]` is `EINVAL`, then `access_ok(events, maxevents *
  sizeof(struct epoll_event))` is `EFAULT`, else `EINVAL`. Nothing is written. That is LPS's
  order, and Linux's from v6.15; up to v6.14 Linux checks `epfd` after `maxevents` and
  `access_ok` (`fs/eventpoll.c:2541-2552` in v6.8; `FdEventsAbi.epollFdFirst`).

## x86-64

`struct epoll_event` is `__attribute__((packed))` on x86-64 (`EPOLL_PACKED`,
`include/uapi/linux/eventpoll.h`): 12 bytes, so `epoll_ctl` copies 12 bytes (an `event` with
12 readable bytes is accepted on x86-64 and is `EFAULT` on riscv64), and
`EP_MAX_EVENTS = INT_MAX / 12 = 178956970` with the `events` range `maxevents * 12`. `access_ok`
is x86-64's. Every specification is parametric in `FdEventsAbi`; the `…X86` ones use
`FdEventsAbi.x86`, whose `do_epoll_wait` order is Linux's up to v6.14, and the `…X86FdFirst`
ones `FdEventsAbi.x86FdFirst`, Linux's order from v6.15 (commit `6b47d35d4d9e`). The two
disagree exactly on an unopened `epfd` with a bad `maxevents` or a bad `events` range
(`epollWaitOrders_agree`, `epollWaitOrders_disagree`); `epollWaitOrdersDiffer` and
`epollPwaitOrdersDiffer` decide
it, and the native table declines those inputs (`NativeX86.All.epollOrderChaos`).

x86-64 also has the legacy `epoll_create` (213) and `epoll_wait` (232):

* `SYSCALL_DEFINE1(epoll_create, int, size)`: `size <= 0` is `EINVAL`, otherwise
  `do_epoll_create(0)`, whose success is declined;
* `SYSCALL_DEFINE4(epoll_wait, …)` is `do_epoll_wait(epfd, events, maxevents, …)`, which is
  `epoll_pwait` with no signal mask (LPS's `EpSigNone` arm).
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys FdEvents

/-- LPS `Sys/Fs/EventPoll.v:185` `EPOLL_CLOEXEC`. -/
def EPOLL_CLOEXEC : Int := O_CLOEXEC

/-- LPS `Sys/Fs/EventPoll.v:192` `EPOLL_CTL_DEL`. -/
def EPOLL_CTL_DEL : Int := 2

/-- LPS `Sys/Fs/EventPoll.v:282` `fd_can_poll`: does the file have a `->poll`? `none` where
the model cannot say (a channel), or where LPS has not written the exact answer yet
(`/dev/null`, `/dev/urandom`). Enumerated with no wildcard, as in LPS. -/
def fdCanPoll : FdEntry → Option Bool
  | .file _ _ | .fileW _ _ | .fileA _ _ | .fileRW _ _ | .dir => some false
  | .socket _ | .pipe _ _ => some true
  | .channel _ => none
  | .devNull _ _ => none
  | .urandom => none

/-- LPS `Sys/Fs/EventPoll.v:362` `epoll_create1_outcome`: `flags & ~EPOLL_CLOEXEC` over 32
bits (`Z.lnot EPOLL_CLOEXEC mod 2^32`). -/
def epollCreate1Outcome (flags32 : Word) : Option Word :=
  if zland (uns flags32) ((-EPOLL_CLOEXEC - 1) % 2 ^ 32) == 0 then none
  else some (errnoRet EINVAL)

/-- LPS `Sys/Fs/EventPoll.v:367` `epoll_create1_spec`. `flags32` arrives narrowed. -/
def epollCreate1Spec (flags32 : Word) : Sys SyscallEffect :=
  match epollCreate1Outcome flags32 with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])

/-- x86-64 `epoll_create` (number 213, no riscv64 counterpart): `size <= 0` (an `int`) is
`EINVAL`; otherwise `do_epoll_create(0)`, LPS's `epoll_create1_spec 0`, declined. -/
def epollCreateSpecX86 (size32 : Word) : Sys SyscallEffect :=
  if sint32 size32 ≤ 0 then errRet EINVAL else epollCreate1Spec 0

/-- LPS `Sys/Fs/EventPoll.v:400` `copy_from_user_ok`, parametric in `access_ok`: the range
check, then every byte mapped. -/
def copyFromUserOkWith (abi : FdEventsAbi) (mp : Word → Option Byte) (a : Word) (len : Int) :
    Bool :=
  abi.accessOk a len &&
    match readBytesMap mp a (zw len) with
    | some _ => true
    | none => false

/-- LPS `Sys/Fs/EventPoll.v:400` `copy_from_user_ok`. -/
def copyFromUserOk (mp : Word → Option Byte) (a : Word) (len : Int) : Bool :=
  copyFromUserOkWith .lps mp a len

/-- LPS `Sys/Fs/EventPoll.v:421` `ep_op_has_event`: `op != EPOLL_CTL_DEL`. -/
def epOpHasEvent (op32 : Word) : Bool := !(uns op32 == EPOLL_CTL_DEL)

/-- LPS `Sys/Fs/EventPoll.v:502` `epoll_ctl_outcome`, parametric in the ABI (`access_ok` and
`sizeof(struct epoll_event)`). -/
def epollCtlOutcomeWith (abi : FdEventsAbi) (i : SyscallInput) (m : Model)
    (epfd op32 tfd event : Word) : Option Word :=
  let afterCopy :=
    match fdLookup m.fds epfd with
    | none => some (errnoRet EBADF)
    | some _ =>
      match fdLookup m.fds tfd with
      | none => some (errnoRet EBADF)
      | some te =>
        match fdCanPoll te with
        | some false => some (errnoRet EPERM)
        | some true => some (errnoRet EINVAL)
        | none => none
  if epOpHasEvent op32 then
    if copyFromUserOkWith abi i.mem event abi.epollEventBytes then afterCopy
    else some (errnoRet EFAULT)
  else afterCopy

/-- LPS `Sys/Fs/EventPoll.v:524` `epoll_ctl_spec`, parametric in the ABI. -/
def epollCtlSpecWith (abi : FdEventsAbi) (epfd op32 tfd event : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match epollCtlOutcomeWith abi i m epfd op32 tfd event with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])

/-- LPS `Sys/Fs/EventPoll.v:524` `epoll_ctl_spec` (16-byte `struct epoll_event`). -/
def epollCtlSpec (epfd op32 tfd event : Word) : Sys SyscallEffect :=
  epollCtlSpecWith .lps epfd op32 tfd event

/-- x86-64 `epoll_ctl` (number 233): the packed 12-byte `struct epoll_event`. -/
def epollCtlSpecX86 (epfd op32 tfd event : Word) : Sys SyscallEffect :=
  epollCtlSpecWith .x86 epfd op32 tfd event

/-- LPS `Sys/Fs/EventPoll.v:560` `EpollSigmask`. -/
inductive EpollSigmask where
  /-- `umask` is NULL: nothing installed. -/
  | epSigNone
  /-- Wrong `sigsetsize`: `EINVAL`. -/
  | epSigBadSize
  /-- `umask` unreadable: `EFAULT`. -/
  | epSigFault
  /-- A mask that would be installed: `unmodeled`. -/
  | epSigReal
  deriving DecidableEq, Repr

/-- LPS `Sys/Fs/EventPoll.v:566` `epoll_sigmask`, parametric in `access_ok`. `sigsetsize` is
compared full width. -/
def epollSigmaskWith (abi : FdEventsAbi) (mp : Word → Option Byte) (umask sigsetsize : Word) :
    EpollSigmask :=
  if wIs0 umask then .epSigNone
  else if !(uns sigsetsize == kernelSigsetBytes) then .epSigBadSize
  else if copyFromUserOkWith abi mp umask kernelSigsetBytes then .epSigReal
  else .epSigFault

/-- `do_epoll_wait` past the signal mask (LPS `Sys/Fs/EventPoll.v:616`, the `EpSigNone` arm
of `epoll_pwait_outcome`). Under LPS's order (`abi.epollFdFirst`): `EBADF`, the `maxevents`
bounds, `access_ok` on the `events` range, then `EINVAL` (no descriptor is an epoll instance).
Under Linux's (`fs/eventpoll.c:2541-2560`, v6.8): the `maxevents` bounds (`EINVAL`), then
`access_ok` (`EFAULT`), then `fdget(epfd)` (`EBADF`), then `is_file_epoll` (`EINVAL`). The two
differ for an unopened `epfd` with a bad `maxevents` or a bad range. -/
def epollWaitCoreWith (abi : FdEventsAbi) (m : Model) (epfd events maxevents32 : Word) :
    Option Word :=
  let n := sint32 maxevents32
  if abi.epollFdFirst then
    match fdLookup m.fds epfd with
    | none => some (errnoRet EBADF)
    | some _ =>
      if n ≤ 0 then some (errnoRet EINVAL)
      else if abi.epMaxEvents < n then some (errnoRet EINVAL)
      else if abi.accessOk events (n * abi.epollEventBytes) then some (errnoRet EINVAL)
      else some (errnoRet EFAULT)
  else
    if n ≤ 0 then some (errnoRet EINVAL)
    else if abi.epMaxEvents < n then some (errnoRet EINVAL)
    else if !abi.accessOk events (n * abi.epollEventBytes) then some (errnoRet EFAULT)
    else match fdLookup m.fds epfd with
      | none => some (errnoRet EBADF)
      | some _ => some (errnoRet EINVAL)

/-- LPS `Sys/Fs/EventPoll.v:616` `epoll_pwait_outcome`, parametric in the ABI. `timeout` is
not an argument: no modeled answer depends on it. -/
def epollPwaitOutcomeWith (abi : FdEventsAbi) (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : Word) : Option Word :=
  match epollSigmaskWith abi i.mem sigmask sigsetsize with
  | .epSigBadSize => some (errnoRet EINVAL)
  | .epSigFault => some (errnoRet EFAULT)
  | .epSigReal => none
  | .epSigNone => epollWaitCoreWith abi m epfd events maxevents32

/-- LPS `Sys/Fs/EventPoll.v:636` `epoll_pwait_spec`, parametric in the ABI. -/
def epollPwaitSpecWith (abi : FdEventsAbi) (epfd events maxevents32 sigmask sigsetsize : Word) :
    Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match epollPwaitOutcomeWith abi i m epfd events maxevents32 sigmask sigsetsize with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])

/-- LPS `Sys/Fs/EventPoll.v:636` `epoll_pwait_spec`. -/
def epollPwaitSpec (epfd events maxevents32 sigmask sigsetsize : Word) : Sys SyscallEffect :=
  epollPwaitSpecWith .lps epfd events maxevents32 sigmask sigsetsize

/-- x86-64 `epoll_pwait` (number 281): x86-64 `access_ok`, the packed 12-byte
`struct epoll_event` and `EP_MAX_EVENTS = 178956970`. -/
def epollPwaitSpecX86 (epfd events maxevents32 sigmask sigsetsize : Word) : Sys SyscallEffect :=
  epollPwaitSpecWith .x86 epfd events maxevents32 sigmask sigsetsize

/-- `epoll_wait`: `do_epoll_wait` with no signal mask, parametric in the ABI. -/
def epollWaitSpecWith (abi : FdEventsAbi) (epfd events maxevents32 : Word) :
    Sys SyscallEffect := do
  let m ← getModel
  match epollWaitCoreWith abi m epfd events maxevents32 with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])

/-- x86-64 `epoll_wait` (number 232, no riscv64 counterpart): `do_epoll_wait` with no signal
mask, in the order of Linux up to v6.14. -/
def epollWaitSpecX86 (epfd events maxevents32 : Word) : Sys SyscallEffect :=
  epollWaitSpecWith .x86 epfd events maxevents32

/-- x86-64 `epoll_wait` in the order of Linux from v6.15 (`epfd` first). -/
def epollWaitSpecX86FdFirst (epfd events maxevents32 : Word) : Sys SyscallEffect :=
  epollWaitSpecWith .x86FdFirst epfd events maxevents32

/-- x86-64 `epoll_pwait` in the order of Linux from v6.15 (`epfd` first). -/
def epollPwaitSpecX86FdFirst (epfd events maxevents32 sigmask sigsetsize : Word) :
    Sys SyscallEffect :=
  epollPwaitSpecWith .x86FdFirst epfd events maxevents32 sigmask sigsetsize

/-! ### The two x86-64 orders -/

/-- The two `do_epoll_wait` orders (Linux up to v6.14, and from v6.15) give different answers:
an unopened `epfd` (`EBADF` from v6.15) with a `maxevents` out of `(0, EP_MAX_EVENTS]`
(`EINVAL` up to v6.14) or an `events` range `access_ok` refuses (`EFAULT` up to v6.14).
`epollWaitOrders_agree` and `epollWaitOrders_disagree` prove it is exactly that. -/
def epollWaitOrdersDiffer (m : Model) (epfd events maxevents32 : Word) : Bool :=
  (fdLookup m.fds epfd).isNone &&
    (decide (sint32 maxevents32 ≤ 0) || decide (EP_MAX_EVENTS_X86 < sint32 maxevents32) ||
      !accessOkbX86 events (sint32 maxevents32 * epollEventBytesX86))

/-- The two orders give different `epoll_pwait` answers: the mask is NULL (both read it the
same way first) and the `do_epoll_wait` orders differ. -/
def epollPwaitOrdersDiffer (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : Word) : Bool :=
  decide (epollSigmaskWith .x86 i.mem sigmask sigsetsize = .epSigNone) &&
    epollWaitOrdersDiffer m epfd events maxevents32

theorem epollWaitCore_x86_unopened (m : Model) (epfd events maxevents32 : Word)
    (hf : fdLookup m.fds epfd = none) :
    epollWaitCoreWith .x86 m epfd events maxevents32 =
      if sint32 maxevents32 ≤ 0 then some (errnoRet EINVAL)
      else if EP_MAX_EVENTS_X86 < sint32 maxevents32 then some (errnoRet EINVAL)
      else if !accessOkbX86 events (sint32 maxevents32 * epollEventBytesX86) then
        some (errnoRet EFAULT)
      else some (errnoRet EBADF) := by
  simp [epollWaitCoreWith, FdEventsAbi.x86, hf]

theorem epollWaitCore_fdFirst_unopened (m : Model) (epfd events maxevents32 : Word)
    (hf : fdLookup m.fds epfd = none) :
    epollWaitCoreWith .x86FdFirst m epfd events maxevents32 = some (errnoRet EBADF) := by
  simp [epollWaitCoreWith, FdEventsAbi.x86FdFirst, hf]

theorem epollWaitCore_opened (m : Model) (epfd events maxevents32 : Word) (e : FdEntry)
    (hf : fdLookup m.fds epfd = some e) :
    epollWaitCoreWith .x86 m epfd events maxevents32 =
      epollWaitCoreWith .x86FdFirst m epfd events maxevents32 := by
  cases h3 : accessOkbX86 events (sint32 maxevents32 * epollEventBytesX86) <;>
    simp [epollWaitCoreWith, FdEventsAbi.x86, FdEventsAbi.x86FdFirst, hf, h3]

/-- **Where `epollWaitOrdersDiffer` is false the two orders give the same answer.** -/
theorem epollWaitOrders_agree (m : Model) (epfd events maxevents32 : Word)
    (h : epollWaitOrdersDiffer m epfd events maxevents32 = false) :
    epollWaitCoreWith .x86 m epfd events maxevents32 =
      epollWaitCoreWith .x86FdFirst m epfd events maxevents32 := by
  cases hf : fdLookup m.fds epfd with
  | some e => exact epollWaitCore_opened m epfd events maxevents32 e hf
  | none =>
    rw [epollWaitCore_x86_unopened m epfd events maxevents32 hf,
      epollWaitCore_fdFirst_unopened m epfd events maxevents32 hf]
    by_cases h1 : sint32 maxevents32 ≤ 0
    · simp [epollWaitOrdersDiffer, hf, h1] at h
    · by_cases h2 : EP_MAX_EVENTS_X86 < sint32 maxevents32
      · simp [epollWaitOrdersDiffer, hf, h1, h2] at h
      · cases h3 : accessOkbX86 events (sint32 maxevents32 * epollEventBytesX86)
        · simp [epollWaitOrdersDiffer, hf, h1, h2, h3] at h
        · simp [h1, h2]

/-- **Where `epollWaitOrdersDiffer` is true the two orders give different answers.** -/
theorem epollWaitOrders_disagree (m : Model) (epfd events maxevents32 : Word)
    (h : epollWaitOrdersDiffer m epfd events maxevents32 = true) :
    epollWaitCoreWith .x86 m epfd events maxevents32 ≠
      epollWaitCoreWith .x86FdFirst m epfd events maxevents32 := by
  have e1 : errnoRet EINVAL ≠ errnoRet EBADF := by decide
  have e2 : errnoRet EFAULT ≠ errnoRet EBADF := by decide
  cases hf : fdLookup m.fds epfd with
  | some e => simp [epollWaitOrdersDiffer, hf] at h
  | none =>
    rw [epollWaitCore_x86_unopened m epfd events maxevents32 hf,
      epollWaitCore_fdFirst_unopened m epfd events maxevents32 hf]
    by_cases h1 : sint32 maxevents32 ≤ 0
    · simp [h1, e1]
    · by_cases h2 : EP_MAX_EVENTS_X86 < sint32 maxevents32
      · simp [h1, h2, e1]
      · cases h3 : accessOkbX86 events (sint32 maxevents32 * epollEventBytesX86)
        · simp [h1, h2, e2]
        · simp [epollWaitOrdersDiffer, hf, h1, h2, h3] at h

theorem epollSigmask_fdFirst (mp : Word → Option Byte) (sigmask sigsetsize : Word) :
    epollSigmaskWith .x86FdFirst mp sigmask sigsetsize =
      epollSigmaskWith .x86 mp sigmask sigsetsize := rfl

/-- **Where `epollPwaitOrdersDiffer` is false the two orders give the same answer.** -/
theorem epollPwaitOrders_agree (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : Word)
    (h : epollPwaitOrdersDiffer i m epfd events maxevents32 sigmask sigsetsize = false) :
    epollPwaitOutcomeWith .x86 i m epfd events maxevents32 sigmask sigsetsize =
      epollPwaitOutcomeWith .x86FdFirst i m epfd events maxevents32 sigmask sigsetsize := by
  unfold epollPwaitOutcomeWith
  rw [epollSigmask_fdFirst]
  cases hs : epollSigmaskWith .x86 i.mem sigmask sigsetsize with
  | epSigNone =>
    exact epollWaitOrders_agree m epfd events maxevents32
      (by simpa [epollPwaitOrdersDiffer, hs] using h)
  | epSigBadSize => rfl
  | epSigFault => rfl
  | epSigReal => rfl

/-- **Where `epollPwaitOrdersDiffer` is true the two orders give different answers.** -/
theorem epollPwaitOrders_disagree (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : Word)
    (h : epollPwaitOrdersDiffer i m epfd events maxevents32 sigmask sigsetsize = true) :
    epollPwaitOutcomeWith .x86 i m epfd events maxevents32 sigmask sigsetsize ≠
      epollPwaitOutcomeWith .x86FdFirst i m epfd events maxevents32 sigmask sigsetsize := by
  have h' : epollSigmaskWith .x86 i.mem sigmask sigsetsize = .epSigNone ∧
      epollWaitOrdersDiffer m epfd events maxevents32 = true := by
    simpa [epollPwaitOrdersDiffer] using h
  unfold epollPwaitOutcomeWith
  rw [epollSigmask_fdFirst, h'.1]
  exact epollWaitOrders_disagree m epfd events maxevents32 h'.2

/-- Equal answers give the same `epoll_wait` specification. -/
theorem epollWaitSpecWith_congr (abi abi' : FdEventsAbi) (epfd events maxevents32 : Word)
    (i : SyscallInput) (m : Model)
    (h : epollWaitCoreWith abi m epfd events maxevents32 =
      epollWaitCoreWith abi' m epfd events maxevents32) (o : Outcome SyscallEffect) :
    epollWaitSpecWith abi epfd events maxevents32 i m o ↔
      epollWaitSpecWith abi' epfd events maxevents32 i m o := by
  unfold epollWaitSpecWith
  rw [Sys.bind_getModel_iff, Sys.bind_getModel_iff, h]

/-- Equal answers give the same `epoll_pwait` specification. -/
theorem epollPwaitSpecWith_congr (abi abi' : FdEventsAbi)
    (epfd events maxevents32 sigmask sigsetsize : Word) (i : SyscallInput) (m : Model)
    (h : epollPwaitOutcomeWith abi i m epfd events maxevents32 sigmask sigsetsize =
      epollPwaitOutcomeWith abi' i m epfd events maxevents32 sigmask sigsetsize)
    (o : Outcome SyscallEffect) :
    epollPwaitSpecWith abi epfd events maxevents32 sigmask sigsetsize i m o ↔
      epollPwaitSpecWith abi' epfd events maxevents32 sigmask sigsetsize i m o := by
  unfold epollPwaitSpecWith
  rw [Sys.bind_input_iff, Sys.bind_input_iff, Sys.bind_getModel_iff, Sys.bind_getModel_iff, h]

/-- LPS `Sys/Fs/EventPoll.v:325` `fd_can_poll_is_select_pollable`: `fd_can_poll` and
`bits_all_pollable` read the same kernel fact (`->poll` is NULL exactly when `vfs_poll`
returns `DEFAULT_POLLMASK`). -/
theorem fdCanPoll_is_select_pollable (e : FdEntry) :
    bitsAllPollable [(0, e)] 1 1 = true ↔ fdCanPoll e = some false := by
  cases e <;> simp [bitsAllPollable, fdCanPoll, fdLookup, natToWord, zw]

end Silmaril.Process.LPS
