module

public import Silmaril.Process.LPS.Sys.FdEvents.Common

/-!
# LPS in Lean: `pselect6` and `ppoll` (and x86-64 `select` and `poll`)

Translation of LPS `Sys/Fs/Select.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/select.c`. Nothing here is nondeterministic: each call has at most one answer, or the model
declines (`unmodeled`).

* **Readiness** is a kernel constant for regular files and directories: they have no
  `->poll`, so `vfs_poll` returns `DEFAULT_POLLMASK` (readable, writable, never exceptional).
  A descriptor whose readiness depends on a peer (a channel, a socket, a pipe end) is declined,
  as are `/dev/null` and `/dev/urandom` (derivable, not yet written in LPS).
* **`pselect6`**: the argpack, then the timeout, then the signal mask, then
  `core_sys_select` (`n < 0` is `EINVAL`, `n > 64` declined, an unreadable set `EFAULT`, a
  closed descriptor `EBADF` for the whole call), then `poll_select_finish`.
* **`ppoll`**: the timeout, then the mask (`set_user_sigmask`: NULL, size, copy), then
  `do_sys_poll` (`nfds > RLIMIT_NOFILE` is `EINVAL`, `nfds > 30` declined, an unreadable array
  `EFAULT`; a closed descriptor is `POLLNVAL` and counted, a negative one is 0 and not
  counted), then `poll_select_finish`.
* **Blocking**: a call that would never return (no timeout and nothing ready) is
  `unmodeled`, not an invented 0. A real deadline with nothing ready returns 0 and writes the
  16-byte zero remaining time; a real deadline with a positive count (or an error) would write
  a live clock reading and is declined. A signal mask that would be installed is declined.
* A write-back range that is not writable end to end is declined (`copy_to_user` lands a
  prefix).

## x86-64

`fd_set`, `struct pollfd`, `struct __kernel_timespec`, `sigset_t` and the `POLL*` bits
(`asm/poll.h` is the generic header) are the same on x86-64, and neither `core_sys_select` nor
`do_sys_poll` consults `access_ok` in LPS's model, so the x86-64 `pselect6` (270) and `ppoll`
(271) are LPS's specifications.

x86-64 also has the legacy `select` (23) and `poll` (7), which riscv64 lacks. They share the
cores and differ only around them:

* `select` (`kern_select`): the timeout is a `struct __kernel_old_timeval`; the kernel folds
  `tv_usec` into `tv_sec + tv_usec / USEC_PER_SEC` and `(tv_usec % USEC_PER_SEC) * 1000`
  (C truncating division, 64-bit wrapping addition) and judges the result with
  `timespec64_valid`, so a `tv_usec` whose truncated remainder modulo `10^6` is negative is
  `EINVAL`, while a multiple of `10^6` (of either sign) only moves `tv_sec` (`{5, -10^6}` is a
  four-second deadline, `{1, -10^6}` is a zero timeout) and `tv_usec = 10^6` is one second;
  there is no signal mask; `poll_select_finish` runs with `PT_TIMEVAL`, which writes 16 zero
  bytes on expiry as `PT_TIMESPEC` does. See `selectSpecX86`.
* `poll`: the timeout is `int timeout_msecs` (negative is no timeout, 0 is poll once, positive
  a deadline); there is no signal mask and **no** `poll_select_finish`, so no remaining time is
  written back and a positive count under a real deadline is an answer. See `pollSpecX86`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys FdEvents

/-! ## `pselect6` -/

/-- LPS `Sys/Fs/Select.v:203` `pselect_nfds_max`: `NR_OPEN_DEFAULT`, one `long` of bitmap. -/
def pselectNfdsMax : Int := NR_OPEN_DEFAULT

/-- LPS `Sys/Fs/Select.v:209` `pselect_touches_sets`: `n = 0` reads and writes no set. -/
def pselectTouchesSets (n : Int) : Bool := !(n == 0)

/-- LPS `Sys/Fs/Select.v:216` `read_fd_set`: the set as `get_fd_set` imports it, zero for a
NULL pointer or `n = 0`; `none` is `EFAULT`. -/
def readFdSet (mp : Word → Option Byte) (p : Word) (n : Int) : Option Word :=
  if !pselectTouchesSets n then some 0
  else if wIs0 p then some 0
  else readU64 mp p

/-- LPS `Sys/Fs/Select.v:229` `fd_set_scanned`: the bits below `n`. -/
def fdSetScanned (v : Word) (n : Int) : Word := v &&& zw (zOnes n)

/-- LPS `Sys/Fs/Select.v:234` `fd_set_writeback`. -/
def fdSetWriteback (p : Word) (n : Int) (v : Word) : List (Word × List Byte) :=
  if !pselectTouchesSets n then []
  else if wIs0 p then []
  else [(p, wordLe8 v)]

/-- LPS `Sys/Fs/Select.v:244` `popcount_aux` (`z` is non-negative at every use, so
`Z.testbit` is `Nat.testBit` of `z.toNat`). -/
def popcountAux (z : Int) : Nat → Int
  | 0 => 0
  | k + 1 => (if z.toNat.testBit k then 1 else 0) + popcountAux z k

/-- LPS `Sys/Fs/Select.v:250` `popcount64`. -/
def popcount64 (v : Word) : Int := popcountAux (uns v) 64

/-- LPS `Sys/Fs/Select.v:257` `bits_all_open`: every descriptor named by a set bit below `k`
is open (`max_select_fd`'s `EBADF` test). Kind-blind, as in LPS. -/
def bitsAllOpen (fds : List (Word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k + 1 =>
    (if z.toNat.testBit k then
      match fdLookup fds (natToWord k) with
      | some _ => true
      | none => false
     else true) && bitsAllOpen fds z k

/-- LPS `Sys/Fs/Select.v:346` `bits_all_pollable`: every descriptor named by a set bit below
`k` has the constant `DEFAULT_POLLMASK` (no `->poll`). Enumerated with no wildcard, as in
LPS. -/
def bitsAllPollable (fds : List (Word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k + 1 =>
    (if z.toNat.testBit k then
      match fdLookup fds (natToWord k) with
      | some (.file _ _) | some (.fileW _ _) | some .dir => true
      | some (.fileRW _ _) => true
      | some (.fileA _ _) => true
      | some (.channel _) | some (.socket _) | none => false
      | some (.pipe _ _) => false
      | some (.devNull _ _) => false
      | some .urandom => false
     else true) && bitsAllPollable fds z k

/-- LPS `Sys/Fs/Select.v:426` `range_writable`. -/
def rangeWritable (i : SyscallInput) (a : Word) (len : Int) : Bool :=
  match readBytesMap i.wmem a (zw len) with
  | some _ => true
  | none => false

/-- LPS `Sys/Fs/Select.v:432` `writes_all_writable`. -/
def writesAllWritable (i : SyscallInput) (ws : List (Word × List Byte)) : Bool :=
  ws.all fun w => rangeWritable i w.1 w.2.length

/-- LPS `Sys/Fs/Select.v:445` `PselectSig`: the sixth argument of `pselect6`. -/
inductive PselectSig where
  /-- The argpack is unreadable: `EFAULT`. -/
  | sigFault
  /-- No mask: the argpack pointer is NULL, or its first word is. -/
  | sigNone
  /-- A mask with the wrong `sigsetsize`: `EINVAL`. -/
  | sigBadSize
  /-- A mask that would be installed: `unmodeled`. -/
  | sigReal
  deriving DecidableEq, Repr

/-- LPS `Sys/Fs/Select.v:451` `pselect_sigpack`. -/
def pselectSigpack (mp : Word → Option Byte) (sig : Word) : PselectSig :=
  if wIs0 sig then .sigNone
  else match readU64 mp sig, readU64 mp (sig + 8) with
    | some sp, some ss =>
      if wIs0 sp then .sigNone
      else if uns ss == kernelSigsetBytes then .sigReal
      else .sigBadSize
    | _, _ => .sigFault

/-- LPS `Sys/Fs/Select.v:488` `PselectTimeout`. -/
inductive PselectTimeout where
  /-- The timeout is unreadable: `EFAULT`. -/
  | toFault
  /-- `timespec64_valid` rejects it: `EINVAL`. -/
  | toInval
  /-- NULL: no deadline. -/
  | toNone
  /-- Exactly `{0, 0}`: poll once. -/
  | toZero
  /-- A real deadline. -/
  | toDeadline
  deriving DecidableEq, Repr

/-- LPS `Sys/Fs/Select.v:495` `pselect_timeout`: the raw `struct __kernel_timespec`, judged by
`timespec64_valid` (`tv_sec < 0`, or `tv_nsec ≥ NSEC_PER_SEC` as `unsigned long`). -/
def pselectTimeout (mp : Word → Option Byte) (tsp : Word) : PselectTimeout :=
  if wIs0 tsp then .toNone
  else match readU64 mp tsp, readU64 mp (tsp + 8) with
    | some sec, some nsec =>
      if sec.toInt < 0 then .toInval
      else if NSEC_PER_SEC ≤ uns nsec then .toInval
      else if wIs0 sec && wIs0 nsec then .toZero
      else .toDeadline
    | _, _ => .toFault

/-- LPS `Sys/Fs/Select.v:511` `PselectCore`: what the core answers before
`poll_select_finish`. -/
inductive PselectCore where
  /-- The model declines. -/
  | gap
  /-- A deterministic errno. -/
  | err (e : Int)
  /-- A count and the user-memory write-back. -/
  | done (ret : Int) (ws : List (Word × List Byte))
  deriving DecidableEq, Repr

/-- LPS `Sys/Fs/Select.v:529` `pselect_core`: `core_sys_select` within the modeled band. -/
def pselectCore (i : SyscallInput) (m : Model) (n32 inp outp exp : Word) : PselectCore :=
  let n := nfdsSigned n32
  if n < 0 then .err EINVAL
  else if pselectNfdsMax < n then .gap
  else
    match readFdSet i.mem inp n, readFdSet i.mem outp n, readFdSet i.mem exp n with
    | some rin, some rout, some rex =>
      let win := fdSetScanned rin n
      let wout := fdSetScanned rout n
      let wex := fdSetScanned rex n
      let all := zlor (zlor (uns win) (uns wout)) (uns wex)
      let k := n.toNat
      if !bitsAllOpen m.fds all k then .err EBADF
      else if !bitsAllPollable m.fds all k then .gap
      else
        .done (popcount64 win + popcount64 wout)
          (fdSetWriteback inp n win ++ fdSetWriteback outp n wout ++ fdSetWriteback exp n 0)
    | _, _, _ => .err EFAULT

/-- LPS `Sys/Fs/Select.v:562` `pselect_err`: no user memory is written on an error path. -/
def pselectErr (e : Int) : Option (Word × List (Word × List Byte)) := some (errnoRet e, [])

/-- LPS `Sys/Fs/Select.v:567` `pselect_timespec_zero`: sixteen zero bytes. -/
def pselectTimespecZero : List Byte := List.replicate 16 0

/-- LPS `Sys/Fs/Select.v:569` `pselect_writes`: the answer, if every write-back range is
writable. -/
def pselectWrites (i : SyscallInput) (ret : Int) (ws : List (Word × List Byte)) :
    Option (Word × List (Word × List Byte)) :=
  if writesAllWritable i ws then some (zw ret, ws) else none

/-- LPS `Sys/Fs/Select.v:634` `pselect_finish`: `poll_select_finish`, shared by `pselect6`
and `ppoll` (and x86-64 `select`). The remaining time it writes is a live clock reading except
when there is no deadline, the deadline is `{0, 0}`, or the deadline ran out (16 zero bytes);
the other cases are declined. -/
def pselectFinish (i : SyscallInput) (tsp : Word) (tmo : PselectTimeout) (c : PselectCore) :
    Option (Word × List (Word × List Byte)) :=
  match c with
  | .gap => none
  | .err e =>
    match tmo with
    | .toDeadline => none
    | _ => pselectErr e
  | .done ret ws =>
    match tmo with
    | .toNone => if ret == 0 then none else pselectWrites i ret ws
    | .toZero => pselectWrites i ret ws
    | .toDeadline =>
      if ret == 0 then pselectWrites i 0 (ws ++ [(tsp, pselectTimespecZero)]) else none
    | _ => none

/-- LPS `Sys/Fs/Select.v:671` `pselect6_outcome`: the one answer, or `none` (declined). -/
def pselect6Outcome (i : SyscallInput) (m : Model) (n32 inp outp exp tsp sig : Word) :
    Option (Word × List (Word × List Byte)) :=
  let core := pselectCore i m n32 inp outp exp
  match pselectSigpack i.mem sig, pselectTimeout i.mem tsp with
  | .sigFault, _ => pselectErr EFAULT
  | _, .toFault => pselectErr EFAULT
  | _, .toInval => pselectErr EINVAL
  | .sigBadSize, _ => pselectErr EINVAL
  | .sigReal, _ => none
  | .sigNone, .toNone => pselectFinish i tsp .toNone core
  | .sigNone, .toZero => pselectFinish i tsp .toZero core
  | .sigNone, .toDeadline => pselectFinish i tsp .toDeadline core

/-- LPS `Sys/Fs/Select.v:690` `pselect6_spec`. `n32` arrives narrowed (`nfds32`). -/
def pselect6Spec (n32 inp outp exp tsp sig : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match pselect6Outcome i m n32 inp outp exp tsp sig with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

/-! ## `ppoll` -/

/-- LPS `Sys/Fs/Select.v:792` `pollfd_bytes`: `struct pollfd` is 8 bytes. -/
def pollfdBytes : Int := 8
/-- LPS `Sys/Fs/Select.v:794` `pollfd_revents_off`. -/
def pollfdReventsOff : Int := 6
/-- LPS `Sys/Fs/Select.v:817` `ppoll_nfds_max`: `N_STACK_PPS = (256 - 16) / 8`. -/
def ppollNfdsMax : Int := 30
/-- LPS `Sys/Fs/Select.v:823` `POLLNVAL`. -/
def POLLNVAL : Int := 32
/-- LPS `Sys/Fs/Select.v:827` `default_pollmask`: `EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM`. -/
def defaultPollmask : Int := 325

/-- LPS `Sys/Fs/Select.v:831` `pollfd_fd`: the entry's `int fd`, signed. -/
def pollfdFd (bs : List Byte) : Int := sint32 (leBytesToWord (bs.take 4))

/-- LPS `Sys/Fs/Select.v:837` `pollfd_events`: the entry's `short events`, unsigned. -/
def pollfdEvents (bs : List Byte) : Int := uns (leBytesToWord ((bs.drop 4).take 2))

/-- LPS `Sys/Fs/Select.v:844` `decode_pollfds`. -/
def decodePollfds (bs : List Byte) : Nat → List (Int × Int)
  | 0 => []
  | k + 1 => (pollfdFd bs, pollfdEvents bs) :: decodePollfds (bs.drop pollfdBytes.toNat) k

/-- LPS `Sys/Fs/Select.v:858` `ppoll_revents_of`: `do_pollfd` for one entry. Enumerated with
no wildcard, as in LPS. -/
def ppollReventsOf (fds : List (Word × FdEntry)) (fd events : Int) : Option Int :=
  if fd < 0 then some 0
  else match fdLookup fds (zw fd) with
    | none => some POLLNVAL
    | some (.file _ _) | some (.fileW _ _) | some .dir => some (zland defaultPollmask events)
    | some (.fileRW _ _) => some (zland defaultPollmask events)
    | some (.fileA _ _) => some (zland defaultPollmask events)
    | some (.channel _) | some (.socket _) | some (.pipe _ _) => none
    | some (.devNull _ _) => none
    | some .urandom => none

/-- LPS `Sys/Fs/Select.v:898` `ppoll_revents`. -/
def ppollRevents (fds : List (Word × FdEntry)) : List (Int × Int) → Option (List Int)
  | [] => some []
  | (fd, ev) :: rest =>
    match ppollReventsOf fds fd ev with
    | none => none
    | some r =>
      match ppollRevents fds rest with
      | none => none
      | some rs => some (r :: rs)

/-- LPS `Sys/Fs/Select.v:921` `ppoll_count`: the number of entries with non-zero `revents`. -/
def ppollCount : List Int → Int
  | [] => 0
  | r :: rest => (if r == 0 then 0 else 1) + ppollCount rest

/-- LPS `Sys/Fs/Select.v:931` `ppoll_writeback`: two bytes at offset 6 of each entry. -/
def ppollWriteback (p : Word) : List Int → List (Word × List Byte)
  | [] => []
  | r :: rest =>
    (p + zw pollfdReventsOff, wordLe2 (zw r)) :: ppollWriteback (p + zw pollfdBytes) rest

/-- LPS `Sys/Fs/Select.v:955` `ppoll_core`: `do_sys_poll` within the modeled band. -/
def ppollCore (i : SyscallInput) (m : Model) (ufds nfds : Word) : PselectCore :=
  let n := uns nfds
  if uns m.nofile < n then .err EINVAL
  else if ppollNfdsMax < n then .gap
  else
    match readBytesMap i.mem ufds (zw (pollfdBytes * n)) with
    | none => .err EFAULT
    | some bs =>
      match ppollRevents m.fds (decodePollfds bs n.toNat) with
      | none => .gap
      | some rs => .done (ppollCount rs) (ppollWriteback ufds rs)

/-- LPS `Sys/Fs/Select.v:983` `PpollSig`: `set_user_sigmask` with separate arguments. -/
inductive PpollSig where
  /-- No mask: the pointer is NULL. -/
  | ppNone
  /-- The wrong `sigsetsize`: `EINVAL`. -/
  | ppBadSize
  /-- The mask is unreadable: `EFAULT`. -/
  | ppFault
  /-- A mask that would be installed: `unmodeled`. -/
  | ppReal
  deriving DecidableEq, Repr

/-- LPS `Sys/Fs/Select.v:989` `ppoll_sigmask`. -/
def ppollSigmask (mp : Word → Option Byte) (sig sigsetsize : Word) : PpollSig :=
  if wIs0 sig then .ppNone
  else if !(uns sigsetsize == kernelSigsetBytes) then .ppBadSize
  else match readBytesMap mp sig (zw kernelSigsetBytes) with
    | some _ => .ppReal
    | none => .ppFault

/-- LPS `Sys/Fs/Select.v:1009` `ppoll_outcome`. -/
def ppollOutcome (i : SyscallInput) (m : Model) (ufds nfds tsp sig sigsetsize : Word) :
    Option (Word × List (Word × List Byte)) :=
  match pselectTimeout i.mem tsp with
  | .toFault => pselectErr EFAULT
  | .toInval => pselectErr EINVAL
  | tmo =>
    match ppollSigmask i.mem sig sigsetsize with
    | .ppBadSize => pselectErr EINVAL
    | .ppFault => pselectErr EFAULT
    | .ppReal => none
    | .ppNone => pselectFinish i tsp tmo (ppollCore i m ufds nfds)

/-- LPS `Sys/Fs/Select.v:1028` `ppoll_spec`. `nfds` arrives narrowed (`unfds32`). -/
def ppollSpec (ufds nfds tsp sig sigsetsize : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match ppollOutcome i m ufds nfds tsp sig sigsetsize with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

/-! ## x86-64 `select` (23) -/

/-- `USEC_PER_SEC`. -/
def USEC_PER_SEC : Int := 1000000
/-- `NSEC_PER_USEC`. -/
def NSEC_PER_USEC : Int := 1000

/-- x86-64 `kern_select`'s timeout (`fs/select.c`): the `struct __kernel_old_timeval` at
`tvp` (16 bytes, `long tv_sec, tv_usec`), passed to `poll_select_set_timeout` as
`tv_sec + tv_usec / USEC_PER_SEC` (64-bit wrapping: the kernel builds with
`-fno-strict-overflow`) and `(tv_usec % USEC_PER_SEC) * NSEC_PER_USEC` (C truncating
division), then judged by `timespec64_valid`. Read as LPS's `pselect_timeout` reads its
`timespec`. -/
def selectTimeoutX86 (mp : Word → Option Byte) (tvp : Word) : PselectTimeout :=
  if wIs0 tvp then .toNone
  else match readU64 mp tvp, readU64 mp (tvp + 8) with
    | some sec, some usec =>
      let s := (zw (sec.toInt + usec.toInt.tdiv USEC_PER_SEC)).toInt
      let ns := usec.toInt.tmod USEC_PER_SEC * NSEC_PER_USEC
      if s < 0 then .toInval
      else if NSEC_PER_SEC ≤ uns (zw ns) then .toInval
      else if s == 0 && ns == 0 then .toZero
      else .toDeadline
    | _, _ => .toFault

/-- x86-64 `select` (`kern_select`): the timeout, then `core_sys_select` (LPS
`pselect_core`), then `poll_select_finish(…, PT_TIMEVAL, …)` (LPS `pselect_finish`: an
expired `timeval` is 16 zero bytes too). No signal mask. -/
def selectOutcomeX86 (i : SyscallInput) (m : Model) (n32 inp outp exp tvp : Word) :
    Option (Word × List (Word × List Byte)) :=
  match selectTimeoutX86 i.mem tvp with
  | .toFault => pselectErr EFAULT
  | .toInval => pselectErr EINVAL
  | tmo => pselectFinish i tvp tmo (pselectCore i m n32 inp outp exp)

/-- x86-64 `select` (number 23, no riscv64 counterpart). `n32` arrives narrowed. -/
def selectSpecX86 (n32 inp outp exp tvp : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match selectOutcomeX86 i m n32 inp outp exp tvp with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

/-! ## x86-64 `poll` (7) -/

/-- x86-64 `poll`'s timeout: `int timeout_msecs`; negative is no timeout, zero is poll once,
positive a deadline (`poll_select_set_timeout` accepts every non-negative value). -/
def pollTimeoutX86 (msecs32 : Word) : PselectTimeout :=
  let t := sint32 msecs32
  if t < 0 then .toNone else if t == 0 then .toZero else .toDeadline

/-- x86-64 `poll` (`SYSCALL_DEFINE3(poll, …)`): `do_sys_poll` (LPS `ppoll_core`) and its
answer, with no `poll_select_finish` and so no remaining-time write-back. Only a zero count
with no timeout (the call never returns) is declined beyond the core's own declines. -/
def pollOutcomeX86 (i : SyscallInput) (m : Model) (ufds nfds msecs32 : Word) :
    Option (Word × List (Word × List Byte)) :=
  match ppollCore i m ufds nfds with
  | .gap => none
  | .err e => pselectErr e
  | .done ret ws =>
    match pollTimeoutX86 msecs32 with
    | .toNone => if ret == 0 then none else pselectWrites i ret ws
    | _ => pselectWrites i ret ws

/-- x86-64 `poll` (number 7, no riscv64 counterpart). `nfds` and `timeout_msecs` arrive
narrowed (`unfds32`, `int32`). -/
def pollSpecX86 (ufds nfds msecs32 : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match pollOutcomeX86 i m ufds nfds msecs32 with
  | none => unmodeled
  | some (r, ws) => Sys.pure (mkEffect r ws [])

end Silmaril.Process.LPS
