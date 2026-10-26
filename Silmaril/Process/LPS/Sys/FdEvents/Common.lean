module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.MonadExt
public import Silmaril.Process.LPS.Sys.FsIo.File

/-!
# LPS in Lean: helpers shared by the descriptor-event family

The descriptor-event family is `pipe2`, `eventfd2`, `epoll_create1`, `epoll_ctl`,
`epoll_pwait`, `timerfd_create`, `pselect6` and `ppoll` (LPS `Sys/Fs/Pipe.v`,
`Sys/Fs/EventFd.v`, `Sys/Fs/EventPoll.v`, `Sys/Fs/Timerfd.v`, `Sys/Fs/Select.v`, upstream
commit `f1006fe8`). This module holds the few helpers of other LPS files that these
specifications need and that are not translated elsewhere (`word_le2`, `Z.ones`), in the
namespace `Silmaril.Process.LPS.FdEvents`. The other shared helpers are the common ones:
`lowest_fd` and `Z.ldiff` are `lowestFd` and `zldiff` of `Sys/FsIo/File`, `set_fds` and
`set_pipes` are `Sys.setFds` and `Sys.setPipes` of `MonadExt`.

## The ABI parameter

The family's specifications depend on the architecture through three facts only, collected in
`FdEventsAbi`:

* `access_ok`: LPS's `access_okb` (the generic `__access_ok` against Sv48 `TASK_SIZE = 2^47`)
  on riscv64, `accessOkbX86` (`TASK_SIZE_MAX = 2^47 - 4096`) on x86-64;
* `sizeof(struct epoll_event)`: 16 on riscv64 (LPS `Sys/Fs/EventPoll.v:203`), 12 on x86-64,
  where `EPOLL_PACKED` is `__attribute__((packed))` (`include/uapi/linux/eventpoll.h`);
* `EP_MAX_EVENTS = INT_MAX / sizeof(struct epoll_event)`: 134217727 against 178956970.

and one fact of the kernel version rather than of the architecture: `epollFdFirst`, the order
of `do_epoll_wait`'s checks, which changed in v6.15.

* Up to v6.14 (`fs/eventpoll.c:2541-2559` in v6.8): the `maxevents` bounds (`-EINVAL`), then
  `access_ok` on the `events` range (`-EFAULT`), then `fdget(epfd)` (`-EBADF`), then
  `is_file_epoll` (`-EINVAL`).
* From v6.15 (commit `6b47d35d4d9e`, "eventpoll: abstract out parameter sanity checking",
  which moved the checks into `ep_check_params`, called after the descriptor lookup):
  `fdget(epfd)` (`-EBADF`) first, then `ep_check_params`: the `maxevents` bounds, `access_ok`,
  `is_file_epoll`. This is LPS's order (`Sys/Fs/EventPoll.v:575-616`; LPS targets v6.18).

`FdEventsAbi.lps` keeps LPS's order (it is a translation). `FdEventsAbi.x86` has the v6.14
order and `FdEventsAbi.x86FdFirst` the v6.15 one. The hub's x86-64 profile (v6.13 to v6.18)
spans both, so the native table declines the inputs where the two disagree
(`NativeX86.All.epollOrderChaos`).

`FdEventsAbi.lps` is LPS's instance; each `…With FdEventsAbi.lps` specification is the
literal translation of its LPS definition.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- The architecture-dependent facts of the descriptor-event family. -/
structure FdEventsAbi where
  /-- `access_ok(base, len)`. -/
  accessOk : Word → Int → Bool
  /-- `sizeof(struct epoll_event)`. -/
  epollEventBytes : Int
  /-- `EP_MAX_EVENTS`. -/
  epMaxEvents : Int
  /-- `do_epoll_wait` looks `epfd` up before checking `maxevents` and `access_ok` (LPS's
  order, Linux from v6.15); `false` is the order up to v6.14 (`fs/eventpoll.c:2541-2552` in
  v6.8). -/
  epollFdFirst : Bool

/-- LPS's ABI (riscv64): `access_okb` (LPS `State.v:1344`) and a 16-byte
`struct epoll_event` (LPS `Sys/Fs/EventPoll.v:203`, `:208`). -/
def FdEventsAbi.lps : FdEventsAbi :=
  ⟨accessOkb, Silmaril.Process.LPS.epollEventBytes, EP_MAX_EVENTS, true⟩

/-- The x86-64 ABI: x86-64 `access_ok` (`arch/x86/include/asm/uaccess_64.h`) and the packed
12-byte `struct epoll_event`, with the `do_epoll_wait` order of
Linux up to v6.14 (`maxevents`, `access_ok`, then `epfd`). -/
def FdEventsAbi.x86 : FdEventsAbi :=
  ⟨accessOkbX86, Silmaril.Process.LPS.epollEventBytesX86, EP_MAX_EVENTS_X86, false⟩

/-- The x86-64 ABI with the `do_epoll_wait` order of Linux from v6.15 (`epfd` first, commit
`6b47d35d4d9e`). -/
def FdEventsAbi.x86FdFirst : FdEventsAbi :=
  ⟨accessOkbX86, Silmaril.Process.LPS.epollEventBytesX86, EP_MAX_EVENTS_X86, true⟩

namespace FdEvents

/-- Coq `Z.ones n` (`Z.pred (2 ^ n)`; `2 ^ n` is `0` for negative `n`). -/
def zOnes (n : Int) : Int := if n < 0 then -1 else 2 ^ n.toNat - 1

/-- LPS `BvBase.v:155` `word_le2`: the two low little-endian bytes of a word. -/
def wordLe2 (v : Word) : List Byte := [v.extractLsb' 0 8, v.extractLsb' 8 8]

end FdEvents

end Silmaril.Process.LPS
