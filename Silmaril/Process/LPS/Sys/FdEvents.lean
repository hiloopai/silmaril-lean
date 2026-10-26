module

public import Silmaril.Process.LPS.Sys.FdEvents.Pipe
public import Silmaril.Process.LPS.Sys.FdEvents.EventFd
public import Silmaril.Process.LPS.Sys.FdEvents.Timerfd
public import Silmaril.Process.LPS.Sys.FdEvents.Select
public import Silmaril.Process.LPS.Sys.FdEvents.EventPoll
public import Silmaril.Process.LPS.Arm

/-!
# LPS in Lean: the descriptor-event family's arms

The arms of `pipe2`, `eventfd2`, `epoll_create1`, `epoll_ctl`, `epoll_pwait`,
`timerfd_create`, `pselect6` and `ppoll`, with the argument narrowings of LPS
`Sys/SyscallTable.v:43-73`:

* `fdEventsLpsArms`: the asm-generic (riscv64) numbers and LPS's specifications;
* `fdEventsX86Arms`: the native x86-64 numbers (`arch/x86/entry/syscalls/syscall_64.tbl`),
  with the x86-64 variant where the ABI differs (`pipe2`, `epoll_ctl`, `epoll_pwait`: x86-64
  `access_ok`; `epoll_ctl`, `epoll_pwait`: the packed 12-byte `struct epoll_event`), and the
  six legacy x86-64 syscalls of the family that riscv64 lacks, each derived from the kernel
  function it forwards to: `poll` (7), `pipe` (22), `select` (23), `epoll_create` (213),
  `epoll_wait` (232), `eventfd` (284).

x86-64's `SYSCALL_DEFINE` wrappers narrow `int`/`unsigned int` arguments with the same
`__SC_CAST` as riscv64's, so the narrowings are the same.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- The family's LPS arms (LPS `Sys/SyscallTable.v:43-46,57,66,67,73`). -/
def fdEventsLpsArms : List SpecArm :=
  [ arm 19 "eventfd2" (fun i => eventfd2Spec (flag32 (i.arg 1))),
    arm 20 "epoll_create1" (fun i => epollCreate1Spec (flag32 (i.arg 0))),
    arm 21 "epoll_ctl"
      (fun i => epollCtlSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (fd32 (i.arg 2)) (i.arg 3)),
    arm 22 "epoll_pwait"
      (fun i => epollPwaitSpec (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4) (i.arg 5)),
    arm 59 "pipe2" (fun i => pipe2Spec (i.arg 0) (pipeFlags32 (i.arg 1))),
    arm 72 "pselect6"
      (fun i => pselect6Spec (nfds32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 73 "ppoll"
      (fun i => ppollSpec (i.arg 0) (unfds32 (i.arg 1)) (i.arg 2) (i.arg 3) (i.arg 4)),
    arm 85 "timerfd_create" (fun i => timerfdCreateSpec (clockid32 (i.arg 0)) (flag32 (i.arg 1))) ]

/-- x86-64 `epoll_wait` (232), in the `do_epoll_wait` order of Linux up to v6.14. -/
def epollWaitArmX86 : SpecArm :=
  arm 232 "epoll_wait" (fun i => epollWaitSpecX86 (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)))

/-- x86-64 `epoll_wait` (232), in the order of Linux from v6.15 (`epfd` first). -/
def epollWaitArmX86FdFirst : SpecArm :=
  arm 232 "epoll_wait"
    (fun i => epollWaitSpecX86FdFirst (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)))

/-- x86-64 `epoll_pwait` (281), in the `do_epoll_wait` order of Linux up to v6.14. -/
def epollPwaitArmX86 : SpecArm :=
  arm 281 "epoll_pwait"
    (fun i => epollPwaitSpecX86 (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4) (i.arg 5))

/-- x86-64 `epoll_pwait` (281), in the order of Linux from v6.15 (`epfd` first). -/
def epollPwaitArmX86FdFirst : SpecArm :=
  arm 281 "epoll_pwait"
    (fun i => epollPwaitSpecX86FdFirst (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4)
      (i.arg 5))

/-- The family's native x86-64 arms. `epoll_wait` and `epoll_pwait` have the `do_epoll_wait`
order of Linux up to v6.14; the native table declines where the v6.15 order disagrees
(`NativeX86.All.epollOrderChaos`). -/
def fdEventsX86Arms : List SpecArm :=
  [ arm 7 "poll" (fun i => pollSpecX86 (i.arg 0) (unfds32 (i.arg 1)) (int32 (i.arg 2))),
    arm 22 "pipe" (fun i => pipeSpecX86 (i.arg 0)),
    arm 23 "select"
      (fun i => selectSpecX86 (nfds32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4)),
    arm 213 "epoll_create" (fun i => epollCreateSpecX86 (int32 (i.arg 0))),
    epollWaitArmX86,
    arm 233 "epoll_ctl"
      (fun i => epollCtlSpecX86 (fd32 (i.arg 0)) (int32 (i.arg 1)) (fd32 (i.arg 2)) (i.arg 3)),
    arm 270 "pselect6"
      (fun i => pselect6Spec (nfds32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 271 "ppoll"
      (fun i => ppollSpec (i.arg 0) (unfds32 (i.arg 1)) (i.arg 2) (i.arg 3) (i.arg 4)),
    epollPwaitArmX86,
    arm 283 "timerfd_create"
      (fun i => timerfdCreateSpec (clockid32 (i.arg 0)) (flag32 (i.arg 1))),
    arm 284 "eventfd" (fun _ => eventfdSpecX86),
    arm 290 "eventfd2" (fun i => eventfd2Spec (flag32 (i.arg 1))),
    arm 291 "epoll_create1" (fun i => epollCreate1Spec (flag32 (i.arg 0))),
    arm 293 "pipe2" (fun i => pipe2SpecX86 (i.arg 0) (pipeFlags32 (i.arg 1))) ]

end Silmaril.Process.LPS
