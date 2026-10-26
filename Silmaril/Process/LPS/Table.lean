module

public import Silmaril.Process.LPS.Sys.ReadWrite
public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Sys.Mmap
public import Silmaril.Process.LPS.Sys.MmExt
public import Silmaril.Process.LPS.Sys.FsIo
public import Silmaril.Process.LPS.Sys.FsMeta
public import Silmaril.Process.LPS.Sys.FsCtl
public import Silmaril.Process.LPS.Sys.FdEvents
public import Silmaril.Process.LPS.Sys.KernelSys
public import Silmaril.Process.LPS.Sys.Signal
public import Silmaril.Process.LPS.Sys.Futex
public import Silmaril.Process.LPS.Sys.Fork
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.Arm

/-!
# LPS in Lean: the syscall table and dispatch

Translation of LPS `Sys/Dispatch.v`, `Sys/SyscallTable.v` and `Specs.v` (upstream commit
`f1006fe8`). Numbers are the asm-generic (riscv64) ones; a machine with its own numbering
(x86-64) renumbers in its adapter or uses a native table, and an unknown number dispatches to
`unmodeled`.

LPS has 90 arms. Each family module (`Silmaril.Process.LPS.Sys.*`) exports its arms at the
asm-generic numbers as a `…LpsArms` list, each arm extracting its arguments exactly as its
`Sys/SyscallTable.v` line does (`in_arg` index and `fd32`/`pid32`/`sig32`/… narrowing).
`lpsFamilyArms` collects them, and `familySpecTable` reads them off in LPS order (`lpsSysnos`,
the order of `Sys/SyscallTable.v`, which is by number). `specTable` spells the same 90 arms out
line by line as `Sys/SyscallTable.v` does, and `specTable_eq_familySpecTable` proves the two
equal by `rfl`.

Each row has a status:

* `translated`: the arm is the translation of the LPS specification;
* `pending`: the arm is in the LPS table but its specification is not translated yet; it is
  `unmodeled` here.

No row is a `pendingArm` placeholder (`translatedArms_length`): every row is built by `arm`
from a translated specification. That count holds by construction (`arm` always sets
`.translated`), so it is a census, not evidence of translation; the evidence is the per-arm
specifications themselves, `specTable_eq_familySpecTable` (the table is the family lists, by
`rfl`) and the per-family checks. The status is kept because a pending arm only makes the Lean model **fail closed** on that call: every
outcome it has is `unmodeled`, which the run semantics turns into the error transition (see
`Silmaril.Process.LPS.Lattice` for the refinement this gives).

`specTable_eq_syscallTable` checks the numbers and names of the table against a literal copy
of `Sys/SyscallTable.v`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- The arms of `Sys/Kernel/Sys.v` and `Sys/Drivers/Char/Random.v` that no family list
exports (LPS `Sys/SyscallTable.v:98-103,129`): `getpid`, `get*id`, `gettid`, `getrandom`. -/
def kernelLpsArms : List SpecArm :=
  [ arm 172 "getpid" (fun _ => getpidSpec),
    arm 174 "getuid" (fun _ => getidSpec (·.uid)),
    arm 175 "geteuid" (fun _ => getidSpec (·.euid)),
    arm 176 "getgid" (fun _ => getidSpec (·.gid)),
    arm 177 "getegid" (fun _ => getidSpec (·.egid)),
    arm 178 "gettid" (fun _ => gettidSpec),
    arm 278 "getrandom" (fun i => getrandomSpec (i.arg 0) (i.arg 1) (i.arg 2)) ]

/-- Every family's LPS arms (asm-generic numbers), in no particular order. -/
def lpsFamilyArms : List SpecArm :=
  fsIoLpsArms ++ fsMetaLpsArms ++ fsCtlLpsArms ++ fdEventsLpsArms ++ mmLpsArms ++
    exitLpsArms ++ forkLpsArms ++ kernelLpsArms ++ kernelSysLpsArms ++ signalLpsArms ++
    futexLpsArms ++ socketLpsArms

/-- The syscall numbers of LPS `Sys/SyscallTable.v:41` `spec_table`, in its order. -/
def lpsSysnos : List Nat :=
  [ 17, 19, 20, 21, 22, 23, 24, 25, 29, 32, 35, 46, 48, 56, 57, 59, 61, 62, 63, 64, 65, 66, 67,
    68, 72, 73, 78, 79, 80, 82, 83, 85, 93, 94, 96, 98, 101, 113, 119, 123, 124, 130, 131, 132,
    134, 135, 144, 146, 147, 149, 157, 158, 159, 160, 167, 169, 172, 174, 175, 176, 177, 178,
    198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 214, 215, 216,
    220, 222, 226, 233, 242, 260, 261, 278, 435, 439 ]

/-- The table read off the family lists: for each number of `lpsSysnos`, the family arm with
that number. A number no family exports would be a `pendingArm` (`unmodeled`); there is
none. -/
def familySpecTable : List SpecArm :=
  lpsSysnos.map fun n => (lookupArm lpsFamilyArms n).getD (pendingArm n "")

/-- LPS `Sys/SyscallTable.v:41` `spec_table`: all 90 LPS arms, in LPS order, one line per
`Sys/SyscallTable.v` line with the same argument extraction (`in_arg` index and narrowing).
It is spelled out (rather than defined as `familySpecTable`) so that consumers can compute
with it cheaply; `specTable_eq_familySpecTable` proves that it is the table of the family
lists, arm by arm and specification by specification. -/
def specTable : List SpecArm :=
  [ arm 17 "getcwd" (fun i => getcwdSpec (i.arg 1)),
    arm 19 "eventfd2" (fun i => eventfd2Spec (flag32 (i.arg 1))),
    arm 20 "epoll_create1" (fun i => epollCreate1Spec (flag32 (i.arg 0))),
    arm 21 "epoll_ctl"
      (fun i => epollCtlSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (fd32 (i.arg 2)) (i.arg 3)),
    arm 22 "epoll_pwait"
      (fun i => epollPwaitSpec (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4) (i.arg 5)),
    arm 23 "dup" (fun i => dupSpec (fd32 (i.arg 0))),
    arm 24 "dup3" (fun i => dup3Spec (fd32 (i.arg 0)) (fd32 (i.arg 1)) (i.arg 2)),
    arm 25 "fcntl" (fun i => fcntlSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1)) (i.arg 2)),
    arm 29 "ioctl" (fun i => ioctlSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1))),
    arm 32 "flock" (fun i => flockSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1))),
    arm 35 "unlinkat" (fun i => unlinkatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 46 "ftruncate" (fun i => ftruncateSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 48 "faccessat" (fun i => faccessatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 56 "openat" (fun i => openatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 57 "close" (fun i => closeSpec (fd32 (i.arg 0))),
    arm 59 "pipe2" (fun i => pipe2Spec (i.arg 0) (pipeFlags32 (i.arg 1))),
    arm 61 "getdents64" (fun i => getdents64Spec (fd32 (i.arg 0)) (i.arg 2)),
    arm 62 "lseek" (fun i => lseekSpec (fd32 (i.arg 0)) (i.arg 1) (whence32 (i.arg 2))),
    arm 63 "read" (fun i => readSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 64 "write" (fun i => writeSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 65 "readv" (fun i => readvSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 66 "writev" (fun i => writevSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 67 "pread64" (fun i => pread64Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 68 "pwrite64" (fun i => pwrite64Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 72 "pselect6"
      (fun i => pselect6Spec (nfds32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 73 "ppoll" (fun i => ppollSpec (i.arg 0) (unfds32 (i.arg 1)) (i.arg 2) (i.arg 3) (i.arg 4)),
    arm 78 "readlinkat" (fun i => readlinkatSpec (fd32 (i.arg 0))),
    arm 79 "newfstatat" (fun i => newfstatatSpec (fd32 (i.arg 0)) (i.arg 1) (flag32 (i.arg 3))),
    arm 80 "fstat" (fun i => fstatSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 82 "fsync" (fun i => fsyncSpec (fd32 (i.arg 0))),
    arm 83 "fdatasync" (fun i => fsyncSpec (fd32 (i.arg 0))),
    arm 85 "timerfd_create" (fun i => timerfdCreateSpec (clockid32 (i.arg 0)) (flag32 (i.arg 1))),
    arm 93 "exit" (fun i => exitSpec (i.arg 0)),
    arm 94 "exit_group" (fun i => exitSpec (i.arg 0)),
    arm 96 "set_tid_address" (fun _ => setTidAddressSpec),
    arm 98 "futex" (fun i => futexSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 101 "nanosleep" (fun i => nanosleepSpec (i.arg 0) (i.arg 1)),
    arm 113 "clock_gettime" (fun i => clockGettimeSpec (clockid32 (i.arg 0)) (i.arg 1)),
    arm 119 "sched_setscheduler" (fun i => schedSetschedulerSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 123 "sched_getaffinity" (fun i => schedGetaffinitySpec (i.arg 1)),
    arm 124 "sched_yield" (fun _ => schedYieldSpec),
    arm 130 "tkill" (fun i => tkillSpec (pid32 (i.arg 0)) (sig32 (i.arg 1))),
    arm 131 "tgkill" (fun i => tgkillSpec (pid32 (i.arg 0)) (pid32 (i.arg 1)) (sig32 (i.arg 2))),
    arm 132 "sigaltstack" (fun i => sigaltstackSpec (i.arg 0) (i.arg 1)),
    arm 134 "rt_sigaction"
      (fun i => rtSigactionSpec (sig32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 135 "rt_sigprocmask"
      (fun i => rtSigprocmaskSpec (how32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 144 "setgid" (fun i => setidSpec credGids setCredGids false (uid32 (i.arg 0))),
    arm 146 "setuid" (fun i => setidSpec credUids setCredUids true (uid32 (i.arg 0))),
    arm 147 "setresuid" (fun i =>
      setresidSpec credUids setCredUids true (uid32 (i.arg 0)) (uid32 (i.arg 1)) (uid32 (i.arg 2))),
    arm 149 "setresgid" (fun i =>
      setresidSpec credGids setCredGids false (uid32 (i.arg 0)) (uid32 (i.arg 1)) (uid32 (i.arg 2))),
    arm 157 "setsid" (fun _ => setsidSpec),
    arm 158 "getgroups" (fun i => getgroupsSpec (i.arg 0)),
    arm 159 "setgroups" (fun _ => setgroupsSpec),
    arm 160 "uname" (fun i => unameSpec (i.arg 0)),
    arm 167 "prctl" (fun i => prctlSpec (int32 (i.arg 0)) (i.arg 1)),
    arm 169 "gettimeofday" (fun i => gettimeofdaySpec (i.arg 0) (i.arg 1)),
    arm 172 "getpid" (fun _ => getpidSpec),
    arm 174 "getuid" (fun _ => getidSpec (·.uid)),
    arm 175 "geteuid" (fun _ => getidSpec (·.euid)),
    arm 176 "getgid" (fun _ => getidSpec (·.gid)),
    arm 177 "getegid" (fun _ => getidSpec (·.egid)),
    arm 178 "gettid" (fun _ => gettidSpec),
    arm 198 "socket" (fun i => socketSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 199 "socketpair" (fun i => socketpairSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 200 "bind" (fun i => bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 201 "listen" (fun i => listenSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 202 "accept" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0),
    arm 203 "connect" (fun i => connectSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 204 "getsockname" (fun i => getsocknameSpec (fd32 (i.arg 0))),
    arm 205 "getpeername" (fun i => getpeernameSpec (fd32 (i.arg 0))),
    arm 206 "sendto"
      (fun i => sendtoSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 207 "recvfrom" (fun i => recvfromSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 208 "setsockopt"
      (fun i => setsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (int32 (i.arg 4))),
    arm 209 "getsockopt" (fun i => getsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (i.arg 4)),
    arm 210 "shutdown" (fun i => shutdownSpec (fd32 (i.arg 0)) (int32 (i.arg 1))),
    arm 211 "sendmsg" (fun i => sendmsgSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 212 "recvmsg" (fun i => recvmsgSpec (fd32 (i.arg 0)) (i.arg 2)),
    arm 214 "brk" (fun i => brkSpec (i.arg 0)),
    arm 215 "munmap" (fun i => munmapSpec (i.arg 0) (i.arg 1)),
    arm 216 "mremap" (fun i => mremapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 220 "clone" (fun i => cloneSpec (i.arg 0)),
    arm 222 "mmap" (fun i => mmapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 226 "mprotect" (fun i => mprotectSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 233 "madvise" (fun i => madviseSpec (i.arg 0) (i.arg 1) (int32 (i.arg 2))),
    arm 242 "accept4" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 260 "wait4"
      (fun i => wait4Spec (pid32 (i.arg 0)) (i.arg 1) (waitopts32 (i.arg 2)) (i.arg 3)),
    arm 261 "prlimit64" (fun i => prlimit64Spec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 278 "getrandom" (fun i => getrandomSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 435 "clone3" (fun i => clone3Spec (i.arg 0) (i.arg 1)),
    arm 439 "faccessat2" (fun i => faccessat2Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)) ]

/-- The table is exactly the arms the families export (`rfl`: same numbers, names, statuses
and specifications). -/
theorem specTable_eq_familySpecTable : specTable = familySpecTable := by
  set_option maxRecDepth 20000 in rfl

/-- LPS `Specs.v:185` `modeled_sysnos`. -/
def modeledSysnos : List Nat := armNumbers specTable

/-- LPS `Specs.v:189` `syscall_spec`, over this translation's table. -/
def syscallSpec : Sys SyscallEffect := dispatch specTable

/-- The table has LPS's 90 arms. -/
theorem specTable_length : specTable.length = 90 := by decide

/-- No number appears twice (LPS `Checks/DispatchSurface.v`). -/
theorem modeledSysnos_nodup : modeledSysnos.Nodup := by decide +kernel

/-- The numbers and names of the table are those of LPS `Sys/SyscallTable.v` (one pair per
line of `spec_table`, in order). -/
theorem specTable_eq_syscallTable :
    specTable.map (fun a => (a.no, a.name)) =
    [ (17, "getcwd"), (19, "eventfd2"), (20, "epoll_create1"), (21, "epoll_ctl"),
      (22, "epoll_pwait"), (23, "dup"), (24, "dup3"), (25, "fcntl"), (29, "ioctl"), (32, "flock"),
      (35, "unlinkat"), (46, "ftruncate"), (48, "faccessat"), (56, "openat"), (57, "close"),
      (59, "pipe2"), (61, "getdents64"), (62, "lseek"), (63, "read"), (64, "write"),
      (65, "readv"), (66, "writev"), (67, "pread64"), (68, "pwrite64"), (72, "pselect6"),
      (73, "ppoll"), (78, "readlinkat"), (79, "newfstatat"), (80, "fstat"), (82, "fsync"),
      (83, "fdatasync"), (85, "timerfd_create"), (93, "exit"), (94, "exit_group"),
      (96, "set_tid_address"), (98, "futex"), (101, "nanosleep"), (113, "clock_gettime"),
      (119, "sched_setscheduler"), (123, "sched_getaffinity"), (124, "sched_yield"),
      (130, "tkill"), (131, "tgkill"), (132, "sigaltstack"), (134, "rt_sigaction"),
      (135, "rt_sigprocmask"), (144, "setgid"), (146, "setuid"), (147, "setresuid"),
      (149, "setresgid"), (157, "setsid"), (158, "getgroups"), (159, "setgroups"), (160, "uname"),
      (167, "prctl"), (169, "gettimeofday"), (172, "getpid"), (174, "getuid"), (175, "geteuid"),
      (176, "getgid"), (177, "getegid"), (178, "gettid"), (198, "socket"), (199, "socketpair"),
      (200, "bind"), (201, "listen"), (202, "accept"), (203, "connect"), (204, "getsockname"),
      (205, "getpeername"), (206, "sendto"), (207, "recvfrom"), (208, "setsockopt"),
      (209, "getsockopt"), (210, "shutdown"), (211, "sendmsg"), (212, "recvmsg"), (214, "brk"),
      (215, "munmap"), (216, "mremap"), (220, "clone"), (222, "mmap"), (226, "mprotect"),
      (233, "madvise"), (242, "accept4"), (260, "wait4"), (261, "prlimit64"), (278, "getrandom"),
      (435, "clone3"), (439, "faccessat2") ] := by
  decide +kernel

/-- The family lists hold 90 arms, no number twice: each is used by exactly one row. -/
theorem lpsFamilyArms_length : lpsFamilyArms.length = 90 := by decide +kernel

theorem lpsFamilyArms_nodup : (armNumbers lpsFamilyArms).Nodup := by decide +kernel

/-- The rows built by `arm` (not `pendingArm` placeholders). -/
def translatedArms : List String :=
  (specTable.filter (·.status = .translated)).map (·.name)

/-- No row of the table is a `pendingArm` placeholder (by construction of `arm`; see the
module docstring for what this does and does not show). -/
theorem specTable_all_translated : specTable.all (·.status == .translated) = true := by
  decide +kernel

/-- All 90 rows are `arm`s, none a `pendingArm` placeholder. -/
theorem translatedArms_length : translatedArms.length = 90 := by decide +kernel

end Silmaril.Process.LPS
