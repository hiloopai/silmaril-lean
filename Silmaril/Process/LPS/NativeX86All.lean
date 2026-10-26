module

public import Silmaril.Process.LPS.X86FamilyArms
public import Silmaril.Process.LPS.X86NativeSystem
public import Silmaril.Process.LPS.Machines.X86ArchPrctl
public import Silmaril.Process.LPS.MonadIff

/-! # The complete native x86-64 table: every reference slot live, soundly

`NativeX86.table` keeps every name outside its review list `pending`. This module installs the
families' own x86-64 arms (`familyX86Arms`, 108 arms) through #3492's checked installer
(`NativeX86.checkedTableWithFamilies`), so that **all ninety reference slots** dispatch the
family's x86-64 specification at the native number (`referenceSlot_live`), and composes the
architecture-only entry points (the eighteen family legacy arms, `getrlimit` and
`arch_prctl(ARCH_SET_FS)`) separately, outside the reference denominator.

## The legacy name collisions

#3492's `Legacy.arms` and the families both export `open`, `stat`, `lstat`, `poll`, `access`,
`pipe`, `dup2`, `unlink` and `readlink` at the same native numbers, so the two lists cannot be
composed. Here the family arms win: they are direct x86-64 specifications written and reviewed
by the family owners, whereas the adapters re-dispatch into the *reference* (riscv64) arms,
whose `access_ok` is the Sv48 one. The only adapter without a family arm is `getrlimit` (97);
it is re-expressed with the x86-64 `prlimit64` (`getrlimitArm`), which is the same kernel path
(`check_prlimit_permission` returns 0 for `current` before the LSM hook, and x86-64's
`struct rlimit` is `struct rlimit64`, see `Legacy.getrlimit_layout_compatible`).

## Kernel profile

The statements are about Linux x86-64 **v6.13 through v6.18** (the range whose sources were
read for this profile; later kernels are not covered until re-checked), four-level paging, LAM
not enabled: `USER_PTR_MAX = TASK_SIZE_MAX = 2^47 - 4096` (`arch/x86/kernel/cpu/common.c`,
v6.13 and v6.18: `USER_PTR_MAX = TASK_SIZE_MAX`). This is the bound `Uaccess.accessOkbX86`
already uses. Linux **v6.12 itself is not covered**: it sets `USER_PTR_MAX = TASK_SIZE_MAX - 1`,
so a variable-size range ending exactly at `TASK_SIZE_MAX` fails `access_ok` there and passes
here. Syscall numbers are the pinned v6.12 `syscall_64.tbl`, unchanged since.

The profile assumes the following `access_ok` forms; re-checking a newer kernel means
re-reading exactly these:

* `__access_ok` and `valid_user_address` (`arch/x86/include/asm/uaccess_64.h`): base-only for
  a compile-time-constant size of at most `PAGE_SIZE`, the 64-bit-sum range check otherwise;
* `import_ubuf` and `__import_iovec`/`__import_iovec_ubuf` (`lib/iov_iter.c`): whole-range
  `access_ok` on the buffer, on the iovec array and on every segment, before any copy;
* `strncpy_from_user` (`lib/strncpy_from_user.c`): no range `access_ok`, a fault per byte;
* the `user_write_access_begin`/`user_read_access_begin` and masked/scoped user-access call
  sites (`copy_to_user`/`copy_from_user` wrappers, `put_user`/`get_user`): a call site that
  moves from a whole-range check to a base-only (masked) check makes its variable-size access
  base-only, which this profile does **not** model, so such a kernel is outside the profile.

## The `TASK_SIZE_MAX` band: chaos, the same way for every arm

x86-64 `__access_ok` checks only the base pointer when the size is a compile-time constant of
at most a page, and the whole range otherwise. Whether a call site sees a constant size is a
compiler fact (inlining, LTO); after a base-only pass, a `copy_to_user` may write the mapped
prefix below `TASK_SIZE_MAX` and then fault. So for a constant-size access of `s` bytes at a
base in `(TASK_SIZE_MAX - s, TASK_SIZE_MAX]` Linux may answer `-EFAULT` after a partial
write, or `-EFAULT` with no write. No Bool-valued `access_ok` can state that. `guard`
therefore makes **every** arm (reference slots and extensions alike) answer only `unmodeled`
when

* some argument register lies in `[TASK_SIZE_MAX, 2^47]` (never a valid x86-64 user pointer;
  this also covers the reference arms' Sv48 `access_ok`, which accepts this window), or
* a register that the arm uses as a pointer to a constant-size object of `s` bytes
  (`constPtrArgs`) lies in `(TASK_SIZE_MAX - s, TASK_SIZE_MAX)`.

`constPtrArgs` is read off `pointerAudit`, which records for **every** native arm the
argument registers that are user pointers and how they are used (constant-size, variable-size
range, path string, or not read). `pointerAudit_complete` proves every arm of `nativeTable` has
a row (a new arm cannot enter without one), `pointerAudit_exact` that no other number has one,
and `constPtrArgs_reviewed` that the derived list is the hand-reviewed one. The audit is a
reviewed table, not derived from the specifications' bodies.

This replaces the two different answers the lanes gave (`accessGateSmallX86` declined the band,
the whole-range arms answered `-EFAULT`) with one. Nested pointers (read from user memory) are
not inspected: in the current family models the only nested accesses are variable-size
(`iovec` bases, `clone3`'s argument block, `msg_name`) and therefore take the whole-range
branch exactly (for `sendmsg` this needs `Socket.sendmsgSpecX86`, which imports the iovecs
through `__import_iovec`'s `access_ok`; LPS's `sendmsg_spec` skips it, see
`Checks.Socket.sendmsgX86_iov_fault`), or reads (`pselect6`'s sigset), whose partial copy has no user-visible effect,
or single `put_user` stores, which fault as a whole on x86-64. `msg_control` is `unmodeled`
in the socket family. Variable-size accesses are exact under the kernel profile. Path strings
are read by `strncpy_from_user`, which needs no `access_ok` branch.

`guard_restricts` relates this variant to the unguarded one (`exactTable`): at each input the
guarded arm either is the exact arm or only declines, which is `Lattice.Restricts`.

## Configuration chaos: `sigaltstack`

Whether `sigaltstack` enforces the signal-frame size depends on `CONFIG_STRICT_SIGALTSTACK_SIZE`
or the `strict_sas_size=` boot parameter, and the frame size on the CPU's xsave layout
(`Signal.sigaltstackSpecX86Strict`). `sigaltstackChaos` answers the family's non-strict arm
where it agrees with every strict reading, and `unmodeled` elsewhere. `sigaltstackChaosUpTo
bound` is a finer lattice point for a declared signal-frame bound (exact for every `ss_size`
above it, `sigaltstackChaosUpTo_large`), between the chaos and the family's arm; it is not
installed, since no frame bound is asserted.

## Version chaos: `do_epoll_wait`'s order

The profile (v6.13 to v6.18) spans a change in `do_epoll_wait` (`fs/eventpoll.c`). Up to
v6.14 it checks the `maxevents` bounds (`-EINVAL`), then `access_ok` on the `events` range
(`-EFAULT`), then `fdget(epfd)` (`-EBADF`) (`fs/eventpoll.c:2541-2559` in v6.8). From v6.15
(commit `6b47d35d4d9e`, "eventpoll: abstract out parameter sanity checking") it looks `epfd`
up first and then runs `ep_check_params` (bounds, `access_ok`, `is_file_epoll`), the order of
LPS's v6.18 `epoll_pwait_outcome`. The families' x86-64 `epoll_wait` and `epoll_pwait` have
the v6.14 order (`FdEventsAbi.x86`); `epollOrderChaos` declines exactly the inputs where the
v6.15 order (`FdEventsAbi.x86FdFirst`) answers differently, an unopened `epfd` with a bad
`maxevents` or a bad `events` range past a NULL signal mask (`epollWaitOrders_agree`,
`epollWaitOrders_disagree`), and keeps the shared answer elsewhere. It also covers
`epoll_pwait2` (441) for tables that install it (`GapSweep.gapTable`).

The mechanical check that no native arm reads iovecs without `access_ok` is
`NativeX86AllReach`.

## ABI review of the remaining families

The families' x86-64 sections (module docstrings of `Sys.FsIo`, `Sys.FsIo.*`, `Sys.MmExt`,
`Sys.KernelSys`, `Sys.Socket`, `Sys.Time`, `Uapi`) were re-checked against x86-64 Linux:
`syscall_64.tbl` numbers (`familyReferenceArms_surface`, checked against
`NativeX86.numbers`, which `lps_x86_parity.py` checks against the pinned table);
`/usr/include/x86_64-linux-gnu/asm/fcntl.h` is `asm-generic/fcntl.h`, so the `O_*` and `F_*`
values are the generic ones the families use; `asm/mman.h` adds only `MAP_32BIT`/`MAP_ABOVE4G`,
which every modelled `mmap` shape declines; the LP64 structures (`iovec`, `user_msghdr`,
`sockaddr_in`, `timespec`, `timeval`, `rlimit64`, `sched_param`, `stack_t`, `dirent64`) have
the generic layout; `struct stat` (144 bytes) and `epoll_event` (12 bytes, packed) differ and
have x86-64 forms; `clone`'s trailing arguments differ (`cloneRegsX86`). The families' own
declines stay (`sched_getaffinity`'s wrapping lengths, `MSG_CMSG_COMPAT`, unknown flag bits).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.All

open Silmaril.Process.LPS

/-! ## The boundary guard -/

/-- `[TASK_SIZE_MAX, 2^47]`: not a valid x86-64 user address, but accepted by the reference
arms' Sv48 `access_ok`. -/
def inGuardWindow (w : Word) : Bool :=
  decide (taskSizeMaxX86 ≤ uns w) && decide (uns w ≤ taskSize)

/-- A base whose constant-size access of `size` bytes reaches `TASK_SIZE_MAX`. -/
def inBand (size : Nat) (w : Word) : Bool :=
  decide (taskSizeMaxX86 - size < uns w) && decide (uns w < taskSizeMaxX86)

/-- How a native arm uses an argument register that is a user pointer. -/
inductive PtrUse where
  /-- A constant-size object of this many bytes (at most a page): base-only `access_ok`, so the
  band below `TASK_SIZE_MAX` is guarded. -/
  | const (size : Nat)
  /-- A variable-size range: whole-range `access_ok` (exact under the kernel profile). -/
  | range
  /-- A path string, read by `strncpy_from_user` (no range `access_ok`). -/
  | path
  /-- A pointer the arm's specification does not read or write (it is not an argument of the
  specification, or only `unmodeled` answers could use it). -/
  | unread
  deriving DecidableEq, Repr

/-- The pointer audit: for every native number, the argument registers that are user pointers
and how the arm uses them (`some []`: no pointer argument; `none`: not audited). Sizes are the
x86-64 ones (see `constPtrArgs`). Every arm of `nativeTable` is audited (`pointerAudit_complete`),
so a new arm cannot enter the table without declaring its pointers, and the guard's
constant-size list is read off this table (`constPtrArgs`). Mapping addresses (`mmap`,
`munmap`, `mprotect`, `mremap`, `madvise`, `brk`) are not user pointers: no `access_ok`. -/
def pointerAudit : Nat → Option (List (Nat × PtrUse))
  | 0 => some [(1, .range)] | 1 => some [(1, .range)] | 2 => some [(0, .path)]
  | 3 => some [] | 4 => some [(0, .path), (1, .const 144)] | 5 => some [(1, .const 144)]
  | 6 => some [(0, .path), (1, .const 144)] | 7 => some [(0, .range)] | 8 => some []
  | 9 => some [] | 10 => some [] | 11 => some [] | 12 => some []
  | 13 => some [(1, .const 32), (2, .const 32)] | 14 => some [(1, .const 8), (2, .const 8)]
  | 16 => some [(2, .const 4096)] | 17 => some [(1, .range)] | 18 => some [(1, .range)]
  | 19 => some [(1, .range)] | 20 => some [(1, .range)] | 21 => some [(0, .path)]
  | 22 => some [(0, .const 8)]
  | 23 => some [(1, .range), (2, .range), (3, .range), (4, .const 16)]
  | 24 => some [] | 25 => some [] | 28 => some [] | 32 => some [] | 33 => some []
  | 35 => some [(0, .const 16), (1, .const 16)] | 39 => some [] | 41 => some []
  | 42 => some [(1, .range)] | 43 => some [(1, .range), (2, .const 4)]
  | 44 => some [(1, .range), (4, .range)]
  | 45 => some [(1, .range), (4, .range), (5, .const 4)]
  | 46 => some [(1, .const 56)] | 47 => some [(1, .const 56)] | 48 => some []
  | 49 => some [(1, .range)] | 50 => some [] | 51 => some [(1, .range), (2, .const 4)]
  | 52 => some [(1, .range), (2, .const 4)] | 53 => some [(3, .const 8)]
  | 54 => some [(3, .range)] | 55 => some [(3, .range), (4, .const 4)]
  | 56 => some [(2, .const 4), (3, .const 4)] | 57 => some [] | 58 => some []
  | 60 => some [] | 61 => some [(1, .const 4), (3, .const 144)] | 63 => some [(0, .const 390)]
  | 72 => some [(2, .const 4096)] | 73 => some [] | 74 => some [] | 75 => some []
  | 77 => some [] | 78 => some [(1, .range)] | 79 => some [(0, .range)]
  | 84 => some [(0, .path)] | 85 => some [(0, .path)] | 87 => some [(0, .path)]
  | 89 => some [(0, .path), (1, .range)] | 96 => some [(0, .const 16), (1, .const 8)]
  | 97 => some [(1, .const 16)] | 102 => some [] | 104 => some [] | 105 => some []
  | 106 => some [] | 107 => some [] | 108 => some [] | 112 => some []
  | 115 => some [(1, .range)] | 116 => some [(1, .range)] | 117 => some [] | 119 => some []
  | 131 => some [(0, .const 24), (1, .const 24)] | 144 => some [(2, .const 4)]
  | 157 => some [(1, .const 4096), (2, .const 4096), (3, .const 4096), (4, .const 4096)]
  | 158 => some [(1, .unread)] | 186 => some [] | 200 => some []
  | 202 => some [(0, .const 4), (3, .const 16), (4, .const 4)] | 204 => some [(2, .range)]
  | 213 => some [] | 217 => some [(1, .range)] | 218 => some [(0, .unread)]
  | 228 => some [(1, .const 16)] | 231 => some [] | 232 => some [(1, .range)]
  | 233 => some [(3, .const 12)] | 234 => some [] | 257 => some [(1, .path)]
  | 262 => some [(1, .path), (2, .const 144)] | 263 => some [(1, .path)]
  | 267 => some [(1, .path), (2, .range)] | 269 => some [(1, .path)]
  | 270 => some [(1, .range), (2, .range), (3, .range), (4, .const 16), (5, .const 16)]
  | 271 => some [(0, .range), (2, .const 16), (3, .const 8)]
  | 281 => some [(1, .range), (4, .const 8)] | 283 => some [] | 284 => some []
  | 288 => some [(1, .range), (2, .const 4)] | 290 => some [] | 291 => some []
  | 292 => some [] | 293 => some [(0, .const 8)]
  | 302 => some [(2, .const 16), (3, .const 16)] | 318 => some [(0, .range)]
  | 435 => some [(0, .range)] | 439 => some [(1, .path)]
  | _ => none

/-- The constant-size entries of an audit row. -/
def constEntries (row : List (Nat × PtrUse)) : List (Nat × Nat) :=
  row.filterMap fun p => match p.2 with
    | .const s => some (p.1, s)
    | _ => none

/-- The reviewed constant-size list, as first written by hand: the argument registers that
each native arm uses as a pointer to an object of constant
size (at most a page), with that size. Sizes are the x86-64 ones: `struct stat` 144, kernel
`struct sigaction` 32, `sigset_t` 8, `timespec`/`timeval` 16, `rusage` 144, `new_utsname` 390,
`rlimit64` 16, `stack_t` 24, `epoll_event` 12, `user_msghdr` 56, `socklen_t`/`int` 4. Where
the size depends on a sub-command (`ioctl`, `fcntl`, `prctl`) the whole page is used. -/
def constPtrArgsReviewed : Nat → List (Nat × Nat)
  | 4 => [(1, 144)] | 5 => [(1, 144)] | 6 => [(1, 144)] | 262 => [(2, 144)]
  | 13 => [(1, 32), (2, 32)] | 14 => [(1, 8), (2, 8)]
  | 16 => [(2, 4096)] | 72 => [(2, 4096)]
  | 157 => [(1, 4096), (2, 4096), (3, 4096), (4, 4096)]
  | 22 => [(0, 8)] | 293 => [(0, 8)] | 53 => [(3, 8)]
  | 23 => [(4, 16)] | 35 => [(0, 16), (1, 16)] | 56 => [(2, 4), (3, 4)]
  | 61 => [(1, 4), (3, 144)] | 63 => [(0, 390)] | 96 => [(0, 16), (1, 8)]
  | 97 => [(1, 16)] | 131 => [(0, 24), (1, 24)] | 144 => [(2, 4)]
  | 202 => [(0, 4), (3, 16), (4, 4)] | 228 => [(1, 16)] | 233 => [(3, 12)]
  | 281 => [(4, 8)] | 270 => [(4, 16), (5, 16)] | 271 => [(2, 16), (3, 8)]
  | 302 => [(2, 16), (3, 16)]
  | 43 => [(2, 4)] | 288 => [(2, 4)] | 51 => [(2, 4)] | 52 => [(2, 4)] | 45 => [(5, 4)]
  | 55 => [(4, 4)] | 46 => [(1, 56)] | 47 => [(1, 56)]
  | _ => []

/-- The guard's constant-size pointers: the `const` entries of the audit. -/
def constPtrArgs (no : Nat) : List (Nat × Nat) := constEntries ((pointerAudit no).getD [])

/-- The input is in the region where x86-64 kernels differ (see the module docstring). -/
def boundarySuspect (no : Nat) (i : SyscallInput) : Bool :=
  (List.range 6).any (fun k => inGuardWindow (i.arg k)) ||
    (constPtrArgs no).any (fun p => inBand p.2 (i.arg p.1))

/-- Decline every outcome on a boundary-suspect input; otherwise the arm itself. -/
def guard (a : SpecArm) : SpecArm :=
  { a with spec := fun i m o => if boundarySuspect a.no i = true then o = .unmodeled
                                else a.spec i m o }

@[simp] theorem guard_no (a : SpecArm) : (guard a).no = a.no := rfl
@[simp] theorem guard_name (a : SpecArm) : (guard a).name = a.name := rfl
@[simp] theorem guard_status (a : SpecArm) : (guard a).status = a.status := rfl

theorem guard_spec_of_not_suspect (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : boundarySuspect a.no i = false) :
    (guard a).spec i m o ↔ a.spec i m o := by
  simp [guard, h]

theorem guard_spec_of_suspect (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : boundarySuspect a.no i = true) :
    (guard a).spec i m o ↔ o = .unmodeled := by
  simp [guard, h]

/-- At each input the guarded arm is the arm, or it only declines (`Lattice.Restricts`). -/
theorem guard_restricts (a : SpecArm) (i : SyscallInput) (m : Model) :
    (∀ o, (guard a).spec i m o ↔ a.spec i m o) ∨ (∀ o, (guard a).spec i m o ↔ o = .unmodeled) := by
  cases h : boundarySuspect a.no i
  · exact .inl fun o => guard_spec_of_not_suspect a i m o h
  · exact .inr fun o => guard_spec_of_suspect a i m o h

/-! ## `sigaltstack` configuration chaos -/

/-- The strict readings of `sigaltstack` all agree with the arm's answer at this input. -/
def StrictAgrees (a : SpecArm) (i : SyscallInput) (m : Model) : Prop :=
  ∀ (fsize : Int) (o' : Outcome SyscallEffect),
    sigaltstackSpecX86Strict fsize (i.arg 0) (i.arg 1) i m o' ↔ a.spec i m o'

/-- The family's non-strict `sigaltstack` where every strict reading agrees with it,
`unmodeled` elsewhere; other arms unchanged. -/
def sigaltstackChaos (a : SpecArm) : SpecArm :=
  if a.no = 131 then
    { a with spec := fun i m o =>
        (StrictAgrees a i m → a.spec i m o) ∧ (¬ StrictAgrees a i m → o = .unmodeled) }
  else a

@[simp] theorem sigaltstackChaos_no (a : SpecArm) : (sigaltstackChaos a).no = a.no := by
  unfold sigaltstackChaos; split <;> rfl
@[simp] theorem sigaltstackChaos_name (a : SpecArm) : (sigaltstackChaos a).name = a.name := by
  unfold sigaltstackChaos; split <;> rfl
@[simp] theorem sigaltstackChaos_status (a : SpecArm) :
    (sigaltstackChaos a).status = a.status := by
  unfold sigaltstackChaos; split <;> rfl

theorem sigaltstackChaos_other (a : SpecArm) (h : a.no ≠ 131) : sigaltstackChaos a = a := by
  simp [sigaltstackChaos, h]

theorem sigaltstackChaos_restricts (a : SpecArm) (i : SyscallInput) (m : Model) :
    (∀ o, (sigaltstackChaos a).spec i m o ↔ a.spec i m o) ∨
      (∀ o, (sigaltstackChaos a).spec i m o ↔ o = .unmodeled) := by
  unfold sigaltstackChaos
  split
  · by_cases h : StrictAgrees a i m
    · exact .inl fun o => by simp [h]
    · exact .inr fun o => by simp [h]
  · exact .inl fun _ => Iff.rfl

/-- Where the strict readings agree, the chaos variant is the family's arm. -/
theorem sigaltstackChaos_agree (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (agree : StrictAgrees a i m) :
    (sigaltstackChaos a).spec i m o ↔ a.spec i m o := by
  unfold sigaltstackChaos
  split
  · simp [agree]
  · exact Iff.rfl

/-! ### A bounded-frame lattice point

`StrictAgrees` quantifies over every `Int` frame size, so every installing call disagrees with
some strict reading and `sigaltstackChaos` declines all of them. On a CPU and kernel whose
signal frame is at most `bound` bytes, only the strict readings with `fsize ≤ bound` are
possible; `sigaltstackChaosUpTo bound` declines only where one of those disagrees. It sits
between the two (`sigaltstackChaos_restricts_upTo`, `sigaltstackChaosUpTo_restricts`), is
monotone in the bound (`sigaltstackChaosUpTo_mono`), and is the family's arm for every
`ss_size` above the bound (`sigaltstackChaosUpTo_large`). It is sound only under the declared
frame bound, so the native table keeps the unbounded `sigaltstackChaos`; no bound is asserted
here for any CPU. -/

/-- The strict readings with a frame of at most `bound` bytes agree with the arm. -/
def StrictAgreesUpTo (bound : Int) (a : SpecArm) (i : SyscallInput) (m : Model) : Prop :=
  ∀ (fsize : Int), fsize ≤ bound → ∀ (o' : Outcome SyscallEffect),
    sigaltstackSpecX86Strict fsize (i.arg 0) (i.arg 1) i m o' ↔ a.spec i m o'

/-- The family's `sigaltstack` where every strict reading with a frame of at most `bound`
bytes agrees with it, `unmodeled` elsewhere; other arms unchanged. -/
def sigaltstackChaosUpTo (bound : Int) (a : SpecArm) : SpecArm :=
  if a.no = 131 then
    { a with spec := fun i m o =>
        (StrictAgreesUpTo bound a i m → a.spec i m o) ∧
          (¬ StrictAgreesUpTo bound a i m → o = .unmodeled) }
  else a

theorem strictAgreesUpTo_of_strictAgrees (bound : Int) (a : SpecArm) (i : SyscallInput)
    (m : Model) (h : StrictAgrees a i m) : StrictAgreesUpTo bound a i m :=
  fun fsize _ => h fsize

theorem strictAgreesUpTo_mono {b b' : Int} (hb : b ≤ b') (a : SpecArm) (i : SyscallInput)
    (m : Model) (h : StrictAgreesUpTo b' a i m) : StrictAgreesUpTo b a i m :=
  fun fsize hf => h fsize (le_trans hf hb)

/-- The bounded variant restricts the family's arm. -/
theorem sigaltstackChaosUpTo_restricts (bound : Int) (a : SpecArm) (i : SyscallInput)
    (m : Model) :
    (∀ o, (sigaltstackChaosUpTo bound a).spec i m o ↔ a.spec i m o) ∨
      (∀ o, (sigaltstackChaosUpTo bound a).spec i m o ↔ o = .unmodeled) := by
  unfold sigaltstackChaosUpTo
  split
  · by_cases h : StrictAgreesUpTo bound a i m
    · exact .inl fun o => by simp [h]
    · exact .inr fun o => by simp [h]
  · exact .inl fun _ => Iff.rfl

/-- The unbounded chaos restricts the bounded one. -/
theorem sigaltstackChaos_restricts_upTo (bound : Int) (a : SpecArm) (i : SyscallInput)
    (m : Model) :
    (∀ o, (sigaltstackChaos a).spec i m o ↔ (sigaltstackChaosUpTo bound a).spec i m o) ∨
      (∀ o, (sigaltstackChaos a).spec i m o ↔ o = .unmodeled) := by
  unfold sigaltstackChaos sigaltstackChaosUpTo
  split
  · by_cases h : StrictAgrees a i m
    · have h' := strictAgreesUpTo_of_strictAgrees bound a i m h
      exact .inl fun o => by simp [h, h']
    · exact .inr fun o => by simp [h]
  · exact .inl fun _ => Iff.rfl

/-- A smaller bound restricts a larger one. -/
theorem sigaltstackChaosUpTo_mono {b b' : Int} (hb : b ≤ b') (a : SpecArm) (i : SyscallInput)
    (m : Model) :
    (∀ o, (sigaltstackChaosUpTo b' a).spec i m o ↔ (sigaltstackChaosUpTo b a).spec i m o) ∨
      (∀ o, (sigaltstackChaosUpTo b' a).spec i m o ↔ o = .unmodeled) := by
  unfold sigaltstackChaosUpTo
  split
  · by_cases h : StrictAgreesUpTo b' a i m
    · have h' := strictAgreesUpTo_mono hb a i m h
      exact .inl fun o => by simp [h, h']
    · exact .inr fun o => by simp [h]
  · exact .inl fun _ => Iff.rfl

/-- `sigaltstackSpecWith` reads its size check only at the `stack_t` it copies in. -/
theorem sigaltstackSpecWith_congr (v₁ v₂ : Word → Bool) (uss uoss : Word) (i : SyscallInput)
    (m : Model) (o : Outcome SyscallEffect)
    (h : ∀ bs, sigaltstackAt i.mem uss = some bs → v₁ (ssSizeOf bs) = v₂ (ssSizeOf bs)) :
    sigaltstackSpecWith v₁ uss uoss i m o ↔ sigaltstackSpecWith v₂ uss uoss i m o := by
  unfold sigaltstackSpecWith
  rw [Sys.bind_getModel_iff, Sys.bind_getModel_iff]
  split
  · exact Iff.rfl
  split
  · exact Iff.rfl
  split
  · exact Iff.rfl
  rw [Sys.bind_input_iff, Sys.bind_input_iff]
  cases hs : sigaltstackAt i.mem uss with
  | none => exact Iff.rfl
  | some bs => dsimp only; rw [h bs hs]

/-- Above the bound the strict readings all agree with the family's arm. -/
theorem strictAgreesUpTo_large (bound : Int) (a : SpecArm)
    (ha : ∀ i, a.spec i = sigaltstackSpecX86 (i.arg 0) (i.arg 1) i) (i : SyscallInput)
    (m : Model) (large : ∀ bs, sigaltstackAt i.mem (i.arg 0) = some bs →
      bound < uns (ssSizeOf bs)) :
    StrictAgreesUpTo bound a i m := by
  intro fsize hf o'
  rw [ha]
  unfold sigaltstackSpecX86Strict sigaltstackSpecX86 sigaltstackSpec
  exact sigaltstackSpecWith_congr _ _ _ _ i m o' fun bs hbs => by
    have := large bs hbs
    simp only [decide_eq_true_eq]; omega

/-- **Large alternate stacks are exact** under the bounded variant: for an `ss_size` above the
frame bound, the bounded variant is the family's `sigaltstack`. -/
theorem sigaltstackChaosUpTo_large (bound : Int) (a : SpecArm) (ha131 : a.no = 131)
    (ha : ∀ i, a.spec i = sigaltstackSpecX86 (i.arg 0) (i.arg 1) i) (i : SyscallInput)
    (m : Model) (o : Outcome SyscallEffect)
    (large : ∀ bs, sigaltstackAt i.mem (i.arg 0) = some bs → bound < uns (ssSizeOf bs)) :
    (sigaltstackChaosUpTo bound a).spec i m o ↔ a.spec i m o := by
  have h := strictAgreesUpTo_large bound a ha i m large
  simp [sigaltstackChaosUpTo, ha131, h]

/-! ## Version chaos: `do_epoll_wait`'s order -/

/-- `epoll_pwait2`'s timeout passes (`get_timespec64` and `timespec64_valid`), so that
`do_epoll_pwait` runs. -/
def timeoutPasses : PselectTimeout → Bool
  | .toFault => false
  | .toInval => false
  | _ => true

/-- At `epoll_wait` (232), `epoll_pwait` (281) and `epoll_pwait2` (441), the input is one on
which the two `do_epoll_wait` orders of the profile (v6.13 and v6.14: `maxevents`, `access_ok`,
then `epfd`; v6.15 to v6.18: `epfd` first, commit `6b47d35d4d9e`) give different answers
(`epollWaitOrders_agree`, `epollPwaitOrders_agree`); `false` at every other number. The
arguments are read as the arms read them. -/
def epollOrderDiffers (no : Nat) (i : SyscallInput) (m : Model) : Bool :=
  if no = 232 then epollWaitOrdersDiffer m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2))
  else if no = 281 then
    epollPwaitOrdersDiffer i m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4) (i.arg 5)
  else if no = 441 then
    timeoutPasses (pselectTimeout i.mem (i.arg 3)) &&
      epollPwaitOrdersDiffer i m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4)
        (i.arg 5)
  else false

theorem epollOrderDiffers_other (no : Nat) (i : SyscallInput) (m : Model) (h232 : no ≠ 232)
    (h281 : no ≠ 281) (h441 : no ≠ 441) : epollOrderDiffers no i m = false := by
  simp [epollOrderDiffers, h232, h281, h441]

/-- Decline every outcome where the `do_epoll_wait` orders disagree; otherwise the arm. -/
def epollOrderChaos (a : SpecArm) : SpecArm :=
  { a with spec := fun i m o => if epollOrderDiffers a.no i m = true then o = .unmodeled
                                else a.spec i m o }

@[simp] theorem epollOrderChaos_no (a : SpecArm) : (epollOrderChaos a).no = a.no := rfl
@[simp] theorem epollOrderChaos_name (a : SpecArm) : (epollOrderChaos a).name = a.name := rfl
@[simp] theorem epollOrderChaos_status (a : SpecArm) :
    (epollOrderChaos a).status = a.status := rfl

theorem epollOrderChaos_spec_of_agree (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : epollOrderDiffers a.no i m = false) :
    (epollOrderChaos a).spec i m o ↔ a.spec i m o := by
  simp [epollOrderChaos, h]

theorem epollOrderChaos_spec_of_differ (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : epollOrderDiffers a.no i m = true) :
    (epollOrderChaos a).spec i m o ↔ o = .unmodeled := by
  simp [epollOrderChaos, h]

theorem epollOrderChaos_other (a : SpecArm) (h232 : a.no ≠ 232) (h281 : a.no ≠ 281)
    (h441 : a.no ≠ 441) : epollOrderChaos a = a := by
  have h := epollOrderDiffers_other a.no
  cases a
  simp only [epollOrderChaos] at h ⊢
  congr
  funext i m o
  simp [h i m h232 h281 h441]

theorem epollOrderChaos_restricts (a : SpecArm) (i : SyscallInput) (m : Model) :
    (∀ o, (epollOrderChaos a).spec i m o ↔ a.spec i m o) ∨
      (∀ o, (epollOrderChaos a).spec i m o ↔ o = .unmodeled) := by
  cases h : epollOrderDiffers a.no i m
  · exact .inl fun o => epollOrderChaos_spec_of_agree a i m o h
  · exact .inr fun o => epollOrderChaos_spec_of_differ a i m o h

/-- The chaos applied to every native arm: configuration chaos, version chaos (the
`do_epoll_wait` order), then the boundary guard. -/
def chaos (a : SpecArm) : SpecArm := guard (epollOrderChaos (sigaltstackChaos a))

@[simp] theorem chaos_no (a : SpecArm) : (chaos a).no = a.no := by simp [chaos]
@[simp] theorem chaos_name (a : SpecArm) : (chaos a).name = a.name := by simp [chaos]
@[simp] theorem chaos_status (a : SpecArm) : (chaos a).status = a.status := by simp [chaos]

theorem chaos_restricts (a : SpecArm) (i : SyscallInput) (m : Model) :
    (∀ o, (chaos a).spec i m o ↔ a.spec i m o) ∨ (∀ o, (chaos a).spec i m o ↔ o = .unmodeled) := by
  rcases guard_restricts (epollOrderChaos (sigaltstackChaos a)) i m with h | h
  · rcases epollOrderChaos_restricts (sigaltstackChaos a) i m with h' | h'
    · rcases sigaltstackChaos_restricts a i m with h'' | h''
      · exact .inl fun o => ((h o).trans (h' o)).trans (h'' o)
      · exact .inr fun o => ((h o).trans (h' o)).trans (h'' o)
    · exact .inr fun o => (h o).trans (h' o)
  · exact .inr h

/-! ## The arms -/

/-- A family arm sits in a reference slot when its native number and name are a row of the
native catalogue `NativeX86.numbers`. -/
def isReferenceSlot (a : SpecArm) : Bool :=
  numbers.any fun row => row.nativeNo == a.no && row.name == a.name

/-- The families' x86-64 arms for the ninety reference slots. -/
def familyReferenceArms : List SpecArm := familyX86Arms.filter isReferenceSlot

/-- The families' x86-64-only (legacy) arms. -/
def familyExtensionArms : List SpecArm := familyX86Arms.filter (fun a => !isReferenceSlot a)

/-- x86-64 `getrlimit` (97): `do_prlimit(current, resource, NULL, &value)` and a
`copy_to_user` of the LP64 `struct rlimit`, the path of `prlimit64(0, resource, NULL, rlim)`. -/
def getrlimitArm : SpecArm :=
  arm 97 "getrlimit" (fun i => prlimit64SpecX86 0 (i.arg 0) 0 (i.arg 1))

/-- The architecture-only entry points, before the chaos: family legacy arms, `getrlimit`,
`arch_prctl`. -/
def extensionArms : List SpecArm := familyExtensionArms ++ [getrlimitArm, archPrctlArm]

theorem familyReferenceArms_length : familyReferenceArms.length = 90 := by decide +kernel

theorem familyExtensionArms_length : familyExtensionArms.length = 18 := by decide +kernel

/-- The family arms cover exactly the ninety catalogue slots, in some order. -/
theorem familyReferenceArms_surface :
    ∀ row ∈ numbers, (lookupArm familyReferenceArms row.nativeNo).map (·.name) = some row.name := by
  decide +kernel

/-- The extension names, with no reference slot among them. -/
theorem extensionArms_names :
    extensionArms.map (fun a => (a.no, a.name)) =
      [(2, "open"), (21, "access"), (33, "dup2"), (85, "creat"),
       (4, "stat"), (6, "lstat"), (78, "getdents"), (84, "rmdir"), (87, "unlink"),
       (89, "readlink"), (7, "poll"), (22, "pipe"), (23, "select"), (213, "epoll_create"),
       (232, "epoll_wait"), (284, "eventfd"), (57, "fork"), (58, "vfork"), (97, "getrlimit"),
       (158, "arch_prctl")] := by
  decide +kernel

/-! ## The tables -/

/-- The native table built from arms transformed by `g`: the transformed extensions, then the
ninety reference slots with the transformed family arms installed. -/
def tableWith (g : SpecArm → SpecArm) : List SpecArm :=
  extensionArms.map g ++ tableWithFamilies specTable (familyReferenceArms.map g)

/-- The exact variant: the families' arms as they are. -/
def exactTable : List SpecArm := tableWith id

/-- The sound variant used by statements: boundary, configuration and version chaos on every arm. -/
def nativeTable : List SpecArm := tableWith chaos

/-- The ninety reference slots of `nativeTable`. -/
def referenceTable : List SpecArm :=
  tableWithFamilies specTable (familyReferenceArms.map chaos)

/-- #3492's checked installer accepts the chaos family arms. -/
theorem referenceOverrides_wf : FamiliesWfFor specTable (familyReferenceArms.map chaos) := by
  have h : FamiliesWfFor specTable familyReferenceArms := by decide +kernel
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have e : armNumbers (familyReferenceArms.map chaos) = armNumbers familyReferenceArms := by
      simp [armNumbers, List.map_map, Function.comp_def]
    rw [e]; exact h.1.1
  · intro native mem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 mem
    simpa using h.1.2 a ha
  · intro native mem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 mem
    simpa using h.2 a ha

theorem checked_referenceTable :
    checkedTableWithFamilies specTable (familyReferenceArms.map chaos) = some referenceTable := by
  simp [checkedTableWithFamilies, referenceOverrides_wf, referenceTable]

theorem nativeTable_eq : nativeTable = extensionArms.map chaos ++ referenceTable := rfl

/-! ### Lookup lemmas -/

theorem lookupArm_no {t : List SpecArm} {n : Nat} {a : SpecArm} (h : lookupArm t n = some a) :
    a.no = n := by
  induction t with
  | nil => simp [lookupArm] at h
  | cons b r ih =>
    simp only [lookupArm] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem lookupArm_mem' {t : List SpecArm} {n : Nat} {a : SpecArm}
    (h : lookupArm t n = some a) : a ∈ t := by
  induction t with
  | nil => simp [lookupArm] at h
  | cons b r ih =>
    simp only [lookupArm] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookupArm_map (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no) (t : List SpecArm)
    (n : Nat) : lookupArm (t.map g) n = (lookupArm t n).map g := by
  induction t with
  | nil => rfl
  | cons b r ih =>
    simp only [List.map_cons, lookupArm, hg]
    split <;> simp [ih]

theorem lookupArm_append (s t : List SpecArm) (n : Nat) :
    lookupArm (s ++ t) n = (lookupArm s n).or (lookupArm t n) := by
  induction s with
  | nil => simp [lookupArm]
  | cons b r ih =>
    simp only [List.cons_append, lookupArm]
    split <;> simp [ih]

theorem lookupArm_none_of_not_mem (t : List SpecArm) (n : Nat) (h : n ∉ armNumbers t) :
    lookupArm t n = none := by
  induction t with
  | nil => rfl
  | cons b r ih =>
    simp only [armNumbers, List.map_cons, List.mem_cons, not_or] at h
    simp only [lookupArm, show b.no ≠ n from Ne.symm h.1, ↓reduceIte]
    exact ih h.2

theorem lookupArm_tableWithFamilies (overrides : List SpecArm) (n : Nat) :
    lookupArm (tableWithFamilies specTable overrides) n =
      (lookupArm (table specTable) n).map (installArm overrides) := by
  unfold tableWithFamilies
  exact lookupArm_map _ (installArm_number overrides) _ n

theorem extension_numbers_not_reference :
    ∀ row ∈ numbers, row.nativeNo ∉ armNumbers extensionArms := by
  decide +kernel

theorem reference_slots_present :
    ∀ row ∈ numbers, (lookupArm (table specTable) row.nativeNo).map (·.name) = some row.name := by
  decide +kernel

/-- Every number of the full table is distinct. -/
theorem tableWith_numbers (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no) :
    armNumbers (tableWith g) = armNumbers extensionArms ++ armNumbers (table specTable) := by
  simp [tableWith, armNumbers, List.map_map, Function.comp_def, hg, tableWithFamilies]

theorem exactNumbers_nodup :
    (armNumbers extensionArms ++ armNumbers (table specTable)).Nodup := by decide +kernel

theorem nativeTable_numbers_nodup : (armNumbers nativeTable).Nodup := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; exact exactNumbers_nodup

theorem exactTable_numbers_nodup : (armNumbers exactTable).Nodup := by
  rw [exactTable, tableWith_numbers id (fun _ => rfl)]; exact exactNumbers_nodup

theorem nativeTable_length : nativeTable.length = 110 := by
  simp [nativeTable, tableWith, nativeFamilies_length, extensionArms,
    familyExtensionArms_length]

/-! ## Every reference slot is live, with the family's specification -/

/-- **All ninety reference slots are live.** For every row of the native catalogue, the
native table's arm at that number is the reference slot's name, is translated, and its
specification is the chaos form of the family's own x86-64 arm `src` (an element of
`familyX86Arms` with the same native number and name). -/
theorem referenceSlot_tableWith (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no)
    (hname : ∀ a, (g a).name = a.name) (hstatus : ∀ a, (g a).status = a.status)
    (row : NativeNumber) (mem : row ∈ numbers) :
    ∃ a src, lookupArm (tableWith g) row.nativeNo = some a ∧ src ∈ familyX86Arms ∧
      src.no = row.nativeNo ∧ src.name = row.name ∧ a.no = row.nativeNo ∧ a.name = row.name ∧
      a.status = .translated ∧ a.spec = (g src).spec := by
  obtain ⟨s, hs, hsname⟩ : ∃ s, lookupArm (table specTable) row.nativeNo = some s ∧
      s.name = row.name := by
    have h := reference_slots_present row mem
    cases e : lookupArm (table specTable) row.nativeNo with
    | none => simp [e] at h
    | some s => exact ⟨s, rfl, by simpa [e] using h⟩
  obtain ⟨src, hsrc, hsrcname⟩ : ∃ src, lookupArm familyReferenceArms row.nativeNo = some src ∧
      src.name = row.name := by
    have h := familyReferenceArms_surface row mem
    cases e : lookupArm familyReferenceArms row.nativeNo with
    | none => simp [e] at h
    | some s => exact ⟨s, rfl, by simpa [e] using h⟩
  have hsno := lookupArm_no hs
  have hsrcno := lookupArm_no hsrc
  have srcMem : src ∈ familyX86Arms := (List.mem_filter.1 (lookupArm_mem' hsrc)).1
  have srcTranslated : src.status = .translated := by
    have := List.all_eq_true.1 familyX86Arms_all_translated src srcMem
    simpa using this
  have hover : lookupArm (familyReferenceArms.map g) s.no = some (g src) := by
    rw [lookupArm_map g hg, hsno, hsrc]; rfl
  refine ⟨installArm (familyReferenceArms.map g) s, src, ?_, srcMem, hsrcno, hsrcname, ?_, ?_,
    ?_, ?_⟩
  · rw [tableWith, lookupArm_append, lookupArm_map g hg, lookupArm_none_of_not_mem _ _
      (extension_numbers_not_reference row mem), lookupArm_tableWithFamilies, hs]
    rfl
  · simp [hsno]
  · simp [hsname]
  · simp [installArm, hover, hname, hsrcname, hsname, hstatus, srcTranslated]
  · simp [installArm, hover, hname, hsrcname, hsname]

theorem referenceSlot_live (row : NativeNumber) (mem : row ∈ numbers) :
    ∃ a src, lookupArm nativeTable row.nativeNo = some a ∧ src ∈ familyX86Arms ∧
      src.no = row.nativeNo ∧ src.name = row.name ∧ a.no = row.nativeNo ∧ a.name = row.name ∧
      a.status = .translated ∧ a.spec = (chaos src).spec :=
  referenceSlot_tableWith chaos chaos_no chaos_name chaos_status row mem

theorem referenceSlot_exact (row : NativeNumber) (mem : row ∈ numbers) :
    ∃ a src, lookupArm exactTable row.nativeNo = some a ∧ src ∈ familyX86Arms ∧
      src.no = row.nativeNo ∧ src.name = row.name ∧ a.no = row.nativeNo ∧ a.name = row.name ∧
      a.status = .translated ∧ a.spec = src.spec :=
  referenceSlot_tableWith id (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) row mem

/-- Dispatch at a reference slot is the chaos form of the family's x86-64 arm. -/
theorem dispatch_referenceSlot (row : NativeNumber) (mem : row ∈ numbers)
    (input : SyscallInput) (number : input.sysno.toNat = row.nativeNo) :
    ∃ src ∈ familyX86Arms, src.no = row.nativeNo ∧ src.name = row.name ∧
      ∀ model outcome, dispatch nativeTable input model outcome ↔ (chaos src).spec input model outcome := by
  obtain ⟨a, src, ha, srcMem, srcNo, srcName, -, -, -, spec⟩ := referenceSlot_live row mem
  refine ⟨src, srcMem, srcNo, srcName, fun model outcome => ?_⟩
  simp only [dispatch, number, ha, spec]

/-- No reference slot of the native table is pending (a census; `referenceSlot_live` is the
statement about specifications). -/
theorem referenceTable_all_translated :
    referenceTable.all (·.status == .translated) = true := by decide +kernel

theorem referenceTable_length : referenceTable.length = 90 := nativeFamilies_length _

/-! ## The pointer audit covers the table -/

/-- Every arm of the native table has a pointer-audit row. -/
theorem pointerAudit_complete : ∀ n ∈ armNumbers nativeTable, (pointerAudit n).isSome := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; decide +kernel

/-- No number outside the table is audited (the audit is not padded). -/
theorem pointerAudit_exact : ∀ n < 512, (pointerAudit n).isSome → n ∈ armNumbers nativeTable := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; decide +kernel

/-- Audit rows name registers `0..5`, each at most once, and constant sizes of at most a page. -/
theorem pointerAudit_wf : ∀ n ∈ armNumbers nativeTable,
    (((pointerAudit n).getD []).map (·.1)).Nodup ∧ ((pointerAudit n).getD []).all
      (fun p => decide (p.1 < 6) && match p.2 with | .const s => decide (s ≤ 4096) | _ => true) := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; decide +kernel

/-- The audit reproduces the hand-reviewed constant-size list on every native arm. -/
theorem constPtrArgs_reviewed : ∀ n ∈ armNumbers nativeTable, constPtrArgs n = constPtrArgsReviewed n := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; decide +kernel

end Silmaril.Process.LPS.NativeX86.All
