module

public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Uapi

/-!
# LPS in Lean: process creation (`clone`, `clone3`) and the x86-64 entry points

Translation of LPS `Sys/Kernel/Fork.v` (upstream commit `f1006fe8`), lines 134-849: the
answer the **calling** process receives from `clone` (220) and `clone3` (435). As in LPS no
second process is created; the success branch only records that a child now exists
(`Model.withChildren`), which is what `wait4Spec` reads before answering `ECHILD`.
`set_tid_address_spec` (`Fork.v:123`) and `PID_MAX_ENVELOPE` (`Fork.v:72`) were already
translated in `Silmaril.Process.LPS.Sys.Kernel` and are reused here.

The modeled cases are exactly LPS's:

* `clone`: the single flag word `SIGCHLD` (a plain `fork`), tested on the whole 64-bit
  register; every other word is `unmodeled`;
* `clone3`: `size = 88` (the full `struct clone_args`), the struct wholly readable, and the
  image all zero except `exit_signal = SIGCHLD`; every other shape is `unmodeled`;
* both: `unmodeled` while a descriptor with a shared offset or shared object is open
  (`cloneNoSharedFileB`); otherwise the environment either injects one of
  `cloneErrnos` or picks a pid in `[1, 2^22)` different from the observed tid, and the
  success branch sets `children`.

## x86-64 differences

* **Register order of the legacy `clone`.** `SYSCALL_DEFINE5(clone)` in `kernel/fork.c` has
  four variants. riscv64 selects `CONFIG_CLONE_BACKWARDS` (`arch/riscv/Kconfig`), so LPS's
  `clone` reads `(flags, newsp, parent_tidptr, tls, child_tidptr)` (`Fork.v:376-379`).
  x86-64 selects none of `CLONE_BACKWARDS*` (`arch/x86/Kconfig` selects
  `CLONE_BACKWARDS` only `if X86_32`), so it takes the `#else` branch:
  `(flags, newsp, parent_tidptr, child_tidptr, tls)`. The fourth and fifth registers are
  swapped. `CloneRegs`, `cloneRegsBackwards` and `cloneRegsX86` decode the two orders. For
  the one modeled flag word `SIGCHLD` neither the tid pointers nor `tls` is dereferenced
  (the uses are gated on `CLONE_PARENT_SETTID`, `CLONE_CHILD_SETTID`,
  `CLONE_CHILD_CLEARTID` and `CLONE_SETTLS`). That is a kernel fact taken from LPS's
  comment (`Fork.v:376-385`), and it is why LPS's `clone_spec` (`Fork.v:708`) reads only
  argument 0. Given that, the two arms have the same outcomes by construction:
  `cloneSpecRegs_backwards_x86` records that both decodings agree on `flags`, and it holds by
  `rfl`. It is not independent evidence about the kernel; it would only detect a mistake in
  the decoders, not a kernel that reads the swapped registers.
* **Numbers.** `clone` is 56 and `clone3` 435 in `arch/x86/entry/syscalls/syscall_64.tbl`;
  `set_tid_address` is 218.
* **`fork` and `vfork` exist on x86-64.** x86-64 defines `__ARCH_WANT_SYS_FORK` and
  `__ARCH_WANT_SYS_VFORK` (`arch/x86/include/asm/unistd.h`), so `fork` (57) and `vfork`
  (58) are syscalls; riscv64 has neither, and LPS has no arm for them. musl's `_Fork`
  issues `SYS_fork` when it is defined and `clone(SIGCHLD, 0)` otherwise
  (`src/process/_Fork.c`), so a musl `fork()` on x86-64 reaches 57, not 56.
  `SYSCALL_DEFINE0(fork)` is `kernel_clone(&{ .exit_signal = SIGCHLD })`, the same
  arguments `clone(SIGCHLD, 0)` reaches `kernel_clone` with, so `forkSpecX86` is LPS's
  `clone_resolve` (`forkSpecX86_eq_cloneSpec`). `SYSCALL_DEFINE0(vfork)` is
  `kernel_clone(&{ .flags = CLONE_VFORK | CLONE_VM, .exit_signal = SIGCHLD })`, the word LPS
  declines, so `vforkSpecX86` is `cloneSpec (CLONE_VFORK + CLONE_VM + SIGCHLD)` (disjoint
  bits, so `+` is `|`), which is `unmodeled` (`vforkSpecX86_unmodeled`). These two arms
  are derived from LPS's `clone_spec`, not translated from an LPS arm.
* **`struct clone_args`** is eleven `__aligned_u64` fields (`include/uapi/linux/sched.h`),
  88 bytes, little-endian on both ISAs: no layout difference.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! ## The legacy `clone` (220 / x86-64 56) -/

/-- LPS `Sys/Kernel/Fork.v:393` `SIGCHLD`. -/
def SIGCHLD : Int := 17

/-- LPS `Sys/Kernel/Fork.v:510` `clone_errnos`: the environment failures admitted for the
one modeled flag word (`copy_process` resource and allocation failures, `dup_fd`'s `EMFILE`,
SELinux's `EACCES`). -/
def cloneErrnos : List Int := [EAGAIN, ENOMEM, EMFILE, EACCES]

/-- LPS `Sys/Kernel/Fork.v:564` `clone_fork_flags_b`: the whole 64-bit register is exactly
`SIGCHLD` (stricter than the kernel, which reads only the low 32 bits). -/
def cloneForkFlagsB (flags : Word) : Bool := flags == zw SIGCHLD

/-- LPS `Sys/Kernel/Fork.v:615` `clone_no_shared_file_b`: no open descriptor whose offset or
object the child would share and the model cannot express (regular files, sockets, pipe
ends). Channels, directories, `/dev/null` and `/dev/urandom` pass. -/
def cloneNoSharedFileB (fds : List (Word × FdEntry)) : Bool :=
  fds.all fun e =>
    match e.2 with
    | .file .. | .fileW .. | .fileA .. | .fileRW .. | .socket _ => false
    | .channel _ | .dir => true
    | .pipe .. => false
    | .devNull .. => true
    | .urandom => true

/-- LPS `Sys/Kernel/Fork.v:679` `clone_pid_ok_b`: a pid in `[1, PID_MAX_ENVELOPE)` and
different from the caller's tid once it has been observed. -/
def clonePidOkB (m : Model) (r : Word) : Bool :=
  decide (0 < uns r) && decide (uns r < PID_MAX_ENVELOPE) &&
    (match m.tid with
     | none => true
     | some t0 => !(r == t0))

/-- LPS `Sys/Kernel/Fork.v:699` `clone_resolve`: decline while a shared-offset descriptor is
open; otherwise an injected errno (the model untouched) or a chosen pid, recording that a
child exists. -/
def cloneResolve : Sys SyscallEffect := do
  let m ← getModel
  if !cloneNoSharedFileB m.fds then unmodeled
  else
    Sys.alt
      (do
        let e ← errnoFrom cloneErrnos
        errRet e)
      (do
        let pid ← Sys.choose fun p => clonePidOkB m p = true
        modify (·.withChildren)
        retOnly pid)

/-- LPS `Sys/Kernel/Fork.v:708` `clone_spec`: only the flag word is read. -/
def cloneSpec (flags : Word) : Sys SyscallEffect :=
  if cloneForkFlagsB flags then cloneResolve else unmodeled

/-! ## The register order of the legacy `clone` -/

/-- The five register arguments of the legacy `clone`, by meaning (`kernel/fork.c`
`SYSCALL_DEFINE5(clone)`). -/
structure CloneRegs where
  flags : Word
  newsp : Word
  parentTid : Word
  childTid : Word
  tls : Word
  deriving DecidableEq, Repr

/-- The `CONFIG_CLONE_BACKWARDS` order that LPS's riscv64 reads (`Sys/Kernel/Fork.v:376`):
`(flags, newsp, parent_tidptr, tls, child_tidptr)`. -/
def cloneRegsBackwards (i : SyscallInput) : CloneRegs :=
  ⟨i.arg 0, i.arg 1, i.arg 2, i.arg 4, i.arg 3⟩

/-- The x86-64 order (`kernel/fork.c`, the `#else` branch of `SYSCALL_DEFINE5(clone)`; x86-64
selects no `CLONE_BACKWARDS*`): `(flags, newsp, parent_tidptr, child_tidptr, tls)`. -/
def cloneRegsX86 (i : SyscallInput) : CloneRegs :=
  ⟨i.arg 0, i.arg 1, i.arg 2, i.arg 3, i.arg 4⟩

/-- LPS `Sys/Kernel/Fork.v:708` `clone_spec`, over decoded registers: for the modeled flag
word only `flags` is read (`Fork.v:379-384`). -/
def cloneSpecRegs (r : CloneRegs) : Sys SyscallEffect := cloneSpec r.flags

/-- The two orders agree on `flags`, `newsp` and `parent_tidptr` and swap the other two. -/
theorem cloneRegsX86_swap (i : SyscallInput) :
    (cloneRegsX86 i).childTid = (cloneRegsBackwards i).tls ∧
      (cloneRegsX86 i).tls = (cloneRegsBackwards i).childTid ∧
      (cloneRegsX86 i).flags = (cloneRegsBackwards i).flags :=
  ⟨rfl, rfl, rfl⟩

/-- Both decodings give the same spec, because `cloneSpecRegs` reads only `flags` (LPS
`Fork.v:379-384,708`). This holds by construction (`rfl`); the kernel fact behind it (no
dereference of the tid pointers or `tls` for `SIGCHLD`) is assumed from LPS, not proved. -/
theorem cloneSpecRegs_backwards_x86 (i : SyscallInput) :
    cloneSpecRegs (cloneRegsBackwards i) = cloneSpecRegs (cloneRegsX86 i) := rfl

/-! ## `clone3` (435 on both ISAs) -/

/-- LPS `Sys/Kernel/Fork.v:783` `CLONE_ARGS_SIZE`: `sizeof (struct clone_args)`. -/
def CLONE_ARGS_SIZE : Int := 88

/-- LPS `Sys/Kernel/Fork.v:786` `clone_args_field`: field `k` of a `struct clone_args`
image, little-endian. -/
def cloneArgsField (bs : List Byte) (k : Nat) : Word :=
  leBytesToWord ((bs.drop (8 * k)).take 8)

/-- LPS `Sys/Kernel/Fork.v:789` `clone3_fork_args_b`: the image of `clone(SIGCHLD, 0)`, all
eleven fields zero except `exit_signal` (field 4). -/
def clone3ForkArgsB (bs : List Byte) : Bool :=
  wIs0 (cloneArgsField bs 0)              -- flags
    && wIs0 (cloneArgsField bs 1)         -- pidfd
    && wIs0 (cloneArgsField bs 2)         -- child_tid
    && wIs0 (cloneArgsField bs 3)         -- parent_tid
    && cloneArgsField bs 4 == zw SIGCHLD  -- exit_signal
    && wIs0 (cloneArgsField bs 5)         -- stack
    && wIs0 (cloneArgsField bs 6)         -- stack_size
    && wIs0 (cloneArgsField bs 7)         -- tls
    && wIs0 (cloneArgsField bs 8)         -- set_tid
    && wIs0 (cloneArgsField bs 9)         -- set_tid_size
    && wIs0 (cloneArgsField bs 10)        -- cgroup

/-- LPS `Sys/Kernel/Fork.v:804` `CLONE_ARGS_SIZE_nat`. -/
def CLONE_ARGS_SIZE_nat : Nat := 88

/-- LPS `Sys/Kernel/Fork.v:806` `clone_args_size_nat_ok`. -/
theorem cloneArgsSizeNat_ok : (CLONE_ARGS_SIZE_nat : Int) = CLONE_ARGS_SIZE := rfl

/-- LPS `Sys/Kernel/Fork.v:823` `clone3_resolve`: `clone_resolve` with the struct's range in
the copy-in ledger. -/
def clone3Resolve (uargs : Word) : Sys SyscallEffect :=
  recordCopyins [(uargs, CLONE_ARGS_SIZE_nat)] cloneResolve

/-- LPS `Sys/Kernel/Fork.v:830` `clone3_resolve_inv`: stripping the ledger leaves a
`clone_resolve` outcome with the same return, model and events. -/
theorem clone3Resolve_inv {uargs : Word} {i : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List Event}
    (h : clone3Resolve uargs i m (.ok eff m' evs)) :
    ∃ e₀, cloneResolve i m (.ok e₀ m' evs) ∧ eff.ret = e₀.ret := by
  obtain ⟨e₀, m₀, evs₀, evs₂, h₀, hp, rfl⟩ := h
  cases hp
  exact ⟨e₀, by simpa using h₀, rfl⟩

/-- LPS `Sys/Kernel/Fork.v:841` `clone3_spec`: only the full-size struct, wholly readable and
of the `fork` image, is answered. -/
def clone3Spec (uargs size : Word) : Sys SyscallEffect :=
  if !(size == zw CLONE_ARGS_SIZE) then unmodeled
  else do
    let i ← input
    match readBytesMap i.mem uargs (zw CLONE_ARGS_SIZE) with
    | none => unmodeled
    | some bs => if clone3ForkArgsB bs then clone3Resolve uargs else unmodeled

/-! ## x86-64 only: `fork` (57) and `vfork` (58) -/

-- `CLONE_VM` (256) is LPS `Sys/Uapi.v:945`, already in `Silmaril.Process.LPS.Uapi`.
/-- x86-64 `CLONE_VFORK` (`include/uapi/linux/sched.h`). -/
def CLONE_VFORK : Int := 0x00004000

/-- x86-64 `fork` (57), derived from LPS `Sys/Kernel/Fork.v:699` `clone_resolve`:
`SYSCALL_DEFINE0(fork)` (`kernel/fork.c`, under `__ARCH_WANT_SYS_FORK`, which x86-64
defines) calls `kernel_clone` with `exit_signal = SIGCHLD` and no flags, the arguments
`clone(SIGCHLD, 0)` reaches it with. Not an LPS arm (riscv64 has no `fork`). -/
def forkSpecX86 : Sys SyscallEffect := cloneResolve

/-- x86-64 `vfork` (58), derived from LPS `Sys/Kernel/Fork.v:708` `clone_spec`:
`SYSCALL_DEFINE0(vfork)` calls `kernel_clone` with `CLONE_VFORK | CLONE_VM` and
`exit_signal = SIGCHLD`, a word outside LPS's allowlist. Not an LPS arm. -/
def vforkSpecX86 : Sys SyscallEffect := cloneSpec (zw (CLONE_VFORK + CLONE_VM + SIGCHLD))

/-- `fork` is `clone(SIGCHLD, …)`. -/
theorem forkSpecX86_eq_cloneSpec : forkSpecX86 = cloneSpec (zw SIGCHLD) := by
  simp [forkSpecX86, cloneSpec, cloneForkFlagsB]

/-- `vfork` declines: its outcomes are exactly `unmodeled`. -/
theorem vforkSpecX86_unmodeled : vforkSpecX86 = Sys.unmodeled := by
  unfold vforkSpecX86 cloneSpec
  rw [ite_eq_right (by decide)]

/-! ## Arms -/

/-- The LPS arms of `Sys/Kernel/Fork.v` (LPS `Sys/SyscallTable.v:76,122,130`), with the
asm-generic numbers. `set_tid_address` (96) is the arm already in `specTable`. -/
def forkLpsArms : List SpecArm :=
  [ arm 96 "set_tid_address" (fun _ => setTidAddressSpec),
    arm 220 "clone" (fun i => cloneSpecRegs (cloneRegsBackwards i)),
    arm 435 "clone3" (fun i => clone3Spec (i.arg 0) (i.arg 1)) ]

/-- The same arms with native x86-64 numbers (`syscall_64.tbl`): `clone` 56 decodes the
x86-64 register order; `fork` 57 and `vfork` 58 are the x86-64-only entry points, derived
from `clone_spec`. -/
def forkX86Arms : List SpecArm :=
  [ arm 56 "clone" (fun i => cloneSpecRegs (cloneRegsX86 i)),
    arm 57 "fork" (fun _ => forkSpecX86),
    arm 58 "vfork" (fun _ => vforkSpecX86),
    arm 218 "set_tid_address" (fun _ => setTidAddressSpec),
    arm 435 "clone3" (fun i => clone3Spec (i.arg 0) (i.arg 1)) ]

/-- The LPS arms of `Sys/Kernel/Exit.v` (LPS `Sys/SyscallTable.v:74,75,127`), as already in
`specTable`. -/
def exitLpsArms : List SpecArm :=
  [ arm 93 "exit" (fun i => exitSpec (i.arg 0)),
    arm 94 "exit_group" (fun i => exitSpec (i.arg 0)),
    arm 260 "wait4"
      (fun i => wait4Spec (pid32 (i.arg 0)) (i.arg 1) (waitopts32 (i.arg 2)) (i.arg 3)) ]

/-- The same arms with native x86-64 numbers: `exit` 60, `wait4` 61, `exit_group` 231. The
argument registers and `int` narrowings are the same on x86-64. -/
def exitX86Arms : List SpecArm :=
  [ arm 60 "exit" (fun i => exitSpec (i.arg 0)),
    arm 61 "wait4"
      (fun i => wait4Spec (pid32 (i.arg 0)) (i.arg 1) (waitopts32 (i.arg 2)) (i.arg 3)),
    arm 231 "exit_group" (fun i => exitSpec (i.arg 0)) ]

end Silmaril.Process.LPS
