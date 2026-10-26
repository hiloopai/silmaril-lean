module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.MonadExt
public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Sys.AccessGate

/-!
# LPS in Lean: signals (`rt_sigaction`, `rt_sigprocmask`, `sigaltstack`, `tkill`, `tgkill`)

Translation of LPS `Sys/Kernel/Signal.v` (upstream commit `f1006fe8`), the specification of
Linux `kernel/signal.c`. The signal setters of `Monad.v:347-357` are those of `MonadExt`.

The model delivers no signal: `SStep` has no asynchronous transition and an `Event` is a
read, a write, an exit or a kill. Each arm is narrow for that reason, and the reasons are
LPS's (`Sys/Kernel/Signal.v:25-178`, `:431-691`, `:1078-1205`, `:1314-1421`):

* `rt_sigaction` (134): `-EINVAL` for a wrong `sigsetsize`; a non-NULL `oact` is `unmodeled`
  (the previous disposition is not known); with `act` NULL, 0 for a signal in 1..64 and
  `-EINVAL` otherwise; with `act` non-NULL, `-EFAULT` unless the whole kernel `struct
  sigaction` is readable, then `-EINVAL` for an invalid signal and for SIGKILL/SIGSTOP, then
  `unmodeled` for `SA_RESTART` or any flag outside the accepted set, then 0 (recording
  nothing) for SIGINT and SIGTERM and `unmodeled` for every other signal.
* `rt_sigprocmask` (135): the mask is state (`ProcState.sigmask`, initially the input's
  `sigmask`). `-EINVAL` for a wrong `sigsetsize`; with `nset` NULL, `how` is not looked at and
  `oset` gets the entry mask; with `nset` non-NULL, `-EFAULT` unless its 8 bytes are
  readable, then SIGKILL/SIGSTOP are stripped, `-EINVAL` for a bad `how`, then the install,
  which **kills** the process by SIGABRT when a pending SIGABRT becomes unblocked; `oset` is
  written last with the entry mask (`-EFAULT` outside `access_ok`, `unmodeled` when only
  partly writable).
* `sigaltstack` (132): one bit of state (`ProcState.sigaltstackInstalled`). Once a stack is
  installed every call is `unmodeled`; a non-NULL `uoss` is `unmodeled`; otherwise the kernel
  answers (`EFAULT`, `EINVAL`, `ENOMEM`, 0), except the zero-`ss_sp`/zero-`ss_size` fast-path
  shadow, which is `unmodeled`.
* `tkill` (130) and `tgkill` (131): `unmodeled` unless the input declares `abort()` terminal
  (`ProcInput.abortTerminal`). Then `-EINVAL` for a non-positive pid, `-ESRCH` for a `tgkill`
  whose tgid is not the caller's, `-EINVAL` for a signal above 64, and SIGABRT to the caller
  itself is the abort path: **killed** by SIGABRT (`Model.withKilled`, which the run semantics
  turns into a `killEv`, never an `exitEv`) when SIGABRT is unblocked, and pending
  (`withSigabrtPending`) when it is blocked. Every other target or signal is `unmodeled`.

## x86-64 differences

* **`struct sigaction`**. The x86-64 kernel's `struct sigaction`
  (`arch/x86/include/uapi/asm/signal.h`, the `__KERNEL__` struct of
  `include/linux/signal_types.h` with `__ARCH_HAS_SA_RESTORER`) is `sa_handler` (0),
  `sa_flags` (8, `unsigned long`), `sa_restorer` (16), `sa_mask` (24): 32 bytes, against
  riscv64's 24 bytes with no `sa_restorer`. `SYSCALL_DEFINE4(rt_sigaction)` copies
  `sizeof(struct sigaction)` with one `copy_from_user`, so on x86-64 `-EFAULT` is decided on
  32 bytes (`sigactionAbiX86`). The flags word is at offset 8 on both. musl's x86-64
  `struct k_sigaction` is the same 32 bytes, so the riscv64 trailing-slack note
  (`Sys/Kernel/Signal.v:302`) has no x86-64 counterpart.
* **`SA_RESTORER`**. x86-64 defines `SA_RESTORER = 0x04000000`, and it is in x86-64's
  `UAPI_SA_FLAGS` (`include/linux/signal_types.h`, `__ARCH_UAPI_SA_FLAGS`), so
  `do_sigaction` keeps it. Its whole meaning is how a handler returns: the kernel reads it
  only in `x64_setup_rt_frame` (`arch/x86/kernel/signal_64.c`), which pushes `sa_restorer` as
  the return address and fails the delivery without it. It is therefore one of the
  "delivery-only" bits LPS accepts as a no-op (`Sys/Kernel/Signal.v:220-233`), and
  `saFlagsAcceptedX86` is LPS's accepted set with `SA_RESTORER` added. This is not a
  convenience: musl (`src/signal/sigaction.c`, `ksa.flags = sa->sa_flags | SA_RESTORER`) and
  glibc set it on every x86-64 `sigaction`, so a gate without it would decline every libc
  install. An install without `SA_RESTORER` is answered too, as Linux does at the
  `rt_sigaction`: the missing restorer would matter only at a delivery, which cannot occur.
  `sigactionAbiX86Strict` is the alternative reading that treats `SA_RESTORER` like a bit
  outside the accepted set (`unmodeled`), as LPS treats the pre-1.2.4 musl riscv64
  `SA_RESTORER` (`Sys/Kernel/Signal.v:242-256`); it is kept for comparison and not wired.
  The x86-only in-kernel bits `SA_IA32_ABI` (0x02000000) and `SA_X32_ABI` (0x01000000) are
  outside `UAPI_SA_FLAGS`; as for every such bit, the kernel masks them silently and the model
  declines (`Sys/Kernel/Signal.v:267-278`).
* **Fault signals**. The accepted signals stay SIGINT and SIGTERM. On x86-64 the machine can
  also raise SIGFPE (8, the `#DE` divide error), which riscv64 never raises; it is outside the
  accepted set already, so an install for it declines as LPS's SIGSEGV/SIGBUS/SIGILL/SIGTRAP
  installs do.
* **`stack_t`** has the same layout on x86-64: `arch/x86/include/uapi/asm/signal.h` defines
  its own, `ss_sp` (0), `int ss_flags` (8, then 4 bytes of padding), `ss_size` (16): 24 bytes,
  as asm-generic's. `MINSIGSTKSZ` is 2048 on both. The second lower bound, `sigaltstack_size_valid`,
  differs: x86-64 selects `DYNAMIC_SIGFRAME`, and `arch/x86/kernel/signal.c`'s
  implementation returns true unless `strict_sigaltstack_size`
  (`CONFIG_STRICT_SIGALTSTACK_SIZE` or the `strict_sas_size=` boot parameter) is set or the
  process was granted a dynamic xfeature (AMX, `arch_prctl(ARCH_REQ_XCOMP_PERM)`, which no
  modeled call grants). `sigaltstackSpecX86` is LPS's arm under that premise (the analogue of
  LPS's "vector state off" premise, `Sys/Kernel/Signal.v:1157-1191`), and
  `sigaltstackSpecX86Strict fsize` is the arm of a strict kernel whose signal-frame size is
  `fsize` (`-ENOMEM` unless `ss_size > fsize`).
* **`access_ok`** of the 8-byte `oset` copy-out is the whole-range check of x86-64's
  out-of-line `copy_to_user` against `USER_PTR_MAX` (`accessGateX86`, the native table's
  v6.13+ profile; v6.8 differs in the band, see `Silmaril.Process.LPS.Sys.AccessGate`); the
  former base-only reading, which declines the band, is kept as `rtSigprocmaskSpecX86Small`.
* `sigset_t` (8 bytes, `_NSIG = 64`), the signal numbers, the `int` narrowings and the musl
  abort sequence (`rt_sigprocmask(SIG_BLOCK, app_mask, &old, 8)`, `tkill(tid, SIGABRT)`,
  `rt_sigprocmask(SIG_SETMASK, &old, 0, 8)`) are the same; only the syscall numbers differ
  (`arch/x86/entry/syscalls/syscall_64.tbl`: `rt_sigaction` 13, `rt_sigprocmask` 14,
  `sigaltstack` 131, `tkill` 200, `tgkill` 234).
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Monad.v:299` `bind_get_model`. -/
theorem bind_getModel {β : Type} (k : Model → Sys β) (i : SyscallInput) (m : Model)
    (o : Outcome β) : (getModel >>= k) i m o ↔ k m i m o := by
  show Sys.bind getModel k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁
      simpa using h₂
    · intro h
      exact ⟨m, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h
      · cases h₁
        exact h₂
    · intro h
      exact .inr ⟨m, m, [], rfl, h⟩

/-- Reading the input is pure: `input >>= k` is `k` at the input. -/
theorem bind_input {β : Type} (k : SyscallInput → Sys β) (i : SyscallInput) (m : Model)
    (o : Outcome β) : (input >>= k) i m o ↔ k i i m o := by
  show Sys.bind input k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁
      simpa using h₂
    · intro h
      exact ⟨i, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h
      · cases h₁
        exact h₂
    · intro h
      exact .inr ⟨i, m, [], rfl, h⟩

/-! ## `rt_sigaction` (134) -/

/-- LPS `Sys/Kernel/Signal.v:185` `sig32`: the `int sig` argument's low half. -/
def sig32 (sig : Word) : Word := abiLow32 sig

/-- LPS `Sys/Kernel/Signal.v:194` `sigaction_accepted`: SIGINT and SIGTERM, the signals whose
disposition no modeled operation can consult and which the theorem's signal-free environment
never delivers. -/
def sigactionAccepted (sig : Word) : Bool := uns sig == 2 || uns sig == 15

/-- LPS `Sys/Kernel/Signal.v:210` `sig_valid`: `1 <= sig <= _NSIG` (64, also on x86-64). -/
def sigValid (sig : Word) : Bool := decide (1 ≤ uns sig) && decide (uns sig ≤ 64)

/-- LPS `Sys/Kernel/Signal.v:217` `sig_kernel_only`: SIGKILL (9) and SIGSTOP (19), the same
numbers on x86-64. -/
def sigKernelOnly (sig : Word) : Bool := uns sig == 9 || uns sig == 19

/-- LPS `Sys/Kernel/Signal.v:285` `sa_flags_accepted`: `UAPI_SA_FLAGS` (riscv64) minus
`SA_RESTART`: `SA_NOCLDSTOP`, `SA_NOCLDWAIT`, `SA_SIGINFO`, `SA_EXPOSE_TAGBITS`,
`SA_ONSTACK`, `SA_NODEFER`, `SA_RESETHAND`. -/
def saFlagsAccepted : Int := 0xC8000807

/-- The x86-64 accepted flags: LPS's set with `SA_RESTORER` (`0x04000000`) added, a
delivery-only bit of x86-64's `UAPI_SA_FLAGS` (see the module docstring). `SA_RESTART`
stays out. -/
def saFlagsAcceptedX86 : Int := zlor saFlagsAccepted SA_RESTORER_X86

/-- LPS `Sys/Kernel/Signal.v:287` `sa_flags_ok`, over the accepted set: no bit outside it
(`Z.ldiff (bv_unsigned fl) accepted = 0`). -/
def saFlagsOkWith (accepted : Int) (fl : Word) : Bool := fl &&& ~~~(zw accepted) == 0

/-- LPS `Sys/Kernel/Signal.v:287` `sa_flags_ok`. -/
def saFlagsOk (fl : Word) : Bool := saFlagsOkWith saFlagsAccepted fl

/-- The user ABI of `rt_sigaction`'s `act`: the size of the kernel's `struct sigaction`
(copied whole before anything else is decided) and the `sa_flags` bits accepted as no-ops.
The flags word is at `SA_FLAGS_OFF` (8) in both ABIs. -/
structure SigactionAbi where
  structBytes : Int
  flagsAccepted : Int

/-- LPS's (riscv64) ABI: 24 bytes, no `sa_restorer` (`Sys/Kernel/Signal.v:290`). -/
def sigactionAbiLps : SigactionAbi := ⟨kernelSigactionBytes, saFlagsAccepted⟩

/-- x86-64: 32 bytes with `sa_restorer` at 16, `SA_RESTORER` accepted. -/
def sigactionAbiX86 : SigactionAbi := ⟨kernelSigactionBytesX86, saFlagsAcceptedX86⟩

/-- x86-64 with `SA_RESTORER` declined like any bit outside LPS's accepted set (not wired; it
declines every libc `sigaction`). -/
def sigactionAbiX86Strict : SigactionAbi := ⟨kernelSigactionBytesX86, saFlagsAccepted⟩

/-- LPS `Sys/Kernel/Signal.v:344` `sigaction_flags`, over the struct size: the flags word when
the whole struct is readable. -/
def sigactionFlagsWith (structBytes : Int) (mp : Word → Option Byte) (act : Word) :
    Option Word :=
  if (readableBytes mp act (zw structBytes)).length == structBytes.toNat then
    readU64 mp (act + zw SA_FLAGS_OFF)
  else none

/-- LPS `Sys/Kernel/Signal.v:344` `sigaction_flags` (24 bytes). -/
def sigactionFlags (mp : Word → Option Byte) (act : Word) : Option Word :=
  sigactionFlagsWith kernelSigactionBytes mp act

/-- LPS `Sys/Kernel/Signal.v:410` `rt_sigaction_spec`, over the `struct sigaction` ABI. -/
def rtSigactionSpecWith (abi : SigactionAbi) (sig act oact ss : Word) : Sys SyscallEffect :=
  if ss != zw 8 then errRet EINVAL
  else if !wIs0 oact then unmodeled
  else if wIs0 act then (if sigValid sig then retOnly 0 else errRet EINVAL)
  else do
    let i ← input
    match sigactionFlagsWith abi.structBytes i.mem act with
    | none => errRet EFAULT
    | some fl =>
      if !sigValid sig then errRet EINVAL
      else if sigKernelOnly sig then errRet EINVAL
      else if !saFlagsOkWith abi.flagsAccepted fl then unmodeled
      else if sigactionAccepted sig then retOnly 0
      else unmodeled

/-- LPS `Sys/Kernel/Signal.v:410` `rt_sigaction_spec`. -/
def rtSigactionSpec (sig act oact ss : Word) : Sys SyscallEffect :=
  rtSigactionSpecWith sigactionAbiLps sig act oact ss

/-- x86-64 `rt_sigaction` (13): the 32-byte `struct sigaction`, `SA_RESTORER` accepted. -/
def rtSigactionSpecX86 (sig act oact ss : Word) : Sys SyscallEffect :=
  rtSigactionSpecWith sigactionAbiX86 sig act oact ss

/-! ## `rt_sigprocmask` (135) -/

/-- LPS `Sys/Kernel/Signal.v:703` `how_valid`. -/
def howValid (how : Word) : Bool :=
  uns how == SIG_BLOCK || uns how == SIG_UNBLOCK || uns how == SIG_SETMASK

/-- LPS `Sys/Kernel/Signal.v:738` `sigset_at`: the 8-byte `sigset_t`, all or nothing. -/
def sigsetAt (mp : Word → Option Byte) (p : Word) : Option Word :=
  (readBytesMap mp p (zw NSIG_BYTES)).map leBytesToWord

/-- LPS `Sys/Uapi.v:808` `sig_kernel_only_mask`: SIGKILL and SIGSTOP, `(1 << 8) | (1 << 18)`
(`Run.sigKernelOnlyMask` is the same mask as a word). -/
def sigKernelOnlyMaskZ : Int := 262400

/-- LPS `Sys/Kernel/Signal.v:832` `sigmask_strip`: `sigdelsetmask` of SIGKILL and SIGSTOP. -/
def sigmaskStrip (w : Word) : Word := w &&& ~~~(zw sigKernelOnlyMaskZ)

/-- LPS `Sys/Kernel/Signal.v:842` `sigmask_apply`: `SIG_BLOCK` ors, `SIG_UNBLOCK` clears,
`SIG_SETMASK` (and the unreachable default) replaces. -/
def sigmaskApply (how old new : Word) : Word :=
  if uns how == SIG_BLOCK then old ||| new
  else if uns how == SIG_UNBLOCK then old &&& ~~~new
  else new

/-- LPS `Sys/Kernel/Signal.v:858` `mask_launchable`: SIGKILL and SIGSTOP are clear. -/
def MaskLaunchable (w : Word) : Prop := w &&& zw sigKernelOnlyMaskZ = 0

/-- LPS `Sys/Kernel/Signal.v:861` `sigmask_strip_launchable`. -/
theorem sigmaskStrip_launchable (w : Word) : MaskLaunchable (sigmaskStrip w) := by
  unfold MaskLaunchable sigmaskStrip
  ext i hi
  simp

/-- LPS `Sys/Kernel/Signal.v:871` `sigmask_apply_launchable`. -/
theorem sigmaskApply_launchable (how old new : Word) (hold : MaskLaunchable old)
    (hnew : MaskLaunchable new) : MaskLaunchable (sigmaskApply how old new) := by
  unfold MaskLaunchable at hold hnew ⊢
  have ho : ∀ i (hi : i < 64), (old[i] && (zw sigKernelOnlyMaskZ)[i]) = false := fun i hi => by
    simpa using congrArg (fun x : Word => x[i]'hi) hold
  have hn : ∀ i (hi : i < 64), (new[i] && (zw sigKernelOnlyMaskZ)[i]) = false := fun i hi => by
    simpa using congrArg (fun x : Word => x[i]'hi) hnew
  unfold sigmaskApply
  split
  · ext i hi
    have h1 := ho i hi
    have h2 := hn i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    revert h1 h2
    cases old[i] <;> cases new[i] <;> cases (zw sigKernelOnlyMaskZ)[i] <;> simp
  · split
    · ext i hi
      have h1 := ho i hi
      simp only [BitVec.getElem_and, BitVec.getElem_not]
      revert h1
      cases old[i] <;> cases new[i] <;> cases (zw sigKernelOnlyMaskZ)[i] <;> simp
    · exact hnew

/-- LPS `Sys/Kernel/Signal.v:937` `write_oset`, over the `access_ok` gate: the entry mask goes
to `oset` last; `-EFAULT` outside `access_ok`, `unmodeled` when the destination is only partly
writable (a partial copy-out is user-visible state). -/
def writeOsetWith (gate : AccessGate) (oset old : Word) : Sys SyscallEffect :=
  gate oset NSIG_BYTES do
    let i ← input
    match readBytesMap i.wmem oset (zw NSIG_BYTES) with
    | some _ => Sys.pure (mkEffect 0 [(oset, zToLeBytes NSIG_BYTES.toNat (uns old))] [])
    | none => unmodeled

/-- LPS `Sys/Kernel/Signal.v:937` `write_oset`. -/
def writeOset (oset old : Word) : Sys SyscallEffect := writeOsetWith accessGateLps oset old

/-- LPS `Sys/Kernel/Signal.v:996` `sigabrt_blocked`. -/
def sigabrtBlocked (mask : Word) : Bool := !wIs0 (mask &&& zw sigabrtMask)

/-- LPS `Sys/Kernel/Signal.v:1005` `sigmask_deliver_model`: install the mask, and die by
SIGABRT when a pending SIGABRT is now unblocked (musl's `raise` restoring its mask). -/
def sigmaskDeliverModel (new : Word) (m : Model) : Model :=
  if m.sigabrtPending && !sigabrtBlocked new then (m.withSigmask new).withKilled (zw SIGABRT)
  else m.withSigmask new

/-- LPS `Sys/Kernel/Signal.v:1010` `set_sigmask_deliver`. -/
def setSigmaskDeliver (new : Word) : Sys Unit := modify (sigmaskDeliverModel new)

/-- LPS `Sys/Kernel/Signal.v:1018` `sigmask_deliver_model_no_pending`. -/
theorem sigmaskDeliverModel_no_pending (new : Word) (m : Model) (hp : m.sigabrtPending = false) :
    sigmaskDeliverModel new m = m.withSigmask new := by
  simp [sigmaskDeliverModel, hp]

/-- LPS `Sys/Kernel/Signal.v:1030` `m_sigmask_sigmask_deliver_model`. -/
theorem sigmask_sigmaskDeliverModel (new : Word) (m : Model) :
    (sigmaskDeliverModel new m).sigmask = new := by
  unfold sigmaskDeliverModel
  split <;> rfl

/-- LPS `Sys/Kernel/Signal.v:1038` `m_vmmaps_sigmask_deliver_model`. -/
theorem vmmaps_sigmaskDeliverModel (new : Word) (m : Model) :
    (sigmaskDeliverModel new m).vmmaps = m.vmmaps := by
  unfold sigmaskDeliverModel
  split <;> rfl

/-- LPS `Sys/Kernel/Signal.v:1046` `set_sigmask_deliver_no_pending`. -/
theorem setSigmaskDeliver_no_pending (new : Word) (i : SyscallInput) (m : Model)
    (o : Outcome Unit) (hp : m.sigabrtPending = false) :
    setSigmaskDeliver new i m o ↔ setSigmask new i m o := by
  unfold setSigmaskDeliver setSigmask
  rw [show modify (sigmaskDeliverModel new) i m o = (o = .ok () (sigmaskDeliverModel new m) [])
    from rfl, sigmaskDeliverModel_no_pending new m hp]
  rfl

/-- LPS `Sys/Kernel/Signal.v:1054` `rt_sigprocmask_spec`, over the `access_ok` gate of the
`oset` copy-out. -/
def rtSigprocmaskSpecWith (gate : AccessGate) (how nset oset ss : Word) : Sys SyscallEffect :=
  if ss != zw NSIG_BYTES then errRet EINVAL
  else do
    let m ← getModel
    let old := m.sigmask
    if wIs0 nset then
      (if wIs0 oset then retOnly 0 else writeOsetWith gate oset old)
    else do
      let i ← input
      match sigsetAt i.mem nset with
      | none => errRet EFAULT
      | some raw =>
        recordCopyins [(nset, NSIG_BYTES.toNat)]
          (if !howValid how then errRet EINVAL
           else do
             setSigmaskDeliver (sigmaskApply how old (sigmaskStrip raw))
             if wIs0 oset then retOnly 0 else writeOsetWith gate oset old)

/-- LPS `Sys/Kernel/Signal.v:1054` `rt_sigprocmask_spec`. -/
def rtSigprocmaskSpec (how nset oset ss : Word) : Sys SyscallEffect :=
  rtSigprocmaskSpecWith accessGateLps how nset oset ss

/-- x86-64 `rt_sigprocmask` (14): the `oset` copy-out is a `copy_to_user`
(`kernel/signal.c:3218-3220` in v6.8), out of line on x86-64, so its `access_ok` checks the
whole range (`accessGateX86`). The band answer (`-EFAULT`, nothing written) is that of kernels
with `USER_PTR_MAX = TASK_SIZE_MAX` (the native table's profile, v6.13 and later); v6.8's
sign-test `access_ok` passes the band and copies partially before `-EFAULT`
(`Sys/AccessGate.lean`). -/
def rtSigprocmaskSpecX86 (how nset oset ss : Word) : Sys SyscallEffect :=
  rtSigprocmaskSpecWith accessGateX86 how nset oset ss

/-- The former, conservative x86-64 reading: the `oset` copy-out behind the base-only small
constant-size `access_ok`, which declines the band below `TASK_SIZE_MAX`. It restricts
`rtSigprocmaskSpecX86` (`NativeX86.GapSweep.rtSigprocmask_restricts`). -/
def rtSigprocmaskSpecX86Small (how nset oset ss : Word) : Sys SyscallEffect :=
  rtSigprocmaskSpecWith accessGateSmallX86 how nset oset ss

/-! ## `sigaltstack` (132) -/

/-- LPS `Sys/Kernel/Signal.v:1211` `ss_sp_of`. -/
def ssSpOf (bs : List Byte) : Word := leBytesToWord (bs.take 8)
/-- LPS `Sys/Kernel/Signal.v:1213` `ss_flags_of`: the `int ss_flags` at 8. -/
def ssFlagsOf (bs : List Byte) : Word := leBytesToWord ((bs.drop SS_FLAGS_OFF.toNat).take 4)
/-- LPS `Sys/Kernel/Signal.v:1215` `ss_size_of`. -/
def ssSizeOf (bs : List Byte) : Word := leBytesToWord (bs.drop SS_SIZE_OFF.toNat)

/-- LPS `Sys/Kernel/Signal.v:1220` `ss_mode`: `ss_flags & ~SS_FLAG_BITS`. -/
def ssMode (fl : Word) : Int := uns (fl &&& ~~~(zw SS_AUTODISARM))

/-- LPS `Sys/Kernel/Signal.v:1228` `ss_mode_ok`: 0, `SS_ONSTACK` or `SS_DISABLE`. -/
def ssModeOk (fl : Word) : Bool :=
  ssMode fl == 0 || ssMode fl == SS_ONSTACK || ssMode fl == SS_DISABLE

/-- LPS `Sys/Kernel/Signal.v:1232` `ss_disabling`. -/
def ssDisabling (fl : Word) : Bool := ssMode fl == SS_DISABLE

/-- LPS `Sys/Kernel/Signal.v:1243` `sigaltstack_at`: the 24-byte `stack_t` (the same layout on
x86-64), all or nothing. -/
def sigaltstackAt (mp : Word → Option Byte) (uss : Word) : Option (List Byte) :=
  readBytesMap mp uss (zw SIGALTSTACK_BYTES)

/-- LPS `Sys/Kernel/Signal.v:1288` `sigaltstack_spec`, over `sigaltstack_size_valid`, the
architecture's second lower bound on `ss_size` (applied after `MINSIGSTKSZ`, both `-ENOMEM`).
LPS's premise (riscv64 vector state off) makes it true for every size above
`MINSIGSTKSZ`. -/
def sigaltstackSpecWith (sizeValid : Word → Bool) (uss uoss : Word) : Sys SyscallEffect := do
  let m ← getModel
  if m.sigaltstackInstalled then unmodeled
  else if !wIs0 uoss then unmodeled
  else if wIs0 uss then retOnly 0
  else do
    let i ← input
    match sigaltstackAt i.mem uss with
    | none => errRet EFAULT
    | some bs =>
      let fl := ssFlagsOf bs
      if !ssModeOk fl then errRet EINVAL
      else if ssDisabling fl then retOnly 0
      else if wIs0 (ssSpOf bs) && wIs0 (ssSizeOf bs) then unmodeled
      else if decide (uns (ssSizeOf bs) < MINSIGSTKSZ) then errRet ENOMEM
      else if !sizeValid (ssSizeOf bs) then errRet ENOMEM
      else do
        setSigaltstackInstalled
        retOnly 0

/-- LPS `Sys/Kernel/Signal.v:1288` `sigaltstack_spec`. -/
def sigaltstackSpec (uss uoss : Word) : Sys SyscallEffect :=
  sigaltstackSpecWith (fun _ => true) uss uoss

/-- x86-64 `sigaltstack` (131) on a kernel without `strict_sigaltstack_size` and a process
without a dynamic xfeature permission: x86-64's `sigaltstack_size_valid` is then true, and the
arm is LPS's. -/
def sigaltstackSpecX86 (uss uoss : Word) : Sys SyscallEffect := sigaltstackSpec uss uoss

/-- x86-64 `sigaltstack` on a `strict_sigaltstack_size` kernel whose signal frame is `fsize`
bytes: `sigaltstack_size_valid` is `ss_size > fsize`. Not wired: `fsize` depends on the CPU's
xstate size. -/
def sigaltstackSpecX86Strict (fsize : Int) (uss uoss : Word) : Sys SyscallEffect :=
  sigaltstackSpecWith (fun sz => decide (fsize < uns sz)) uss uoss

/-! ## `tkill` (130) and `tgkill` (131) -/

/-- LPS `Sys/Kernel/Signal.v:1426` `pid_positive`: 1..2^31-1 after the `pid_t` narrowing. -/
def pidPositive (p : Word) : Bool := decide (1 ≤ uns p) && decide (uns p < 2 ^ 31)

/-- LPS `Sys/Kernel/Signal.v:1436` `tkill_sig_valid`: `valid_signal`, `sig <= 64`; 0 passes. -/
def tkillSigValid (sig : Word) : Bool := decide (uns sig ≤ 64)

/-- LPS `Sys/Kernel/Signal.v:1450` `send_sigabrt`: blocked, SIGABRT is pending; unblocked,
the process is killed by it (a death by signal, not an exit). -/
def sendSigabrt : Sys SyscallEffect := do
  let m ← getModel
  if sigabrtBlocked m.sigmask then setSigabrtPending else setKilled (zw SIGABRT)
  retOnly 0

/-- LPS `Sys/Kernel/Signal.v:1460` `tkill_self`. -/
def tkillSelf (pid sig : Word) : Sys SyscallEffect := do
  let m ← getModel
  if !m.abortTerminal then unmodeled
  else
    match m.tid with
    | none => unmodeled
    | some t =>
      if pid != t then unmodeled
      else if !tkillSigValid sig then errRet EINVAL
      else if sig == zw SIGABRT then sendSigabrt
      else unmodeled

/-- LPS `Sys/Kernel/Signal.v:1473` `tkill_spec`. -/
def tkillSpec (pid sig : Word) : Sys SyscallEffect := do
  let m ← getModel
  if !m.abortTerminal then unmodeled
  else if !pidPositive pid then errRet EINVAL
  else tkillSelf pid sig

/-- LPS `Sys/Kernel/Signal.v:1479` `tgkill_spec`. -/
def tgkillSpec (tgid pid sig : Word) : Sys SyscallEffect := do
  let m ← getModel
  if !m.abortTerminal then unmodeled
  else if !(pidPositive pid && pidPositive tgid) then errRet EINVAL
  else
    match m.tid with
    | none => unmodeled
    | some t =>
      if pid != t then unmodeled
      else if tgid != t then errRet ESRCH
      else tkillSelf pid sig

/-- LPS `Sys/Kernel/Signal.v:1499` `tkill_spec_off_unmodeled`: with `abort()` not declared
terminal, `tkill` only declines. -/
theorem tkillSpec_off_unmodeled (pid sig : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (hoff : m.abortTerminal = false) (h : tkillSpec pid sig i m o) :
    o = .unmodeled := by
  unfold tkillSpec at h
  rw [bind_getModel] at h
  simp only [hoff, Bool.not_false, ite_true] at h
  exact h

/-- LPS `Sys/Kernel/Signal.v:1506` `tgkill_spec_off_unmodeled`. -/
theorem tgkillSpec_off_unmodeled (tgid pid sig : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (hoff : m.abortTerminal = false)
    (h : tgkillSpec tgid pid sig i m o) : o = .unmodeled := by
  unfold tgkillSpec at h
  rw [bind_getModel] at h
  simp only [hoff, Bool.not_false, ite_true] at h
  exact h

/-! ## Table arms -/

/-- LPS `Sys/SyscallTable.v:83-87`: the signal arms at their asm-generic numbers. -/
def signalLpsArms : List SpecArm :=
  [ arm 130 "tkill" fun i => tkillSpec (pid32 (i.arg 0)) (sig32 (i.arg 1)),
    arm 131 "tgkill" fun i => tgkillSpec (pid32 (i.arg 0)) (pid32 (i.arg 1)) (sig32 (i.arg 2)),
    arm 132 "sigaltstack" fun i => sigaltstackSpec (i.arg 0) (i.arg 1),
    arm 134 "rt_sigaction" fun i =>
      rtSigactionSpec (sig32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3),
    arm 135 "rt_sigprocmask" fun i =>
      rtSigprocmaskSpec (how32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) ]

/-- The signal arms at their native x86-64 numbers (`syscall_64.tbl`), with the x86-64
`struct sigaction` and `access_ok` variants. -/
def signalX86Arms : List SpecArm :=
  [ arm 200 "tkill" fun i => tkillSpec (pid32 (i.arg 0)) (sig32 (i.arg 1)),
    arm 234 "tgkill" fun i => tgkillSpec (pid32 (i.arg 0)) (pid32 (i.arg 1)) (sig32 (i.arg 2)),
    arm 131 "sigaltstack" fun i => sigaltstackSpecX86 (i.arg 0) (i.arg 1),
    arm 13 "rt_sigaction" fun i =>
      rtSigactionSpecX86 (sig32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3),
    arm 14 "rt_sigprocmask" fun i =>
      rtSigprocmaskSpecX86 (how32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) ]

end Silmaril.Process.LPS
