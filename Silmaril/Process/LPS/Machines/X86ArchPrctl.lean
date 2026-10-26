module

public import Silmaril.Process.LPS.NativeX86
public import Silmaril.Process.LPS.Machines.X86

/-! # Native x86 FS-base syscall bridge

Linux v6.12 `arch/x86/kernel/process_64.c:898-923` checks `arg2 >=
TASK_SIZE_MAX` and returns `-EPERM` for `ARCH_SET_FS`. This adapter fixes
four-level addressing (`0x7ffffffff000`), as does `x86ExtNative`; it does not
model five-level kernels, FS selectors, GS, GET_FS, or other arch_prctl operations.
Unsupported operations are explicitly unmodeled. The machine side samples RSI
before applying effects and changes FS only for a successful native call.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86

def archSetFs : Word := 0x1002

def archPrctlSpec (operation base : Word) : Sys SyscallEffect :=
  if operation = archSetFs then
    if uns base < x86AddressSpace.taskSize then retOnly 0 else errRet EPERM
  else Sys.unmodeled

def archPrctlArm : SpecArm :=
  arm 158 "arch_prctl" (fun input => archPrctlSpec (input.arg 0) (input.arg 1))

def extendedTable : List SpecArm := archPrctlArm :: table specTable

def extendedSyscallSpec : Sys SyscallEffect := dispatch extendedTable

/-- Reference arms use the reference refusal families. The architecture-only
FS-base operation has no injected-failure alternative in this model. -/
def defaultRefusalFilter (cfg : SpuriousCfg) : RefusalFilter :=
  refusalFilter Silmaril.Process.LPS.syscallSpec cfg

theorem extended_numbers_nodup : (armNumbers extendedTable).Nodup := by decide

theorem archPrctl_dispatch (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (number : input.sysno = 158) :
    extendedSyscallSpec input model outcome ↔
      archPrctlSpec (input.arg 0) (input.arg 1) input model outcome := by
  simp [extendedSyscallSpec, extendedTable, dispatch, lookupArm, archPrctlArm, arm, number]

theorem archPrctl_success (base : Word) (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (valid : uns base < x86AddressSpace.taskSize) :
    archPrctlSpec archSetFs base input model outcome ↔
      outcome = .ok (mkEffect 0 [] []) model [] := by
  simp [archPrctlSpec, valid, retOnly, Sys.pure]

theorem archPrctl_high (base : Word) (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (invalid : ¬ uns base < x86AddressSpace.taskSize) :
    archPrctlSpec archSetFs base input model outcome ↔
      outcome = .ok (mkEffect (errnoRet EPERM) [] []) model [] := by
  simp [archPrctlSpec, invalid, errRet, retOnly, Sys.pure]

theorem archPrctl_unsupported (operation base : Word) (input : SyscallInput)
    (model : Model) (outcome : Outcome SyscallEffect) (other : operation ≠ archSetFs) :
    archPrctlSpec operation base input model outcome ↔ outcome = .unmodeled := by
  simp [archPrctlSpec, other, Sys.unmodeled]

section

-- Consume the abstract success rule instead of reducing the symbolic syscall
-- relation while elaborating and linting the bridge's proof arguments.
attribute [local irreducible] archPrctlSpec

/-- The declared syscall success and the architectural side effect connect.
This is a bridge for a single call; no machine/memory simulation is assumed. -/
theorem successful_setFs (state : Machines.X86State) (base : Word)
    (input : SyscallInput) (model nextModel : Model) (effect : SyscallEffect)
    (events : List Event) (pending : state.pending = some 158)
    (operation : state.m.core.read .rdi = archSetFs)
    (argument : state.m.core.read .rsi = base)
    (valid : uns base < x86AddressSpace.taskSize)
    (success : archPrctlSpec archSetFs base input model (.ok effect nextModel events)) :
    (Machines.x86ApplyEffectNative state effect).m.core.fsBase = base := by
  have equal := (archPrctl_success base input model (.ok effect nextModel events) valid).mp success
  have sameEffect : effect = mkEffect 0 [] [] := (Outcome.ok.inj equal).1
  have ret : effect.ret = 0 := congrArg SyscallEffect.ret sameEffect
  exact (Machines.x86ApplyEffectNative_setFs state effect pending operation ret).trans argument

end

theorem failed_setFs_preserves (state : Machines.X86State) :
    (Machines.x86ApplyEffectNative state (mkEffect (errnoRet EPERM) [] [])).m.core.fsBase =
      state.m.core.fsBase := by
  apply Machines.x86ApplyEffectNative_preservesFs
  simp [mkEffect, errnoRet, EPERM, zw]

theorem archPrctl_not_spuriously_refused (cfg : SpuriousCfg) (input : SyscallInput)
    (model : Model) (effect : SyscallEffect) (number : input.sysno = 158) :
    ¬ defaultRefusalFilter cfg input model effect := by
  simp [defaultRefusalFilter, refusalFilter, referenceInput, number, byNative, numbers]

/-- Nonempty success domain, including the null base used to clear FS. -/
theorem zero_base_valid : uns (0 : Word) < x86AddressSpace.taskSize := by decide

theorem last_base_valid : uns (0x7fffffffefff : Word) < x86AddressSpace.taskSize := by decide

theorem boundary_base_invalid : ¬ uns (0x7ffffffff000 : Word) < x86AddressSpace.taskSize := by decide

theorem getFs_unsupported : (0x1003 : Word) ≠ archSetFs := by decide

end Silmaril.Process.LPS.NativeX86
