module

public import Silmaril.Process.LPS.Machines.X86LaunchControls
public import Silmaril.Process.LPS.RunHelpers

/-! # Executing the nonempty native x86 launch control

A complete finite execution of the checked ELF fixture through MOV, SUB,
SYSCALL trapping, and the native exit arm. The initialized stack memory remains
symbolic throughout. This is an existence-of-execution theorem for the actual
LPS transition relation, not a claim about a separate arithmetic toy machine.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Silmaril.Process.LPS.Machines.X86Launch.Controls

open Silmaril.X86

/-- The actual launch configuration, with its initialized code and stack. -/
def initial : Config x86ExtNative := init x86ExtNative snapshot entry sourceAllocLimit input

/-- Symbolic register effect of the first instruction. -/
def movExitNumber (state : X86State) : X86State :=
  ⟨⟨{ state.m.core.write .rax 60 with rip := state.m.core.rip + 5 }, state.m.memory⟩, none⟩

/-- Symbolic effect of SUB-zeroing: unlike XOR-zeroing, every status flag is defined. -/
def zeroExitStatus (state : X86State) : X86State :=
  ⟨⟨{ state.m.core.write .rdi 0 with
        rip := state.m.core.rip + 2
        flags := Silmaril.X86.Ext.subFlagsN
          (Silmaril.X86.Ext.Sz.d.read state.m.core .rdi)
          (Silmaril.X86.Ext.Sz.d.read state.m.core .rdi) }, state.m.memory⟩, none⟩

def moved : Config x86ExtNative := ⟨movExitNumber initial.ms, initial.model⟩
def zeroed : Config x86ExtNative := ⟨zeroExitStatus moved.ms, initial.model⟩
def trapped : Config x86ExtNative :=
  ⟨{ zeroed.ms with pending := some 60 }, initial.model⟩
def exited : Config x86ExtNative := ⟨trapped.ms, initial.model.withHalted 0⟩

theorem mov_execution (state : X86State) :
    x86ExecResult [(state.m.core.rip, 5)]
      (Silmaril.X86.Ext.exec (.movI32 .rax 60) state.m.core state.m.memory 5) =
    .ok ⟨movExitNumber state, [(state.m.core.rip, 5)]⟩ := by
  rfl

theorem sub_execution (state : X86State) :
    x86ExecResult [(state.m.core.rip, 2)]
      (Silmaril.X86.Ext.exec (.alu .d .sub (.reg .rdi) .rdi)
        state.m.core state.m.memory 2) =
    .ok ⟨zeroExitStatus state, [(state.m.core.rip, 2)]⟩ := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write,
    zeroExitStatus, x86ExecResult]
  change (state.m.core.write .rdi (((state.m.core.read .rdi).setWidth 32 -
    (state.m.core.read .rdi).setWidth 32).setWidth 64)).regs =
    (state.m.core.write .rdi 0).regs
  rw [BitVec.sub_self]
  rfl

/-- A genuine precision boundary of the current adapter, retained as a
negative control: XOR leaves AF undefined, so no concrete RFLAGS image exists. -/
theorem xor_zeroing_flags_refused :
    rflagsImage (Silmaril.X86.Ext.logicFlagsN (0#32)) = none := by decide +kernel

theorem mov_prefix_fetched :
    initial.ms.m.memory.fetchBytes initial.ms.m.core.rip.toNat 2 = some [0xb8, 0x3c] :=
  Process.Memory.readWith_sub_range loaded_code_fetched
    (offset := 0) (len := 2) (by decide) (by decide)

theorem mov_machine_step : x86NativeStep initial.ms =
    .ok ⟨moved.ms, [(initial.ms.m.core.rip, 5)]⟩ := by
  have notSyscall : initial.ms.m.memory.fetchBytes initial.ms.m.core.rip.toNat 2 ≠
      some [0x0f, 0x05] := by
    rw [mov_prefix_fetched]
    decide +kernel
  rw [x86NativeStep_of_fetch initial.ms notSyscall loaded_entry_instruction_fetched
    (by decide +kernel : Ext.decode [0xb8, 0x3c, 0, 0, 0] = some (.movI32 .rax 60, 5))]
  exact mov_execution initial.ms

theorem sub_fetched : moved.ms.m.memory.fetchBytes moved.ms.m.core.rip.toNat 2 =
    some [0x29, 0xff] :=
  Process.Memory.readWith_sub_range loaded_code_fetched
    (offset := 5) (len := 2) (by decide) (by decide)

theorem sub_machine_step : x86NativeStep moved.ms =
    .ok ⟨zeroed.ms, [(moved.ms.m.core.rip, 2)]⟩ := by
  have notSyscall : moved.ms.m.memory.fetchBytes moved.ms.m.core.rip.toNat 2 ≠
      some [0x0f, 0x05] := by
    rw [sub_fetched]
    decide +kernel
  rw [x86NativeStep_of_fetch moved.ms notSyscall sub_fetched
    (by decide +kernel : Ext.decode [0x29, 0xff] = some (.alu .d .sub (.reg .rdi) .rdi, 2))]
  exact sub_execution moved.ms

theorem syscall_fetched : zeroed.ms.m.memory.fetchBytes zeroed.ms.m.core.rip.toNat 2 =
    some [0x0f, 0x05] :=
  Process.Memory.readWith_sub_range loaded_code_fetched
    (offset := 7) (len := 2) (by decide) (by decide)

theorem syscall_machine_step : x86NativeStep zeroed.ms =
    .ok ⟨trapped.ms, [(zeroed.ms.m.core.rip, 2)]⟩ := by
  exact x86NativeStep_syscall zeroed.ms syscall_fetched rfl

theorem mov_process_step (refused : RefusalFilter) :
    SStep image.segments NativeX86.extendedSyscallSpec refused initial [] (.next moved) := by
  apply SStep.instr rfl rfl
  exact Progress.accountStep_of_noLazy initial.ms moved.ms initial.model _ rfl mov_machine_step

theorem sub_process_step (refused : RefusalFilter) :
    SStep image.segments NativeX86.extendedSyscallSpec refused moved [] (.next zeroed) := by
  apply SStep.instr rfl rfl
  exact Progress.accountStep_of_noLazy moved.ms zeroed.ms initial.model _ rfl sub_machine_step

theorem syscall_process_step (refused : RefusalFilter) :
    SStep image.segments NativeX86.extendedSyscallSpec refused zeroed [] (.next trapped) := by
  apply SStep.instr rfl rfl
  exact Progress.accountStep_of_noLazy zeroed.ms trapped.ms initial.model _ rfl syscall_machine_step

theorem native_exit_zero (syscallInput : SyscallInput) (model : Model)
    (number : syscallInput.sysno = 60) (status : syscallInput.arg 0 = 0) :
    NativeX86.extendedSyscallSpec syscallInput model
      (.ok (mkEffect 0 [] []) (model.withHalted 0) []) := by
  have dispatch : NativeX86.extendedSyscallSpec syscallInput model
      (.ok (mkEffect 0 [] []) (model.withHalted 0) []) ↔
      exitSpec (syscallInput.arg 0) (NativeX86.referenceInputFor ⟨93, 60, "exit"⟩ syscallInput)
        model (.ok (mkEffect 0 [] []) (model.withHalted 0) []) := by
    simp only [NativeX86.extendedSyscallSpec, NativeX86.extendedTable, dispatch, number]
    rfl
  rw [dispatch, status]
  exact ⟨(), model.withHalted 0, [], [], rfl, rfl, rfl⟩

theorem exit_process_step (refused : RefusalFilter) :
    SStep image.segments NativeX86.extendedSyscallSpec refused trapped
      [.exitEv 0 initial.model.fs] (.next exited) := by
  exact SStep.exit rfl rfl (native_exit_zero _ initial.model rfl rfl) rfl rfl

/-- Four actual process transitions from the validated ELF's initialized
configuration to normal exit zero, under any syscall-refusal filter. -/
theorem initialized_exit_path (refused : RefusalFilter) :
    Star image.segments NativeX86.extendedSyscallSpec refused initial
      [.exitEv 0 initial.model.fs] exited :=
  .step (mov_process_step refused) (.step (sub_process_step refused)
    (.step (syscall_process_step refused) (.step (exit_process_step refused) (.refl exited))))

theorem initialized_finite_exit (refused : RefusalFilter) :
    Omni.FiniteExec image.segments NativeX86.extendedSyscallSpec refused initial
      [.exitEv 0 initial.model.fs] (.halt exited) :=
  Omni.star_finiteExec (initialized_exit_path refused) (.halt (by decide))

theorem initialized_normal_exit : exited.model.halted = some 0 ∧ exited.model.killedBy = none :=
  ⟨rfl, rfl⟩

/-- The actual native launch's observable trace includes the exit event. -/
theorem native_launch_exit_trace (refused : RefusalFilter) :
    (runWith x86ExtNative NativeX86.extendedSyscallSpec refused snapshot
      sourceAllocLimit entry input).traces [.exitEv 0 input.fs] :=
  ⟨[.exitEv 0 initial.model.fs], exited, initialized_exit_path refused, ⟨[], rfl⟩⟩

/-- A concrete successful execution refutes the universal all-error claim.
This is not by itself a proof that every execution avoids errors. -/
theorem native_launch_not_all_errors (refused : RefusalFilter) :
    ¬ (runWith x86ExtNative NativeX86.extendedSyscallSpec refused snapshot
      sourceAllocLimit entry input).allErrors :=
  Progress.halting_path_not_allTracesError (initialized_exit_path refused) (by decide)

end Silmaril.Process.LPS.Machines.X86Launch.Controls
