module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.ArchPrctl

/-! # The `arch_prctl` probes at every native launch

`arch_fs` sets the FS base to the image start and exits with the byte at `%fs:0` (the ELF
magic `0x7f`); `arch_fs1` sets it one byte further (`0x45`); `arch_getfs_exit` sets it and
exits 3 before its `ARCH_GET_FS`. The FS base, the image and the exit status do not depend on
the launch. `arch_getfs_exit` passes the entry stack pointer in RSI to its `exit`, which the
hub's boundary guard checks: at every native launch it is below `TASK_SIZE_MAX`
(`NativeLaunch.sp_below`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem archFs_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ArchFs.probe en inp) :
    Omni.Exec Data.ArchFs.probe.segs spec noFilter (Data.ArchFs.probe.launchedAt en inp).initial
      (Emits Data.ArchFs.observed) := by
  have := Probe.checked_launchedAt (P := Data.ArchFs.probe) launch.entry launch.input
  show Omni.Exec (Data.ArchFs.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400000)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  apply Probe.exec_instr _ (off := 137) (len := 9)
    (instruction := .load .q .rdi (Silmaril.X86.Ext.Mem.fsAt 0))
    (exec := Probe.exec_loadFs _ _ .rdi 9 0 rfl (by rw [Probe.launchedAt_size]; decide)
      (by rw [Probe.launchedAt_size]; decide)) <;> probe_sides
  probe_instr 146 5 (.movI32 .rax 60)
  probe_trap 151
  probe_exit 0x00010102464c457f
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem archFs1_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ArchFs1.probe en inp) :
    Omni.Exec Data.ArchFs1.probe.segs spec noFilter (Data.ArchFs1.probe.launchedAt en inp).initial
      (Emits Data.ArchFs1.observed) := by
  have := Probe.checked_launchedAt (P := Data.ArchFs1.probe) launch.entry launch.input
  show Omni.Exec (Data.ArchFs1.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400001)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  apply Probe.exec_instr _ (off := 137) (len := 9)
    (instruction := .load .q .rdi (Silmaril.X86.Ext.Mem.fsAt 0))
    (exec := Probe.exec_loadFs _ _ .rdi 9 1 rfl (by rw [Probe.launchedAt_size]; decide)
      (by rw [Probe.launchedAt_size]; decide)) <;> probe_sides
  probe_instr 146 5 (.movI32 .rax 60)
  probe_trap 151
  probe_exit 0x0000010102464c45
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem archGetfsExit_exec (en : ExecEntry) (inp : ProcInput)
    (launch : NativeLaunch Data.ArchGetfsExit.probe en inp) :
    Omni.Exec Data.ArchGetfsExit.probe.segs spec noFilter (Data.ArchGetfsExit.probe.launchedAt en inp).initial
      (Emits Data.ArchGetfsExit.observed) := by
  have := Probe.checked_launchedAt (P := Data.ArchGetfsExit.probe) launch.entry launch.input
  have below := launch.sp_below
  show Omni.Exec (Data.ArchGetfsExit.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400078)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  probe_instr 137 5 (.movI32 .rax 60)
  probe_instr 142 5 (.movI32 .rdi 0x1003)
  -- `mov %rsp, %rsi` copies the symbolic stack pointer: its side conditions by evaluation.
  apply Probe.exec_instr _ (off := 147) (len := 3) (instruction := .mov .q (.reg .rsi) .rsp)
  case exec => rfl
  case rip => rfl
  case running => rfl
  case lazy => rfl
  case fits => probe_side
  case two => probe_side
  case notSyscall => probe_side
  case decoded => probe_side
  probe_trap 150
  probe_exit 0x1003
  exact ⟨_, rfl, rfl, rfl, rfl⟩
  all_goals assumption

end Silmaril.Process.LPS.Problems.X86Probes
