module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.WriteZero
public import Silmaril.Process.LPS.Probes.WriteClosed
public import Silmaril.Process.LPS.Probes.WriteEfault
public import Silmaril.Process.LPS.Probes.CloseTwice
public import Silmaril.Process.LPS.Probes.ReadBadfd
public import Silmaril.Process.LPS.Probes.UnknownSyscall

/-! # The descriptor and errno probes at every native launch

The kit's proof scripts (`Probes.WriteZero`, `Probes.WriteClosed`, `Probes.WriteEfault`,
`Probes.CloseTwice`, `Probes.ReadBadfd`, `Probes.UnknownSyscall`) replayed at the symbolic
launch `probe.launchedAt en inp`. None of these probes reads the stack, the auxiliary vector,
a file or stdin: they touch only descriptors 0, 1 and 2, which every launch opens as the three
channels (`initModel`), an unmapped address below the image (`0x10`), and the image itself.

The postcondition is `Emits observed`: the recorded events and status, at the launch's own
file system. The mutants whose run writes a channel (`write_zero1`, `write_closed2`,
`write_efault_ok`) have the short-write alternatives of the hub's `write` as well
(`WroteThenExit`): each nonempty prefix of the message, then the status computed from its
length.

`unknown_syscall` is not lifted: its call 999 is unmodeled, so at its own launch it reaches
an error (`UnknownSyscall.any_filter`), which refutes every halting shape.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem writeZero_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.WriteZero.probe en inp) :
    Omni.Exec Data.WriteZero.probe.segs spec noFilter (Data.WriteZero.probe.launchedAt en inp).initial
      (Emits Data.WriteZero.observed) := by
  have := Probe.checked_launchedAt (P := Data.WriteZero.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteZero.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x400098)
  probe_instr 135 5 (.movI32 .rdx 0)
  probe_trap 140
  probe_ret write_zero_iff
  probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 145 5 (.movI32 .rax 60)
  probe_trap 150
  probe_exit 0
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem writeClosed_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.WriteClosed.probe en inp) :
    Omni.Exec Data.WriteClosed.probe.segs spec noFilter (Data.WriteClosed.probe.launchedAt en inp).initial
      (Emits Data.WriteClosed.observed) := by
  have := Probe.checked_launchedAt (P := Data.WriteClosed.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteClosed.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 3)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_trap 130
  probe_ret close_ok_iff
  probe_instr 132 5 (.movI32 .rax 1)
  probe_instr 137 5 (.movI32 .rdi 1)
  probe_instr 142 5 (.movI32 .rsi 0x4000a9)
  probe_instr 147 5 (.movI32 .rdx 6)
  probe_trap 152
  probe_ret write_badf_iff
  probe_instr 154 5 (.movI32 .rdi 0)
  probe_instr 159 3 (.alu .q .sub (.reg .rdi) .rax)
  probe_instr 162 5 (.movI32 .rax 60)
  probe_trap 167
  probe_exit 9
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem writeEfault_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.WriteEfault.probe en inp) :
    Omni.Exec Data.WriteEfault.probe.segs spec noFilter (Data.WriteEfault.probe.launchedAt en inp).initial
      (Emits Data.WriteEfault.observed) := by
  have := Probe.checked_launchedAt (P := Data.WriteEfault.probe) launch.entry launch.input
  have valid := launch.entry
  show Omni.Exec (Data.WriteEfault.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x10)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  probe_ret write_efault_iff
  probe_instr 142 5 (.movI32 .rdi 0)
  probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
  probe_instr 150 5 (.movI32 .rax 60)
  probe_trap 155
  probe_exit 14
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem closeTwice_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.CloseTwice.probe en inp) :
    Omni.Exec Data.CloseTwice.probe.segs spec noFilter (Data.CloseTwice.probe.launchedAt en inp).initial
      (Emits Data.CloseTwice.observed) := by
  have := Probe.checked_launchedAt (P := Data.CloseTwice.probe) launch.entry launch.input
  show Omni.Exec (Data.CloseTwice.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 3)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_trap 130
  probe_ret close_ok_iff
  probe_instr 132 5 (.movI32 .rax 3)
  probe_instr 137 5 (.movI32 .rdi 0)
  probe_trap 142
  probe_ret close_badf_iff
  probe_instr 144 5 (.movI32 .rdi 0)
  probe_instr 149 3 (.alu .q .sub (.reg .rdi) .rax)
  probe_instr 152 5 (.movI32 .rax 60)
  probe_trap 157
  probe_exit 9
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem closeTwice1_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.CloseTwice1.probe en inp) :
    Omni.Exec Data.CloseTwice1.probe.segs spec noFilter (Data.CloseTwice1.probe.launchedAt en inp).initial
      (Emits Data.CloseTwice1.observed) := by
  have := Probe.checked_launchedAt (P := Data.CloseTwice1.probe) launch.entry launch.input
  show Omni.Exec (Data.CloseTwice1.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 3)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_trap 130
  probe_ret close_ok_iff
  probe_instr 132 5 (.movI32 .rax 3)
  probe_instr 137 5 (.movI32 .rdi 1)
  probe_trap 142
  probe_ret close_ok_iff
  probe_instr 144 5 (.movI32 .rdi 0)
  probe_instr 149 3 (.alu .q .sub (.reg .rdi) .rax)
  probe_instr 152 5 (.movI32 .rax 60)
  probe_trap 157
  probe_exit 0
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem readBadfd_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadBadfd.probe en inp) :
    Omni.Exec Data.ReadBadfd.probe.segs spec noFilter (Data.ReadBadfd.probe.launchedAt en inp).initial
      (Emits Data.ReadBadfd.observed) := by
  have := Probe.checked_launchedAt (P := Data.ReadBadfd.probe) launch.entry launch.input
  show Omni.Exec (Data.ReadBadfd.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 99)
  probe_instr 130 5 (.movI32 .rsi 0x40009d)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  probe_ret read_badf_iff
  probe_instr 142 5 (.movI32 .rdi 0)
  probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
  probe_instr 150 5 (.movI32 .rax 60)
  probe_trap 155
  probe_exit 9
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- `exit_group(rdi)` with RDI as the launch leaves it: zero at every launch. -/
theorem unknownExitGroup_exec (en : ExecEntry) (inp : ProcInput)
    (launch : NativeLaunch Data.UnknownExitGroup.probe en inp) :
    Omni.Exec Data.UnknownExitGroup.probe.segs spec noFilter
      (Data.UnknownExitGroup.probe.launchedAt en inp).initial (Emits Data.UnknownExitGroup.observed) := by
  have := Probe.checked_launchedAt (P := Data.UnknownExitGroup.probe) launch.entry launch.input
  show Omni.Exec (Data.UnknownExitGroup.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 231)
  probe_trap 125
  apply Probe.exec_exitH (Or.inr rfl) (status := 0) rfl rfl (by probe_side)
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## Mutants that write a channel -/

theorem writeZero1_message :
    (Data.WriteZero1.probe.bytes.drop 152).take 1 = Data.WriteZero1.observed.stdout := by
  decide +kernel

theorem writeZero1_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.WriteZero1.probe en inp) :
    Omni.Exec Data.WriteZero1.probe.segs spec noFilter (Data.WriteZero1.probe.launchedAt en inp).initial
      (WroteThenExit Data.WriteZero1.observed.stdout countStatus) := by
  have := Probe.checked_launchedAt (P := Data.WriteZero1.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteZero1.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x400098)
  probe_instr 135 5 (.movI32 .rdx 1)
  probe_trap 140
  probe_write 152 1
  intro ds delivered
  rw [Probe.launchedAt_bytes, writeZero1_message] at delivered
  have cases : ds ∈ [[104]] :=
    writePrefix_mem_tail delivered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl
  · probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 145 5 (.movI32 .rax 60)
    probe_trap 150
    probe_exit _
    exact ⟨_, _, rfl, delivered, rfl, rfl, rfl⟩

theorem writeClosed2_message :
    (Data.WriteClosed2.probe.bytes.drop 169).take 6 = Data.WriteClosed2.observed.stdout := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem writeClosed2_exec (en : ExecEntry) (inp : ProcInput)
    (launch : NativeLaunch Data.WriteClosed2.probe en inp) :
    Omni.Exec Data.WriteClosed2.probe.segs spec noFilter (Data.WriteClosed2.probe.launchedAt en inp).initial
      (WroteThenExit Data.WriteClosed2.observed.stdout negStatus) := by
  have := Probe.checked_launchedAt (P := Data.WriteClosed2.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteClosed2.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 3)
  probe_instr 125 5 (.movI32 .rdi 2)
  probe_trap 130
  probe_ret close_ok_iff
  probe_instr 132 5 (.movI32 .rax 1)
  probe_instr 137 5 (.movI32 .rdi 1)
  probe_instr 142 5 (.movI32 .rsi 0x4000a9)
  probe_instr 147 5 (.movI32 .rdx 6)
  probe_trap 152
  probe_write 169 6
  intro ds delivered
  rw [Probe.launchedAt_bytes, writeClosed2_message] at delivered
  have cases : ds ∈ [[104], [104, 101], [104, 101, 108], [104, 101, 108, 108], [104, 101, 108, 108, 111],
      [104, 101, 108, 108, 111, 10]] :=
    writePrefix_mem_tail delivered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · probe_instr 154 5 (.movI32 .rdi 0)
    probe_instr 159 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 162 5 (.movI32 .rax 60)
    probe_trap 167
    probe_exit _
    exact ⟨_, _, rfl, delivered, rfl, rfl, rfl⟩

theorem writeEfaultOk_message :
    (Data.WriteEfaultOk.probe.bytes.drop 157).take 6 = Data.WriteEfaultOk.observed.stdout := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem writeEfaultOk_exec (en : ExecEntry) (inp : ProcInput)
    (launch : NativeLaunch Data.WriteEfaultOk.probe en inp) :
    Omni.Exec Data.WriteEfaultOk.probe.segs spec noFilter (Data.WriteEfaultOk.probe.launchedAt en inp).initial
      (WroteThenExit Data.WriteEfaultOk.observed.stdout negStatus) := by
  have := Probe.checked_launchedAt (P := Data.WriteEfaultOk.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteEfaultOk.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x40009d)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  probe_write 157 6
  intro ds delivered
  rw [Probe.launchedAt_bytes, writeEfaultOk_message] at delivered
  have cases : ds ∈ [[104], [104, 101], [104, 101, 108], [104, 101, 108, 108], [104, 101, 108, 108, 111],
      [104, 101, 108, 108, 111, 10]] :=
    writePrefix_mem_tail delivered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · probe_instr 142 5 (.movI32 .rdi 0)
    probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 150 5 (.movI32 .rax 60)
    probe_trap 155
    probe_exit _
    exact ⟨_, _, rfl, delivered, rfl, rfl, rfl⟩

/-! ## `unknown_syscall` -/

/-- `unknown_syscall` reaches an error at its own launch. -/
theorem unknownSyscall_errors :
    ReachesError Data.UnknownSyscall.probe.segs spec noFilter
      (Data.UnknownSyscall.probe.launchedAt Data.UnknownSyscall.probe.entry
        Data.UnknownSyscall.probe.input).initial :=
  (UnknownSyscall.any_filter noFilter).2.1

end Silmaril.Process.LPS.Problems.X86Probes
