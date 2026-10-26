module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.Exit42
public import Silmaril.Process.LPS.Probes.WriteHello

/-! # `exit42`, `exit43`, `write_hello`, `write_hello5` at every native launch

The kit's proof scripts of `Probes.Exit42` and `Probes.WriteHello`, replayed at the symbolic
launch `probe.launchedAt en inp` (`Probes.Probe.checked_launchedAt`): none of these probes
reads the stack, the auxiliary vector, a file or stdin, and the only model state they touch
is the descriptor table entry of stdout, which every launch has.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem exit42_exec (en : ExecEntry) (inp : ProcInput) (lim : Int) (launch : NativeLaunch Data.Exit42.probe en inp) :
    Omni.Exec Data.Exit42.probe.segs spec noFilter ((Data.Exit42.probe.launchedAt en inp).initialAt lim)
      (ExitOnly 42) := by
  have := Probe.checked_launchedAt (P := Data.Exit42.probe) launch.entry launch.input
  show Omni.Exec (Data.Exit42.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initialAt_eq]
  probe_instr 120 5 (.movI32 .rax 60)
  probe_instr 125 5 (.movI32 .rdi 42)
  probe_trap 130
  probe_exit 42
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem exit43_exec (en : ExecEntry) (inp : ProcInput) (lim : Int) (launch : NativeLaunch Data.Exit43.probe en inp) :
    Omni.Exec Data.Exit43.probe.segs spec noFilter ((Data.Exit43.probe.launchedAt en inp).initialAt lim)
      (ExitOnly 43) := by
  have := Probe.checked_launchedAt (P := Data.Exit43.probe) launch.entry launch.input
  show Omni.Exec (Data.Exit43.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initialAt_eq]
  probe_instr 120 5 (.movI32 .rax 60)
  probe_instr 125 5 (.movI32 .rdi 43)
  probe_trap 130
  probe_exit 43
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem writeHello_exec (en : ExecEntry) (inp : ProcInput) (lim : Int)
    (launch : NativeLaunch Data.WriteHello.probe en inp) :
    Omni.Exec Data.WriteHello.probe.segs spec noFilter ((Data.WriteHello.probe.launchedAt en inp).initialAt lim)
      (WriteThenExit Data.WriteHello.observed.stdout) := by
  have := Probe.checked_launchedAt (P := Data.WriteHello.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteHello.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initialAt_eq]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x40009a)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  probe_write 154 6
  intro ds delivered
  probe_instr 142 5 (.movI32 .rax 60)
  probe_instr 147 5 (.movI32 .rdi 0)
  probe_trap 152
  probe_exit 0
  rw [Probe.launchedAt_bytes, WriteHello.message] at delivered
  apply WriteThenExit.intro delivered <;> probe_side

theorem writeHello5_exec (en : ExecEntry) (inp : ProcInput) (lim : Int)
    (launch : NativeLaunch Data.WriteHello5.probe en inp) :
    Omni.Exec Data.WriteHello5.probe.segs spec noFilter ((Data.WriteHello5.probe.launchedAt en inp).initialAt lim)
      (WriteThenExit Data.WriteHello5.observed.stdout) := by
  have := Probe.checked_launchedAt (P := Data.WriteHello5.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteHello5.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initialAt_eq]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x40009a)
  probe_instr 135 5 (.movI32 .rdx 5)
  probe_trap 140
  probe_write 154 5
  intro ds delivered
  probe_instr 142 5 (.movI32 .rax 60)
  probe_instr 147 5 (.movI32 .rdi 0)
  probe_trap 152
  probe_exit 0
  rw [Probe.launchedAt_bytes, WriteHello5.message] at delivered
  apply WriteThenExit.intro delivered <;> probe_side

theorem WriteThenExit.exitsIn {bs : List Byte} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : WriteThenExit bs trace outcome) : Omni.ExitsIn [0] trace outcome := by
  cases post with
  | full halted unkilled => exact ⟨0, halted, List.mem_singleton_self _, unkilled⟩
  | shortWrite _ _ _ halted unkilled => exact ⟨0, halted, List.mem_singleton_self _, unkilled⟩

theorem WriteThenExit.stdoutPrefix {bs : List Byte} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : WriteThenExit bs trace outcome) : (TraceSpec.stdoutPrefix bs).denote trace := by
  cases post with
  | full => exact stdoutPrefix_of (List.prefix_refl _) _ _
  | shortWrite _ pre => exact stdoutPrefix_of pre _ _

theorem WriteThenExit.stdoutNonemptyPrefix {bs : List Byte} (nonempty : bs ≠ []) (trace : List Event)
    (outcome : Omni.Outcome x86ExtNative) (post : WriteThenExit bs trace outcome) :
    (TraceSpec.stdoutNonemptyPrefix bs).denote trace := by
  cases post with
  | full => exact stdoutNonemptyPrefix_of ⟨nonempty, List.prefix_refl _⟩ _ _
  | shortWrite ne pre => exact stdoutNonemptyPrefix_of ⟨ne, pre⟩ _ _

end Silmaril.Process.LPS.Problems.X86Probes
