module

public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Exit
public import Silmaril.Process.LPS.Probes.WriteHelloSplit

/-! # `write_hello_split` at every native launch

`write_hello_split.s` writes the six bytes of `write_hello` in two calls,
`write(1, "hel", 3); write(1, "lo\n", 3); exit(0)`, ignoring both return values. Each call
is a channel write, which the hub may cut short (`Probe.WritePrefix`): every execution
writes a nonempty prefix of `hel`, then a nonempty prefix of `lo\n`, then exits 0
(`writeHelloSplit_exec`, at every native launch, by the kit's rules replayed at the
symbolic launch).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-- The outcomes of two channel writes of `first` and `second`, then `exit(0)`. -/
def TwoWritesThenExit (first second : List Byte) : Omni.Post x86ExtNative := fun trace outcome =>
  ∃ d₁ d₂ final, outcome = .halt final ∧ Probe.WritePrefix first d₁ ∧ Probe.WritePrefix second d₂ ∧
    trace = d₁.map (.writeEv 1) ++ (d₂.map (.writeEv 1) ++ [.exitEv 0 final.model.fs]) ∧
    final.model.halted = some 0 ∧ final.model.killedBy = none

/-- `hel` -/
def hel : List Byte := [0x68, 0x65, 0x6c]

/-- `lo\n` -/
def loNl : List Byte := [0x6c, 0x6f, 0x0a]

theorem writeHelloSplit_first : (Data.WriteHelloSplit.probe.bytes.drop 176).take 3 = hel := by
  decide +kernel

theorem writeHelloSplit_second : (Data.WriteHelloSplit.probe.bytes.drop 179).take 3 = loNl := by
  decide +kernel

theorem writeHelloSplit_exec (en : ExecEntry) (inp : ProcInput)
    (launch : NativeLaunch Data.WriteHelloSplit.probe en inp) :
    Omni.Exec Data.WriteHelloSplit.probe.segs spec noFilter
      (Data.WriteHelloSplit.probe.launchedAt en inp).initial (TwoWritesThenExit hel loNl) := by
  have := Probe.checked_launchedAt (P := Data.WriteHelloSplit.probe) launch.entry launch.input
  show Omni.Exec (Data.WriteHelloSplit.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x4000b0)
  probe_instr 135 5 (.movI32 .rdx 3)
  probe_trap 140
  probe_write 176 3
  intro d₁ first
  probe_instr 142 5 (.movI32 .rax 1)
  probe_instr 147 5 (.movI32 .rdi 1)
  probe_instr 152 5 (.movI32 .rsi 0x4000b3)
  probe_instr 157 5 (.movI32 .rdx 3)
  probe_trap 162
  probe_write 179 3
  intro d₂ second
  probe_instr 164 5 (.movI32 .rax 60)
  probe_instr 169 5 (.movI32 .rdi 0)
  probe_trap 174
  probe_exit 0
  rw [Probe.launchedAt_bytes, writeHelloSplit_first] at first
  rw [Probe.launchedAt_bytes, writeHelloSplit_second] at second
  exact ⟨d₁, d₂, _, rfl, first, second, rfl, rfl, rfl⟩

theorem TwoWritesThenExit.exitsIn {first second : List Byte} (trace : List Event)
    (outcome : Omni.Outcome x86ExtNative) (post : TwoWritesThenExit first second trace outcome) :
    Omni.ExitsIn [0] trace outcome := by
  obtain ⟨_, _, final, rfl, _, _, _, halted, unkilled⟩ := post
  exact ⟨0, halted, List.mem_singleton_self _, unkilled⟩

/-- Two channel writes print a prefix of each piece in turn. -/
theorem TwoWritesThenExit.pieces {first second : List Byte} (trace : List Event)
    (outcome : Omni.Outcome x86ExtNative) (post : TwoWritesThenExit first second trace outcome) :
    (TraceSpec.stdoutPieces [first, second]).denote trace := by
  obtain ⟨d₁, d₂, final, _, ⟨_, p₁⟩, ⟨_, p₂⟩, rfl, _⟩ := post
  refine ⟨⟨[d₁, d₂], .cons p₁ (.cons p₂ .nil), ?_⟩, ?_⟩
  · rw [written_writes, written_writes]
    simp [written]
  · rw [writesOtherThan_writes, writesOtherThan_writes]
    rfl

end Silmaril.Process.LPS.Problems.X86Probes
