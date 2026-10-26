module

public import Silmaril.Process.LPS.Probes.Data.WriteHelloSplit
public import Silmaril.Process.LPS.Probes.Launches

/-! # Probe `write_hello_split`

`write_hello_split.s` writes the six bytes of `write_hello` in two calls,
`write(1, "hel", 3); write(1, "lo\n", 3); exit(0)`, ignoring both return values. On Linux
the harness recorded `write(1, 0x4000b0, 3) = 3`, `write(1, 0x4000b3, 3) = 3`, stdout
`hello\n` and exit status 0 (`Data.WriteHelloSplit.observed`).

* `WriteHelloSplit.admits`: the model admits that run (both writes in full).
* `WriteHelloSplit.admits_short`: it also admits a run whose first write is cut short to
  `h` (the reference short write of a channel), so the probe prints `hlo\n`. This is the
  run that separates the probe from `write_hello`, whose every output is a prefix of
  `hello\n` (`Problems.X86Probes.Pairs`).

Every execution at every native launch is in `Problems.X86Probes.writeHelloSplit_exec`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes.WriteHelloSplit

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch Data.WriteHelloSplit

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Reality is admitted: both writes in full, then `exit(0)`. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 1)
    probe_instr 125 5 (.movI32 .rdi 1)
    probe_instr 130 5 (.movI32 .rsi 0x4000b0)
    probe_instr 135 5 (.movI32 .rdx 3)
    probe_trap 140
    probe_write 176 3 with [104, 101, 108]
    probe_instr 142 5 (.movI32 .rax 1)
    probe_instr 147 5 (.movI32 .rdi 1)
    probe_instr 152 5 (.movI32 .rsi 0x4000b3)
    probe_instr 157 5 (.movI32 .rdx 3)
    probe_trap 162
    probe_write 179 3 with [108, 111, 10]
    probe_instr 164 5 (.movI32 .rax 60)
    probe_instr 169 5 (.movI32 .rdi 0)
    probe_trap 174
    probe_exit 0
  all_goals probe_side

/-- The short-write run, at any allocation limit: the first write delivers only `h`, the
second all of `lo\n`. -/
theorem admits_short (lim : Int) : ∃ calls fs final,
    Run probe.segs spec noFilter (probe.initialAt lim) calls
      ([104].map (.writeEv 1) ++ ([108, 111, 10].map (.writeEv 1) ++ [.exitEv 0 fs]))
      (.halt final) := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  rw [Probe.initialAt_eq]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x4000b0)
  probe_instr 135 5 (.movI32 .rdx 3)
  probe_trap 140
  probe_write 176 3 with [104]
  probe_instr 142 5 (.movI32 .rax 1)
  probe_instr 147 5 (.movI32 .rdi 1)
  probe_instr 152 5 (.movI32 .rsi 0x4000b3)
  probe_instr 157 5 (.movI32 .rdx 3)
  probe_trap 162
  probe_write 179 3 with [108, 111, 10]
  probe_instr 164 5 (.movI32 .rax 60)
  probe_instr 169 5 (.movI32 .rdi 0)
  probe_trap 174
  probe_exit 0

end Silmaril.Process.LPS.Probes.WriteHelloSplit
