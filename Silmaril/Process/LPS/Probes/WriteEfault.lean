module

public import Silmaril.Process.LPS.Probes.KitReturns
public import Silmaril.Process.LPS.Probes.Data.WriteEfault
public import Silmaril.Process.LPS.Probes.Data.WriteEfaultOk

/-! # Probe `write_efault` and its mutant `write_efault_ok`

`write_efault.s` is `write(1, 0x10, 6)` followed by `exit(0 - rax)`, so the
errno of the write becomes the exit status. Address `0x10` is unmapped. On Linux
the harness recorded `write(1, 0x10, 6) = -14` (`-EFAULT`), no output, then
`exit(14)` (`Data.WriteEfault.observed`).

* `WriteEfault.determined`: every execution of the actual bytes without
  refusals does exactly this. The reference `write_spec` channel branch finds
  no readable byte at the buffer (`write_source` is empty) and answers
  `-EFAULT`, which is deterministic: the channel's short-write choice is never
  reached. `sound` covers every finite execution under any refusal filter, and
  `no_error` says no execution errors or is unmodeled.
* `WriteEfault.admits`: the recorded raw calls are a run of the model.

The mutant `write_efault_ok.s` passes the message address instead of `0x10`.
Linux then writes `hello\n`, the call returns 6 and the probe exits with
`0 - 6 = 250` (`Data.WriteEfaultOk.observed`). The model admits that run, so
the original's universal claim is false for the mutant
(`WriteEfaultOk.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace WriteEfault

open Data.WriteEfault

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution without refusals: `-EFAULT`, then exit status 14. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
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
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Every finite execution under any refusal filter. -/
theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    Probe.Exactly observed trace outcome :=
  Omni.Exec.sound_any determined finite

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
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
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end WriteEfault

namespace WriteEfaultOk

open Data.WriteEfaultOk

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Linux's run of the mutant: the full write of `hello\n`, then exit 250. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 1)
    probe_instr 125 5 (.movI32 .rdi 1)
    probe_instr 130 5 (.movI32 .rsi 0x40009d)
    probe_instr 135 5 (.movI32 .rdx 6)
    probe_trap 140
    probe_write 157 6 with observed.stdout
    probe_instr 142 5 (.movI32 .rdi 0)
    probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 150 5 (.movI32 .rax 60)
    probe_trap 155
    probe_exit (0 - 6)
  all_goals probe_side

/-- Mutation: the original's universal claim (`-EFAULT`, exit 14) is false for
the mutant, which may write `hello\n` and exit 250. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.WriteEfault.observed :=
  Probe.not_determined_of_admits _ admits fun _ _ same => by
    simp [Observed.events, Observed.terminal, observed, Data.WriteEfault.observed] at same

end WriteEfaultOk

end Silmaril.Process.LPS.Probes
