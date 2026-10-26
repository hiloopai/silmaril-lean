module

public import Silmaril.Process.LPS.Probes.KitReturns
public import Silmaril.Process.LPS.Probes.Data.WriteClosed
public import Silmaril.Process.LPS.Probes.Data.WriteClosed2

/-! # Probe `write_closed` and its mutant `write_closed2`

`write_closed.s` is `close(1); write(1, "hello\n", 6); exit(0 - rax)`. On Linux
the harness recorded `close(1) = 0`, `write(1, 0x4000a9, 6) = -9` (`-EBADF`), no
output and `exit(9)` (`Data.WriteClosed.observed`).

* `WriteClosed.determined`: every execution without refusals does exactly this.
  `close_spec` removes descriptor 1 from the table, and `write_spec` of a
  descriptor that is not in the table is `-EBADF`. `sound` covers every finite
  execution under any refusal filter; `no_error`: nothing errors or is unmodeled.
* `WriteClosed.admits`: the recorded raw calls are a run of the model.

The mutant `write_closed2.s` closes descriptor 2 instead. The write then reaches
the stdout channel: Linux prints `hello\n` and the probe exits with
`0 - 6 = 250` (`Data.WriteClosed2.observed`). The model admits that run, so the
original's universal claim is false for the mutant
(`WriteClosed2.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace WriteClosed

open Data.WriteClosed

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution without refusals: `close(1) = 0`, `-EBADF`, exit status 9. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
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
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end WriteClosed

namespace WriteClosed2

open Data.WriteClosed2

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Linux's run of the mutant: `close(2) = 0`, the full write of `hello\n`,
then exit 250. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
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
    probe_write 169 6 with observed.stdout
    probe_instr 154 5 (.movI32 .rdi 0)
    probe_instr 159 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 162 5 (.movI32 .rax 60)
    probe_trap 167
    probe_exit (0 - 6)
  all_goals probe_side

/-- Mutation: the original's universal claim (`-EBADF`, exit 9) is false for the
mutant, which may write `hello\n` and exit 250. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.WriteClosed.observed :=
  Probe.not_determined_of_admits _ admits fun _ _ same => by
    simp [Observed.events, Observed.terminal, observed, Data.WriteClosed.observed] at same

end WriteClosed2

end Silmaril.Process.LPS.Probes
