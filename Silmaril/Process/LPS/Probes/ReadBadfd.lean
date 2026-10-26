module

public import Silmaril.Process.LPS.Probes.KitReturns
public import Silmaril.Process.LPS.Probes.Data.ReadBadfd
public import Silmaril.Process.LPS.Probes.Data.ReadBadfd0

/-! # Probe `read_badfd` and its mutant `read_badfd0`

`read_badfd.s` is `read(99, buffer, 6); exit(0 - rax)`, with the buffer in the
probe's own (writable, `rwx`) image. On Linux the harness recorded
`read(99, 0x40009d, 6) = -9` (`-EBADF`) and `exit(9)` (`Data.ReadBadfd.observed`).

* `ReadBadfd.determined`: every execution without refusals does exactly this:
  `read_spec` of a descriptor that is not in the table is `-EBADF`, before the
  buffer is examined. `sound` covers every finite execution under any refusal
  filter; `no_error`: nothing errors or is unmodeled.
* `ReadBadfd.admits`: the recorded raw calls are a run of the model.

The mutant `read_badfd0.s` reads descriptor 0. The harness's stdin is empty, so
Linux returns 0 (end of file) and the probe exits 0
(`Data.ReadBadfd0.observed`). The model admits that run (`read_spec` of stdin at
end of file), so the original's universal claim is false for the mutant
(`ReadBadfd0.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace ReadBadfd

open Data.ReadBadfd

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution without refusals: `-EBADF`, exit status 9. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
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
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end ReadBadfd

namespace ReadBadfd0

open Data.ReadBadfd0

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Linux's run of the mutant: the read of the empty stdin returns 0, exit 0. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 0)
    probe_instr 125 5 (.movI32 .rdi 0)
    probe_instr 130 5 (.movI32 .rsi 0x40009d)
    probe_instr 135 5 (.movI32 .rdx 6)
    probe_trap 140
    probe_ret read_eof_iff
    probe_instr 142 5 (.movI32 .rdi 0)
    probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 150 5 (.movI32 .rax 60)
    probe_trap 155
    probe_exit 0
  all_goals probe_side

/-- Mutation: the original's universal claim (exit 9) is false for the mutant,
which exits 0. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.ReadBadfd.observed :=
  Probe.not_determined_of_admits _ admits fun _ _ same => by
    simp [Observed.events, Observed.terminal, observed, Data.ReadBadfd.observed] at same

end ReadBadfd0

end Silmaril.Process.LPS.Probes
