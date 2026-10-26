module

public import Silmaril.Process.LPS.Probes.KitReturns
public import Silmaril.Process.LPS.Probes.Data.WriteZero
public import Silmaril.Process.LPS.Probes.Data.WriteZero1

/-! # Probe `write_zero` and its mutant `write_zero1`

`write_zero.s` is `write(1, "hello\n", 0); exit(rax)`. On Linux the harness
recorded `write(1, 0x400098, 0) = 0`, no output and `exit(0)`
(`Data.WriteZero.observed`).

* `WriteZero.determined`: every execution without refusals does exactly this.
  `write_spec` of a channel with count 0 checks that the empty range is
  accessible (`access_ok_zero`) and returns 0 without emitting events; the
  short-write choice is never reached. `sound` covers every finite execution
  under any refusal filter; `no_error`: nothing errors or is unmodeled.
* `WriteZero.admits`: the recorded raw calls are a run of the model.

The mutant `write_zero1.s` passes length 1. Linux writes `h`, the call returns 1
and the probe exits 1 (`Data.WriteZero1.observed`). The model admits that run,
so the original's universal claim is false for the mutant
(`WriteZero1.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace WriteZero

open Data.WriteZero

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution without refusals: the empty write returns 0, exit status 0. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
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
    probe_instr 130 5 (.movI32 .rsi 0x400098)
    probe_instr 135 5 (.movI32 .rdx 0)
    probe_trap 140
    probe_ret write_zero_iff
    probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 145 5 (.movI32 .rax 60)
    probe_trap 150
    probe_exit 0
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end WriteZero

namespace WriteZero1

open Data.WriteZero1

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Linux's run of the mutant: the write of `h` returns 1, exit 1. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 1)
    probe_instr 125 5 (.movI32 .rdi 1)
    probe_instr 130 5 (.movI32 .rsi 0x400098)
    probe_instr 135 5 (.movI32 .rdx 1)
    probe_trap 140
    probe_write 152 1 with observed.stdout
    probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 145 5 (.movI32 .rax 60)
    probe_trap 150
    probe_exit 1
  all_goals probe_side

/-- Mutation: the original's universal claim (no output, exit 0) is false for
the mutant, which may write `h` and exit 1. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.WriteZero.observed :=
  Probe.not_determined_of_admits _ admits fun _ _ same => by
    simp [Observed.events, Observed.terminal, observed, Data.WriteZero.observed] at same

end WriteZero1

end Silmaril.Process.LPS.Probes
