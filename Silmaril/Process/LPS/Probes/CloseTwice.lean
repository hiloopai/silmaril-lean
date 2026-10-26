module

public import Silmaril.Process.LPS.Probes.KitReturns
public import Silmaril.Process.LPS.Probes.Data.CloseTwice
public import Silmaril.Process.LPS.Probes.Data.CloseTwice1

/-! # Probe `close_twice` and its mutant `close_twice1`

`close_twice.s` is `close(0); close(0); exit(0 - rax)`. On Linux the harness
recorded `close(0) = 0`, `close(0) = -9` (`-EBADF`) and `exit(9)`
(`Data.CloseTwice.observed`).

* `CloseTwice.determined`: every execution without refusals does exactly this.
  The first `close_spec` finds descriptor 0 and removes it; the second finds
  nothing and answers `-EBADF`. `sound` covers every finite execution under any
  refusal filter; `no_error`: nothing errors or is unmodeled.
* `CloseTwice.admits`: the recorded raw calls are a run of the model.

The mutant `close_twice1.s` closes descriptor 1 the second time. Both closes
succeed and the probe exits 0 (`Data.CloseTwice1.observed`). The model admits
that run, so the original's universal claim is false for the mutant
(`CloseTwice1.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace CloseTwice

open Data.CloseTwice

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution without refusals: `close(0) = 0`, `close(0) = -EBADF`, exit 9. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
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
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end CloseTwice

namespace CloseTwice1

open Data.CloseTwice1

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Linux's run of the mutant: `close(0) = 0`, `close(1) = 0`, exit 0. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
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
  all_goals probe_side

/-- Mutation: the original's universal claim (exit 9) is false for the mutant,
which exits 0. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.CloseTwice.observed :=
  Probe.not_determined_of_admits _ admits fun _ _ same => by
    simp [Observed.events, Observed.terminal, observed, Data.CloseTwice.observed] at same

end CloseTwice1

end Silmaril.Process.LPS.Probes
