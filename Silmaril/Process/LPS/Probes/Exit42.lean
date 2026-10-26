module

public import Silmaril.Process.LPS.Probes.Data.Exit42
public import Silmaril.Process.LPS.Probes.Data.Exit43

/-! # Probe `exit42` and its mutant `exit43`

`exit42.s` is `mov $60,%eax; mov $42,%edi; syscall`: native `exit(42)`. On Linux
the harness recorded one raw syscall `exit(0x2a)` and exit status 42
(`Data.Exit42.observed`, generated from `probes/exit42.json`).

* `Exit42.admits`: the LPS model admits that run of the actual bytes, with the
  same raw syscall and the same status, under any refusal filter.
* `Exit42.determined`: every maximal execution under any refusal filter halts
  with exactly that exit event and status 42. Nothing else can happen: no
  execution errors, is unmodeled (`no_error`, `no_unmodeled`), and there is no
  nondeterministic alternative, since `exit` has a single outcome.

The mutant `exit43.s` changes the status immediate to 43. Linux exits with 43
(`Data.Exit43.observed`), the model admits that run (`Exit43.admits`), and the
`exit42` property is false of the mutant (`Exit43.not_determined_42`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace Exit42

open Data.Exit42

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The universal statement: every execution halts with exactly the observed
exit event and status, under every refusal filter. -/
theorem determined (refused : RefusalFilter) : probe.Determined refused observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 60)
  probe_instr 125 5 (.movI32 .rdi 42)
  probe_trap 130
  probe_exit 42
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Reality is admitted: the recorded raw syscall and outcome form a run. -/
theorem admits (refused : RefusalFilter) : probe.Admits refused observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 60)
    probe_instr 125 5 (.movI32 .rdi 42)
    probe_trap 130
    probe_exit 42
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ (determined noFilter)

theorem no_unmodeled (refused : RefusalFilter) : ¬ (probe.behavior refused).unmodeled :=
  Probe.Determined.no_unmodeled _ (determined noFilter)

end Exit42

namespace Exit43

open Data.Exit43

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The mutant's own observation (status 43) is admitted. -/
theorem admits (refused : RefusalFilter) : probe.Admits refused observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 60)
    probe_instr 125 5 (.movI32 .rdi 43)
    probe_trap 130
    probe_exit 43
  all_goals probe_side

/-- Mutation: the `exit42` property is false of the mutant. -/
theorem not_determined_42 (refused : RefusalFilter) : ¬ probe.Determined refused Data.Exit42.observed :=
  Probe.not_determined_of_admits _ (admits refused) (by
    intro fs fs' same
    simp [Observed.events, Observed.terminal, observed, Data.Exit42.observed] at same)

end Exit43

end Silmaril.Process.LPS.Probes
