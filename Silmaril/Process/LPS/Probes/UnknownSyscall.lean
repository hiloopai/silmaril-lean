module

public import Silmaril.Process.LPS.Probes.KitMisc
public import Silmaril.Process.LPS.Probes.Data.UnknownSyscall
public import Silmaril.Process.LPS.Probes.Data.UnknownExitGroup

/-! # Probe `unknown_syscall` and its mutant `unknown_exit_group`

`unknown_syscall.s` is `mov $999,%eax; syscall; mov %rax,%rdi; mov $60,%eax;
syscall`: call number 999, which no x86-64 kernel implements, then exit with its
return value. On Linux the harness recorded `syscall_0x3e7(0, 0, 0, 0, 0, 0) =
-1 ENOSYS` and exit status 218, that is -38 modulo 256
(`Data.UnknownSyscall.observed`).

This is the key example of a reference-faithful gap. The LPS dispatcher (LPS
`Sys/Dispatch.v:53` `dispatch`, here `Silmaril.Process.LPS.dispatch`) sends a number
outside its table to `unmodeled`: the model *fails closed* rather than guess a
result. The theorems state exactly what the model does instead of returning
`-ENOSYS`:

* `UnknownSyscall.unmodeled_at_call`: under every refusal filter, every execution
  of the actual bytes stops, with no event, at the first `syscall`, in an error
  configuration where call 999 is pending and unmodeled;
* `UnknownSyscall.unmodeled`: the launched behaviour is `unmodeled` (so no
  safety claim about this program can be derived from the model);
* `UnknownSyscall.not_admits`: Linux's observation (return -ENOSYS, exit 218) is
  not admitted;
* `UnknownSyscall.linux_enosys`: the observation, from the JSON, is that Linux
  returned -38.

The mutant `unknown_exit_group.s` changes the number immediate to 231
(`exit_group`). RDI is 0 at entry, so Linux exits with status 0. The model admits
that run, every execution exits 0 exactly (`UnknownExitGroup.determined`), and the
original's fail-closed property is false of the mutant
(`UnknownExitGroup.not_stops`). `exit_group` has the specification of `exit`
(`Probe.native_exit_group_iff_exit`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace UnknownSyscall

open Data.UnknownSyscall

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The model's actual behaviour, under every refusal filter: every execution
stops at the first call, 999, which is unmodeled. -/
theorem unmodeled_at_call (refused : RefusalFilter) :
    Omni.Exec probe.segs spec refused probe.initial (probe.StopsUnmodeled 999) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 999)
  probe_trap 125
  exact Probe.exec_stops rfl (fun outcome => Probe.native_unknown_iff _ _ outcome rfl)

theorem unmodeled (refused : RefusalFilter) : (probe.behavior refused).unmodeled :=
  Probe.unmodeled_of_stops (unmodeled_at_call refused)

/-- Linux's run (return -ENOSYS, exit 218) is not a run of the model. -/
theorem not_admits (refused : RefusalFilter) : ¬ probe.Admits refused observed :=
  Probe.not_admits_of_stops (unmodeled_at_call refused)

/-- No reading of the environment rescues the program: under every refusal
filter the behaviour reaches the fail-closed error, and Linux's run is not
admitted. -/
theorem any_filter (refused : RefusalFilter) :
    (probe.behavior refused).unmodeled ∧ (probe.behavior refused).errors ∧
      ¬ probe.Admits refused observed :=
  ⟨unmodeled refused, Probe.unmodeled_reachesError (unmodeled refused), not_admits refused⟩

/-- What Linux did instead, from the fixture: call 999 returned -38 (`-ENOSYS`)
and the probe exited with that value's low byte. -/
theorem linux_enosys :
    observed.syscalls.head? = some ⟨999, [0, 0, 0, 0, 0, 0], some (-38)⟩ ∧
      observed.outcome = .exited ((2 ^ 64 - 38) % 256) := by
  decide

end UnknownSyscall

namespace UnknownExitGroup

open Data.UnknownExitGroup

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- Every execution under every refusal filter is `exit_group(0)`. -/
theorem determined (refused : RefusalFilter) : probe.Determined refused observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 231)
  probe_trap 125
  apply Probe.exec_exitH (Or.inr rfl) (status := 0) rfl rfl (by decide +kernel)
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem admits (refused : RefusalFilter) : probe.Admits refused observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 231)
    probe_trap 125
    exact Probe.run_exitH (Or.inr rfl) (status := 0) rfl rfl (by decide +kernel)
  all_goals probe_side

theorem not_unmodeled (refused : RefusalFilter) : ¬ (probe.behavior refused).unmodeled :=
  Probe.Determined.no_unmodeled _ (determined noFilter)

/-- Mutation: the original's fail-closed property is false of the mutant. -/
theorem not_stops (refused : RefusalFilter) :
    ¬ Omni.Exec probe.segs spec refused probe.initial (probe.StopsUnmodeled 999) :=
  Probe.not_stops_of_admits (admits refused)

/-- `exit_group` and `exit` have the same LPS specification. -/
theorem exit_group_iff_exit (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect) :
    spec { input with sysno := 231 } model outcome ↔ spec { input with sysno := 60 } model outcome :=
  Probe.native_exit_group_iff_exit input model outcome

end UnknownExitGroup

end Silmaril.Process.LPS.Probes
