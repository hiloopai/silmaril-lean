module

public import Silmaril.Process.LPS.Probes.KitMisc
public import Silmaril.Process.LPS.Probes.Data.ArchFs
public import Silmaril.Process.LPS.Probes.Data.ArchFs1
public import Silmaril.Process.LPS.Probes.Data.ArchGetfs
public import Silmaril.Process.LPS.Probes.Data.ArchGetfsExit

/-! # Probes `arch_fs` and `arch_getfs`, with their mutants

`arch_fs.s` is `arch_prctl(ARCH_SET_FS, 0x400000); mov %fs:0, %rdi; exit`. Linux
recorded `arch_prctl(0x1002, 0x400000) = 0` and exit status 127: the low byte of
`%fs:0` is the first byte of the ELF magic, 0x7f (`Data.ArchFs.observed`).

* `ArchFs.admits`: the native `arch_prctl` bridge (`Machines.X86ArchPrctl`) sets the
  FS base and returns 0, and the FS-relative load reads the image through the
  initialized memory: the recorded run, with its raw syscalls and status, is a run
  of the model;
* `ArchFs.determined`, `ArchFs.sound`: every execution exits 127 (no alternative:
  `ARCH_SET_FS` with a base below `TASK_SIZE` has one outcome).

The mutant `arch_fs1.s` sets the base to 0x400001; Linux exits 69 (0x45, `E`),
the model admits it, and the original's universal claim is false of it
(`ArchFs1.not_determined_original`).

`arch_getfs.s` is `ARCH_SET_FS(0x400078); ARCH_GET_FS(rsp); exit(*(rsp))`. Linux
read 0x400078 back and exited 120. The native adapter models only
`ARCH_SET_FS`: every execution stops at the `ARCH_GET_FS` call, unmodeled
(`ArchGetfs.unmodeled_at_get`), so the recorded run is not admitted
(`ArchGetfs.not_admits`). This is a missing feature of the x86 extension (the
reference has no `arch_prctl`): the syscall specification sees no FS base, so a
read-back needs the machine state in the syscall input.

The mutant `arch_getfs_exit.s` changes the second call to `exit(0x1003)`: Linux
exits 3, the model admits it, and every execution exits 3, so the original's
fail-closed property is false of it (`ArchGetfsExit.not_stops`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace ArchFs

open Data.ArchFs

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400000)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  apply Probe.exec_instr _ (off := 137) (len := 9)
    (instruction := .load .q .rdi (Silmaril.X86.Ext.Mem.fsAt 0))
    (exec := Probe.exec_loadFs _ _ .rdi 9 0 rfl (by decide) (by decide)) <;> probe_sides
  probe_instr 146 5 (.movI32 .rax 60)
  probe_trap 151
  probe_exit 0x00010102464c457f
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    Probe.Exactly observed trace outcome :=
  Omni.Exec.sound_any determined finite

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 158)
    probe_instr 125 5 (.movI32 .rdi 0x1002)
    probe_instr 130 5 (.movI32 .rsi 0x400000)
    probe_trap 135
    apply Probe.run_setFs <;> probe_sides
    apply Probe.run_instr _ (off := 137) (len := 9)
      (instruction := .load .q .rdi (Silmaril.X86.Ext.Mem.fsAt 0))
      (exec := Probe.exec_loadFs _ _ .rdi 9 0 rfl (by decide) (by decide)) <;> probe_sides
    probe_instr 146 5 (.movI32 .rax 60)
    probe_trap 151
    probe_exit 0x00010102464c457f
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end ArchFs

namespace ArchFs1

open Data.ArchFs1

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 158)
    probe_instr 125 5 (.movI32 .rdi 0x1002)
    probe_instr 130 5 (.movI32 .rsi 0x400001)
    probe_trap 135
    apply Probe.run_setFs <;> probe_sides
    apply Probe.run_instr _ (off := 137) (len := 9)
      (instruction := .load .q .rdi (Silmaril.X86.Ext.Mem.fsAt 0))
      (exec := Probe.exec_loadFs _ _ .rdi 9 1 rfl (by decide) (by decide)) <;> probe_sides
    probe_instr 146 5 (.movI32 .rax 60)
    probe_trap 151
    probe_exit 0x0000010102464c45
  all_goals probe_side

/-- Mutation: the original's "every execution exits 127" is false of the mutant. -/
theorem not_determined_original : ¬ probe.Determined noFilter Data.ArchFs.observed :=
  Probe.not_determined_of_admits _ admits (by
    intro fs fs' same
    simp [Observed.events, Observed.terminal, observed, Data.ArchFs.observed] at same)

end ArchFs1

namespace ArchGetfs

open Data.ArchGetfs

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The model's actual behaviour: `ARCH_SET_FS` succeeds, then every execution
stops at `ARCH_GET_FS`, which is unmodeled. -/
theorem unmodeled_at_get :
    Omni.Exec probe.segs spec noFilter probe.initial (probe.StopsUnmodeled 158) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400078)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  probe_instr 137 5 (.movI32 .rax 158)
  probe_instr 142 5 (.movI32 .rdi 0x1003)
  probe_instr 147 3 (.mov .q (.reg .rsi) .rsp)
  probe_trap 150
  exact Probe.exec_stops rfl (fun outcome => Probe.archOther_outcomes (by decide) outcome)

/-- Under every refusal filter, every finite execution stops there. -/
theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    probe.StopsUnmodeled 158 trace outcome :=
  Omni.Exec.sound_any unmodeled_at_get finite

theorem unmodeled : (probe.behavior noFilter).unmodeled :=
  Probe.unmodeled_of_stops unmodeled_at_get

/-- Linux's read-back run is not admitted, under any refusal filter. -/
theorem not_admits (refused : RefusalFilter) : ¬ probe.Admits refused observed := by
  rintro ⟨_, _, _, run, _⟩
  obtain ⟨_, _, impossible, _⟩ := sound refused run.finite
  cases impossible

end ArchGetfs

namespace ArchGetfsExit

open Data.ArchGetfsExit

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 158)
  probe_instr 125 5 (.movI32 .rdi 0x1002)
  probe_instr 130 5 (.movI32 .rsi 0x400078)
  probe_trap 135
  apply Probe.exec_setFs <;> probe_sides
  probe_instr 137 5 (.movI32 .rax 60)
  probe_instr 142 5 (.movI32 .rdi 0x1003)
  probe_instr 147 3 (.mov .q (.reg .rsi) .rsp)
  probe_trap 150
  probe_exit 0x1003
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 158)
    probe_instr 125 5 (.movI32 .rdi 0x1002)
    probe_instr 130 5 (.movI32 .rsi 0x400078)
    probe_trap 135
    apply Probe.run_setFs <;> probe_sides
    probe_instr 137 5 (.movI32 .rax 60)
    probe_instr 142 5 (.movI32 .rdi 0x1003)
    probe_instr 147 3 (.mov .q (.reg .rsi) .rsp)
    probe_trap 150
    probe_exit 0x1003
  all_goals probe_side

theorem not_unmodeled (refused : RefusalFilter) : ¬ (probe.behavior refused).unmodeled :=
  Probe.Determined.no_unmodeled _ determined

/-- Mutation: the original's fail-closed property is false of the mutant. -/
theorem not_stops : ¬ Omni.Exec probe.segs spec noFilter probe.initial (probe.StopsUnmodeled 158) :=
  Probe.not_stops_of_admits admits

end ArchGetfsExit

end Silmaril.Process.LPS.Probes
