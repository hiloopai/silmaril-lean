module

public import Silmaril.Process.LPS.Probes.Files
public import Silmaril.Process.LPS.Probes.Data.OpenMissing
public import Silmaril.Process.LPS.Probes.Data.OpenEfault

/-! # Probe `open_missing` and its mutant `open_efault`

`open_missing.s` is `openat(AT_FDCWD, "nofile", O_RDONLY)` on a launch file
system without `nofile`, then `exit(-ret)`: the status is the errno. On Linux
the harness recorded `openat(0xffffff9c, 0x40009b, 0, 0) = -2` (`ENOENT`) and
exit status 2 (`Data.OpenMissing.observed`).

* `OpenMissing.admits`: the model (`noFilter`, the reference `run`) admits that
  run of the actual bytes; the pathname is read from the loaded image.
* `OpenMissing.determined`: every execution halts with exactly that exit event
  and status 2. An absent name is a deterministic `ENOENT` in LPS
  (`Sys/Fs/Open.v:362` `openat_read_spec`): no injected-failure alternative.
  `sound` extends it to every finite execution under any refusal filter.

The mutant `open_efault.s` passes the unmapped pointer `0x1000`. Linux answers
`EFAULT` and the probe exits 14 (`Data.OpenEfault.observed`); the model determines
that run too (`getname`'s fault, `Sys/Fs/Open.v:1339`), and the original's property
is false of the mutant (`OpenEfault.not_determined_missing`).

All of these are about the hub's native table (`Probes.spec`, dispatching
`NativeX86.All.nativeTable`), whose `openat` slot is the fs-io lane's arm
(`OpenMissing.hub_openat_translated`). In the table the hub used before the
all-arms integration, `NativeX86.extendedTable`, `openat` is a pending arm, hence
`unmodeled` (`OpenMissing.previousHub_unmodeled`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace OpenMissing

open Data.OpenMissing

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The name the probe opens: `nofile`. -/
def name : List Byte := [110, 111, 102, 105, 108, 101]

theorem name_read : cstrOfList (probe.bytes.drop 155) pathMax = .ok name := by decide +kernel

/-- Every execution halts with exactly the observed exit event and status 2. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x40009b)
  probe_instr 135 5 (.movI32 .rdx 0)
  probe_trap 140
  probe_call (spec_openat_missing (clear := ?_) (path := name) ?_ ?_ ?_ ?_
    (readCstr_image (off := 155) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_)
  probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 145 3 (.unary .q .neg (.reg .rdi))
  probe_instr 148 5 (.movI32 .rax 60)
  probe_trap 153
  probe_exit 2
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    Probe.Exactly observed trace outcome :=
  Omni.Exec.sound_any determined finite

/-- Reality is admitted by the reference run. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 257)
    probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 130 5 (.movI32 .rsi 0x40009b)
    probe_instr 135 5 (.movI32 .rdx 0)
    probe_trap 140
    probe_call (spec_openat_missing (clear := ?_) (path := name) ?_ ?_ ?_ ?_
      (readCstr_image (off := 155) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_)
    probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 145 3 (.unary .q .neg (.reg .rdi))
    probe_instr 148 5 (.movI32 .rax 60)
    probe_trap 153
    probe_exit 2
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

/-- The hub's native table dispatches `openat` (257) to a translated arm. -/
theorem hub_openat_translated :
    (lookupArm table 257).map (fun a => (a.name, a.status)) = some ("openat", .translated) := by
  decide +kernel

/-- In the hub's previous native table (`NativeX86.extendedTable`, before the
all-arms integration), `openat` (257) is a pending arm. -/
theorem previousHub_openat_pending :
    (lookupArm NativeX86.extendedTable 257).map (·.status) = some .pending := by decide +kernel

/-- So with the previous table every `openat` is `unmodeled`: the theorems above
need the current hub table. -/
theorem previousHub_unmodeled (input : SyscallInput) (model : Model) (number : input.sysno = 257) :
    NativeX86.extendedSyscallSpec input model .unmodeled := by
  have found : lookupArm NativeX86.extendedTable input.sysno.toNat =
      some (pendingArm 257 "openat") := by
    rw [number]; rfl
  unfold NativeX86.extendedSyscallSpec dispatch
  rw [found]
  exact rfl

end OpenMissing

namespace OpenEfault

open Data.OpenEfault

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x1000)
  probe_instr 135 5 (.movI32 .rdx 0)
  probe_trap 140
  probe_call (spec_openat_fault (clear := ?_) ?_ ?_ (readCstr_view_unmapped _ _ ?_))
  probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 145 3 (.unary .q .neg (.reg .rdi))
  probe_instr 148 5 (.movI32 .rax 60)
  probe_trap 153
  probe_exit 14
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 257)
    probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 130 5 (.movI32 .rsi 0x1000)
    probe_instr 135 5 (.movI32 .rdx 0)
    probe_trap 140
    probe_call (spec_openat_fault (clear := ?_) ?_ ?_ (readCstr_view_unmapped _ _ ?_))
    probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 145 3 (.unary .q .neg (.reg .rdi))
    probe_instr 148 5 (.movI32 .rax 60)
    probe_trap 153
    probe_exit 14
  all_goals probe_side

/-- Mutation: the `open_missing` property (exactly `ENOENT`, exit 2) is false of
the mutant, which exits 14. -/
theorem not_determined_missing : ¬ probe.Determined noFilter Data.OpenMissing.observed :=
  Probe.not_determined_of_admits _ admits (by
    intro fs fs' same
    simp [Observed.events, Observed.terminal, observed, Data.OpenMissing.observed] at same)

end OpenEfault

end Silmaril.Process.LPS.Probes
