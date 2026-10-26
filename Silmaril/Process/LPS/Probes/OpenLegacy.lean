module

public import Silmaril.Process.LPS.Probes.Files
public import Silmaril.Process.LPS.Probes.Data.OpenLegacy

/-! # Probe `open_legacy`: the legacy x86-64 `open(2)`

`open_legacy.s` is `open("in.txt", O_RDONLY)` (native number 2, which musl's
`open` uses) on a launch file system holding `in.txt`, then `exit(fd)`. On Linux
the harness recorded `open(0x400093, 0, 0) = 3` and exit status 3
(`Data.OpenLegacy.observed`).

LPS's asm-generic table has no `open`; the fs-io lane translates the x86-64 entry
point as `openat(AT_FDCWD, …)` (`Sys/FsIo/Open.lean` `openSpecX86`, after
`fs/open.c` `SYSCALL_DEFINE3(open)`), and the hub's native table
(`NativeX86.All.nativeTable`, the probes' `Probes.table`) installs it as an
x86-64-only extension arm (`OpenLegacy.hub_open_translated`).

* `OpenLegacy.admits`: the model admits the recorded run of the actual bytes.
* `OpenLegacy.exec`, `OpenLegacy.sound`: every execution ends in one of two named
  outcomes (`OpenStatus`): `opened`, exit status 3 (the lowest free descriptor), or
  `injected`, the open failed with an injected `ENOMEM`, `EACCES`, `EMFILE` or
  `ENFILE` (LPS `Sys/Fs/Open.v:27` `openat_errnos`) and the status is `-errno`. The
  file system is the launch one in both.
* `OpenLegacy.previousHub_unmodeled`: the table the hub dispatched native calls
  through before the all-arms integration (`NativeX86.extendedTable`, still defined
  in `Machines.X86ArchPrctl`) has no row for number 2, so there the call is
  `unmodeled`: the gap this probe found, closed in the hub by #3534/#3564.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

/-- The outcomes of a probe that opens a file and exits with the descriptor. -/
inductive OpenStatus (fd : Word) (fs : Fs.FileSystem) : Omni.Post x86ExtNative where
  /-- The open returned the lowest free descriptor `fd`. -/
  | opened {trace : List Event} {final : Config x86ExtNative} :
      trace = [.exitEv fd fs] → final.model.halted = some fd → final.model.killedBy = none →
      final.model.fs = fs → OpenStatus fd fs trace (.halt final)
  /-- The open failed with the injected errno `e`; the status is the low byte of `-e`. -/
  | injected {trace : List Event} {final : Config x86ExtNative} (e : Int) :
      e ∈ openatErrnos → trace = [.exitEv (errnoRet e &&& 255) fs] →
      final.model.halted = some (errnoRet e &&& 255) → final.model.killedBy = none →
      final.model.fs = fs → OpenStatus fd fs trace (.halt final)

namespace OpenLegacy

open Data.OpenLegacy

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputFiles_valid _ (by unfold Fs.ValidFs; decide) (by decide),
    probe.snapshot_valid layout,
    by unfold ValidBrk; decide +kernel⟩

/-- The name the probe opens: `in.txt`. -/
def name : List Byte := [105, 110, 46, 116, 120, 116]

theorem name_read : cstrOfList (probe.bytes.drop 147) pathMax = .ok name := by decide +kernel

theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (OpenStatus 3 observed.files) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 2)
  probe_instr 125 5 (.movI32 .rdi 0x400093)
  probe_instr 130 5 (.movI32 .rsi 0)
  probe_trap 135
  probe_open (spec_open_read (clear := ?_) (path := name) ?_ ?_ ?_
    (readCstr_image (off := 147) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
  · probe_instr 137 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 140 5 (.movI32 .rax 60)
    probe_trap 145
    probe_exit 3
    exact .opened rfl rfl rfl rfl
  · intro e member
    rcases openatErrnos_cases member with rfl | rfl | rfl | rfl
    all_goals
      probe_instr 137 3 (.mov .q (.reg .rdi) .rax)
      probe_instr 140 5 (.movI32 .rax 60)
      probe_trap 145
      probe_exit _
      exact .injected _ member rfl rfl rfl rfl

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    OpenStatus 3 observed.files trace outcome :=
  Omni.Exec.sound_any exec finite

/-- Reality is admitted: `open` returns descriptor 3 and the probe exits 3. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 2)
    probe_instr 125 5 (.movI32 .rdi 0x400093)
    probe_instr 130 5 (.movI32 .rsi 0)
    probe_trap 135
    probe_open (spec_open_read (clear := ?_) (path := name) ?_ ?_ ?_
      (readCstr_image (off := 147) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
    probe_instr 137 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 140 5 (.movI32 .rax 60)
    probe_trap 145
    probe_exit 3
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Omni.Exec.no_error exec (fun _ _ post => by cases post)

/-- The hub's native table dispatches number 2 to the translated legacy `open`. -/
theorem hub_open_translated :
    (lookupArm table 2).map (fun a => (a.name, a.status)) = some ("open", .translated) := by
  decide +kernel

/-- The hub's previous native table (`NativeX86.extendedTable`, the table of the
native launch before the all-arms integration) has no number 2. -/
theorem previousHub_open_missing : (lookupArm NativeX86.extendedTable 2).isNone = true := by
  decide +kernel

/-- So in the previous table `open` was `unmodeled`. -/
theorem previousHub_unmodeled (input : SyscallInput) (model : Model) (number : input.sysno = 2) :
    NativeX86.extendedSyscallSpec input model .unmodeled := by
  have missing : lookupArm NativeX86.extendedTable input.sysno.toNat = none := by
    rw [number]
    exact Option.isNone_iff_eq_none.mp previousHub_open_missing
  unfold NativeX86.extendedSyscallSpec dispatch
  rw [missing]
  exact rfl

end OpenLegacy

end Silmaril.Process.LPS.Probes
