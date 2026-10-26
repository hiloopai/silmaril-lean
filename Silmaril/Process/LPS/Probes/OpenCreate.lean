module

public import Silmaril.Process.LPS.Probes.Files
public import Silmaril.Process.LPS.Probes.Data.OpenCreate
public import Silmaril.Process.LPS.Probes.Data.OpenCreateKo

/-! # Probe `open_create` and its mutant `open_create_ko`: the final file system

`open_create.s` is `openat(AT_FDCWD, "out.txt", O_WRONLY|O_CREAT|O_TRUNC, 0644)`,
`write(fd, "ok", 2)`, `close(fd)` and `exit(write's return)`, on an empty launch file
system. On Linux the harness recorded `openat(0xffffff9c, 0x4000c2, 0x241, 0x1a4) = 3`,
`write(3, 0x4000ca, 2) = 2`, `close(3) = 0`, exit status 2, and afterwards the work
directory held exactly `out.txt` with the bytes `ok` (`Data.OpenCreate.observed`,
whose `files` the harness read back after the run).

* `OpenCreate.admits`: the model admits that run, and its final file system (the
  file system of the exit event) is exactly the observed one: `out.txt` = `ok`.
* `OpenCreate.exec`, `OpenCreate.sound`: every execution ends in one of two named
  outcomes (`CreateThenExit`): `created`, exit status 2 with `out.txt` = `ok`; or
  `injected`, `openat` failed with an injected errno, the write and the close fail
  with `EBADF`, the probe exits with `-EBADF` (247) and the file system is still empty.
  A regular-file write is never short in LPS (`Sys/Fs/ReadWrite.v:1017`).

The mutant `open_create_ko.s` writes `ko`. Linux leaves `out.txt` = `ko` and still
exits 2 (`Data.OpenCreateKo.observed`): only the final file system differs. The model
admits that file system, so the original's universal statement is false of the mutant
(`OpenCreateKo.not_sound_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

/-- The outcomes of a probe that creates a file, writes it, closes it and exits
with the write's return. -/
inductive CreateThenExit (status : Word) (fs fs₀ : Fs.FileSystem) : Omni.Post x86ExtNative where
  /-- `openat` created the file; the write placed the bytes. -/
  | created {trace : List Event} {final : Config x86ExtNative} :
      trace = [.exitEv status fs] → final.model.halted = some status →
      final.model.killedBy = none → final.model.fs = fs → CreateThenExit status fs fs₀ trace (.halt final)
  /-- `openat` failed with the injected errno `e`: the write and the close fail with
  `EBADF`, the status is the low byte of `-EBADF`, and the file system is `fs₀`. -/
  | injected {trace : List Event} {final : Config x86ExtNative} (e : Int) :
      e ∈ openatErrnos → trace = [.exitEv (errnoRet EBADF &&& 255) fs₀] →
      final.model.halted = some (errnoRet EBADF &&& 255) → final.model.killedBy = none →
      final.model.fs = fs₀ → CreateThenExit status fs fs₀ trace (.halt final)

/-- The name both probes create: `out.txt`. -/
def outName : List Byte := [111, 117, 116, 46, 116, 120, 116]

namespace OpenCreate

open Data.OpenCreate

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem name_read : cstrOfList (probe.bytes.drop 194) pathMax = .ok outName := by decide +kernel

theorem exec :
    Omni.Exec probe.segs spec noFilter probe.initial (CreateThenExit 2 observed.files []) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x4000c2)
  probe_instr 135 5 (.movI32 .rdx 0x241)
  probe_instr 140 6 (.movI32 .r10 0x1a4)
  probe_trap 146
  probe_open (spec_openat_create (clear := ?_) (path := outName) ?_ ?_ ?_ ?_ ?_
    (readCstr_image (off := 194) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
  · probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 151 5 (.movI32 .rax 1)
    probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 159 5 (.movI32 .rsi 0x4000ca)
    probe_instr 164 5 (.movI32 .rdx 2)
    probe_trap 169
    probe_call (spec_write_file (clear := ?_) (path := outName) (off := 0) (data := []) ?_ ?_ ?_ ?_
      (writeSource_image (P := probe) (off := 202) (length := 2) ?_ ?_ ?_ ?_) ?_ ?_ ?_)
    probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
    probe_instr 174 5 (.movI32 .rax 3)
    probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
    probe_trap 182
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instr 184 5 (.movI32 .rax 60)
    probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
    probe_trap 192
    probe_exit 2
    exact .created rfl rfl rfl rfl
  · intro e member
    rcases openatErrnos_cases member with rfl | rfl | rfl | rfl
    all_goals
      probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
      probe_instr 151 5 (.movI32 .rax 1)
      probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
      probe_instr 159 5 (.movI32 .rsi 0x4000ca)
      probe_instr 164 5 (.movI32 .rdx 2)
      probe_trap 169
      probe_call (spec_write_badfd (clear := ?_) ?_ ?_)
      probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
      probe_instr 174 5 (.movI32 .rax 3)
      probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
      probe_trap 182
      probe_call (spec_close_badfd (clear := ?_) ?_ ?_)
      probe_instr 184 5 (.movI32 .rax 60)
      probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
      probe_trap 192
      probe_exit _
      exact .injected _ member rfl rfl rfl rfl

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    CreateThenExit 2 observed.files [] trace outcome :=
  Omni.Exec.sound_any exec finite

/-- Reality is admitted, with the observed final file system `out.txt` = `ok`. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 257)
    probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 130 5 (.movI32 .rsi 0x4000c2)
    probe_instr 135 5 (.movI32 .rdx 0x241)
    probe_instr 140 6 (.movI32 .r10 0x1a4)
    probe_trap 146
    probe_open (spec_openat_create (clear := ?_) (path := outName) ?_ ?_ ?_ ?_ ?_
      (readCstr_image (off := 194) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
    probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 151 5 (.movI32 .rax 1)
    probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 159 5 (.movI32 .rsi 0x4000ca)
    probe_instr 164 5 (.movI32 .rdx 2)
    probe_trap 169
    probe_call (spec_write_file (clear := ?_) (path := outName) (off := 0) (data := []) ?_ ?_ ?_ ?_
      (writeSource_image (P := probe) (off := 202) (length := 2) ?_ ?_ ?_ ?_) ?_ ?_ ?_)
    probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
    probe_instr 174 5 (.movI32 .rax 3)
    probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
    probe_trap 182
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instr 184 5 (.movI32 .rax 60)
    probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
    probe_trap 192
    probe_exit 2
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Omni.Exec.no_error exec (fun _ _ post => by cases post)

end OpenCreate

namespace OpenCreateKo

open Data.OpenCreateKo

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem name_read : cstrOfList (probe.bytes.drop 194) pathMax = .ok outName := by decide +kernel

/-- Reality is admitted: the mutant leaves `out.txt` = `ko`. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 257)
    probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 130 5 (.movI32 .rsi 0x4000c2)
    probe_instr 135 5 (.movI32 .rdx 0x241)
    probe_instr 140 6 (.movI32 .r10 0x1a4)
    probe_trap 146
    probe_open (spec_openat_create (clear := ?_) (path := outName) ?_ ?_ ?_ ?_ ?_
      (readCstr_image (off := 194) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
    probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 151 5 (.movI32 .rax 1)
    probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 159 5 (.movI32 .rsi 0x4000ca)
    probe_instr 164 5 (.movI32 .rdx 2)
    probe_trap 169
    probe_call (spec_write_file (clear := ?_) (path := outName) (off := 0) (data := []) ?_ ?_ ?_ ?_
      (writeSource_image (P := probe) (off := 202) (length := 2) ?_ ?_ ?_ ?_) ?_ ?_ ?_)
    probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
    probe_instr 174 5 (.movI32 .rax 3)
    probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
    probe_trap 182
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instr 184 5 (.movI32 .rax 60)
    probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
    probe_trap 192
    probe_exit 2
  all_goals probe_side

/-- Mutation: the original's universal statement (every execution ends with
`out.txt` = `ok`, or with an untouched file system) is false of the mutant, whose
admitted run ends with `out.txt` = `ko`. -/
theorem not_sound_original :
    ¬ ∀ trace outcome, Omni.FiniteExec probe.segs spec noFilter probe.initial trace outcome →
      CreateThenExit 2 Data.OpenCreate.observed.files [] trace outcome := by
  intro sound
  obtain ⟨_, _, final, run, _, _, files, _⟩ := admits
  cases sound _ _ run.finite with
  | created _ _ _ same =>
    rw [files] at same
    exact absurd same (by decide)
  | injected _ _ _ _ _ same =>
    rw [files] at same
    exact absurd same (by decide)

end OpenCreateKo

end Silmaril.Process.LPS.Probes
