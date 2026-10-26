module

public import Silmaril.Process.LPS.Probes.Data.WriteHello
public import Silmaril.Process.LPS.Probes.Data.WriteHello5

/-! # Probe `write_hello` and its mutant `write_hello5`

`write_hello.s` is `write(1, "hello\n", 6); exit(0)`, the six message bytes
following the code in the loaded segment. On Linux the harness recorded the raw
syscalls `write(1, 0x40009a, 6) = 6` and `exit(0)`, stdout `hello\n` and exit
status 0 (`Data.WriteHello.observed`).

* `WriteHello.admits`: the LPS model (`noFilter`, the reference `run`) admits
  exactly that run of the actual bytes: the write reads the six bytes from the
  loaded image through the read view of the initial memory.
* `WriteHello.exec`, `WriteHello.sound`: every execution halts with exit status
  0 after writing a nonempty prefix of `hello\n`, under any refusal filter. The
  one explicitly sanctioned alternative is the reference short write
  (`Outcome.shortWrite`): the channel may accept fewer bytes than requested,
  and since the probe ignores the return value it still exits 0. Nothing errors
  or is unmodeled.

The mutant `write_hello5.s` passes length 5. Linux prints `hello` without the
newline (`Data.WriteHello5.observed`); the model admits that run, and no
observable trace of the mutant is the original's observation
(`WriteHello5.not_traces_original`): every mutant write delivers at most 5 bytes.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

/-- The outcomes a channel write of `bs` followed by `exit(0)` may have: the
write delivers `ds` (all of `bs`, or a short write of a nonempty prefix). -/
inductive WriteThenExit (bs : List Byte) : Omni.Post x86ExtNative where
  | full {final : Config x86ExtNative} :
      final.model.halted = some 0 → final.model.killedBy = none →
      WriteThenExit bs (bs.map (.writeEv 1) ++ [.exitEv 0 final.model.fs]) (.halt final)
  | shortWrite {ds : List Byte} {final : Config x86ExtNative} :
      ds ≠ [] → ds <+: bs → ds ≠ bs →
      final.model.halted = some 0 → final.model.killedBy = none →
      WriteThenExit bs (ds.map (.writeEv 1) ++ [.exitEv 0 final.model.fs]) (.halt final)

theorem WriteThenExit.intro {bs ds : List Byte} {final : Config x86ExtNative} {code : Word}
    {fs : Fs.FileSystem} (delivered : Probe.WritePrefix bs ds) (zero : code = 0)
    (sameFs : fs = final.model.fs) (halted : final.model.halted = some 0)
    (unkilled : final.model.killedBy = none) :
    WriteThenExit bs (ds.map (.writeEv 1) ++ [.exitEv code fs]) (.halt final) := by
  subst zero sameFs
  by_cases all : ds = bs
  · subst all
    exact .full halted unkilled
  · exact .shortWrite delivered.1 delivered.2 all halted unkilled

theorem WriteThenExit.delivered {bs : List Byte} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (post : WriteThenExit bs trace outcome) :
    ∃ (ds : List Byte) (final : Config x86ExtNative), ds <+: bs ∧ trace = ds.map (.writeEv 1) ++ [.exitEv 0 final.model.fs] := by
  cases post with
  | full => exact ⟨bs, _, List.prefix_refl _, rfl⟩
  | shortWrite _ pre => exact ⟨_, _, pre, rfl⟩

namespace WriteHello

open Data.WriteHello

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem message : (probe.bytes.drop 154).take 6 = observed.stdout := by decide +kernel

/-- Every execution without refusals; `sound` extends it to every filter. -/
theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (WriteThenExit observed.stdout) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x40009a)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  probe_write 154 6
  intro ds delivered
  probe_instr 142 5 (.movI32 .rax 60)
  probe_instr 147 5 (.movI32 .rdi 0)
  probe_trap 152
  probe_exit 0
  rw [message] at delivered
  apply WriteThenExit.intro delivered <;> probe_side

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    WriteThenExit observed.stdout trace outcome :=
  Omni.Exec.sound_any exec finite

/-- Reality is admitted by the reference run: the full write of `hello\n`. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 1)
    probe_instr 125 5 (.movI32 .rdi 1)
    probe_instr 130 5 (.movI32 .rsi 0x40009a)
    probe_instr 135 5 (.movI32 .rdx 6)
    probe_trap 140
    probe_write 154 6 with observed.stdout
    probe_instr 142 5 (.movI32 .rax 60)
    probe_instr 147 5 (.movI32 .rdi 0)
    probe_trap 152
    probe_exit 0
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Omni.Exec.no_error exec (fun _ _ post => by cases post)

end WriteHello

namespace WriteHello5

open Data.WriteHello5

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem message : (probe.bytes.drop 154).take 5 = observed.stdout := by decide +kernel

theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (WriteThenExit observed.stdout) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 1)
  probe_instr 125 5 (.movI32 .rdi 1)
  probe_instr 130 5 (.movI32 .rsi 0x40009a)
  probe_instr 135 5 (.movI32 .rdx 5)
  probe_trap 140
  probe_write 154 5
  intro ds delivered
  probe_instr 142 5 (.movI32 .rax 60)
  probe_instr 147 5 (.movI32 .rdi 0)
  probe_trap 152
  probe_exit 0
  rw [message] at delivered
  apply WriteThenExit.intro delivered <;> probe_side

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 1)
    probe_instr 125 5 (.movI32 .rdi 1)
    probe_instr 130 5 (.movI32 .rsi 0x40009a)
    probe_instr 135 5 (.movI32 .rdx 5)
    probe_trap 140
    probe_write 154 5 with observed.stdout
    probe_instr 142 5 (.movI32 .rax 60)
    probe_instr 147 5 (.movI32 .rdi 0)
    probe_trap 152
    probe_exit 0
  all_goals probe_side

/-- Mutation: under any refusal filter, the original's observation (`hello\n`
then exit 0) is not even a prefix of a mutant trace. -/
theorem not_traces_original (refused : RefusalFilter) (fs : Fs.FileSystem) :
    ¬ (probe.behavior refused).traces (Data.WriteHello.observed.events fs) := by
  intro traced
  obtain ⟨rest, _, pre, post⟩ := Omni.Exec.obsTrace exec traced
  obtain ⟨ds, _, delivered, rfl⟩ := post.delivered
  have long := pre.length_le
  have short := delivered.length_le
  have five : observed.stdout.length = 5 := rfl
  have seven : (Data.WriteHello.observed.events fs).length = 7 := rfl
  simp only [List.length_append, List.length_map, List.length_singleton] at long
  omega

end WriteHello5

end Silmaril.Process.LPS.Probes
