module

public import Silmaril.Process.LPS.Probes.KitMemory
public import Silmaril.Process.LPS.Probes.Data.ReadEcho
public import Silmaril.Process.LPS.Probes.Data.ReadEcho2

/-! # Probe `read_echo` and its mutant `read_echo2`

`read_echo.s` is `n = read(0, buffer, 16); write(1, buffer, n); exit(0)`, with
the 16-byte buffer in the probe's own writable (`rwx`) image at `0x4000a9`. The
harness ran it with stdin `ping\n` and recorded `read(0, 0x4000a9, 16) = 5`,
`write(1, 0x4000a9, 5) = 5`, stdout `ping\n` and exit status 0
(`Data.ReadEcho.observed`).

Stdin is an input of the LPS launch, so the universal statement quantifies over
it. `ReadEcho.exec_any s`: for *every* stdin stream `s`, every execution of the
actual bytes launched with stdin `s` (no refusals) halts with status 0 in one of
the two outcomes of `Echo 16 s`:

* `Echo.atEof`: stdin is at end of file. The read returns 0, the write of
  0 bytes returns 0, and the probe exits 0 with no output.
* `Echo.echoed`: the read delivers `bs`, a nonempty prefix of stdin of at most
  16 bytes (all available bytes or a reference short read), and stores it in
  the buffer. The write then delivers `ds`, a nonempty prefix of `bs` (all of it
  or a reference short write). The trace is the read events of `bs`, the write
  events of `ds`, then the exit.

So the output is always a prefix of what was read, which is a prefix of stdin.
`ReadEcho.exec` and `ReadEcho.sound` are this for the recorded stdin, the latter
under any refusal filter; `ReadEcho.no_error`: nothing errors or is unmodeled.
`ReadEcho.admits`: the recorded run (the full read of `ping\n` and its full echo)
is a run of the model.

The mutant `read_echo2.s` reads at most 2 bytes. Linux echoes `pi`
(`Data.ReadEcho2.observed`), which the model admits. No trace of the mutant, under
any refusal filter, has the original's observation as a prefix
(`ReadEcho2.not_traces_original`), because every mutant execution reads at
most 2 bytes and the original's observation has 5 read events.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

/-- The outcomes of `n = read(0, buffer, count); write(1, buffer, n); exit(0)`
with stdin `s`. -/
inductive Echo (count : Nat) (s : InputStream) : Omni.Post x86ExtNative where
  /-- Stdin is at end of file: nothing is read or written. -/
  | atEof {final : Config x86ExtNative} : s.atEof = true →
      final.model.halted = some 0 → final.model.killedBy = none →
      Echo count s [.exitEv 0 final.model.fs] (.halt final)
  /-- The read delivers a prefix `bs` of stdin (all of it or a short read) and the
  write delivers a prefix `ds` of `bs` (all of it or a short write). -/
  | echoed {bs ds : List Byte} {final : Config x86ExtNative} :
      ReadPrefix s count bs → Probe.WritePrefix bs ds →
      final.model.halted = some 0 → final.model.killedBy = none →
      Echo count s (bs.map (.readEv 0) ++ ds.map (.writeEv 1) ++ [.exitEv 0 final.model.fs]) (.halt final)

theorem Echo.intro {count : Nat} {s : InputStream} {bs ds : List Byte} {final : Config x86ExtNative}
    {code : Word} {fs : Fs.FileSystem} (read : ReadPrefix s count bs) (delivered : Probe.WritePrefix bs ds)
    (zero : code = 0) (sameFs : fs = final.model.fs) (halted : final.model.halted = some 0)
    (unkilled : final.model.killedBy = none) :
    Echo count s (bs.map (.readEv 0) ++ (ds.map (.writeEv 1) ++ [.exitEv code fs])) (.halt final) := by
  subst zero sameFs
  rw [← List.append_assoc]
  exact .echoed read delivered halted unkilled

theorem Echo.intro_eof {count : Nat} {s : InputStream} {final : Config x86ExtNative}
    {code : Word} {fs : Fs.FileSystem} (eof : s.atEof = true)
    (zero : code = 0) (sameFs : fs = final.model.fs) (halted : final.model.halted = some 0)
    (unkilled : final.model.killedBy = none) :
    Echo count s [.exitEv code fs] (.halt final) := by
  subst zero sameFs
  exact .atEof eof halted unkilled

/-- Whether an event is a read. -/
def isReadEv : Event → Bool
  | .readEv _ _ => true
  | _ => false

/-- An `Echo count` trace has at most `count` read events. -/
theorem Echo.reads_le {count : Nat} {s : InputStream} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (post : Echo count s trace outcome) :
    trace.countP isReadEv ≤ count := by
  cases post with
  | atEof => simp [isReadEv]
  | echoed read =>
    simp [List.countP_append, List.countP_map, isReadEv, Function.comp_def]
    exact read.2.1

namespace ReadEcho

open Data.ReadEcho

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputWith_valid stdin, probe.snapshot_valid layout,
    by unfold ValidBrk; decide +kernel⟩

/-- The probe launched with stdin `s` loads the same segments and starts from the
same registers and memory, with `s` as the model's stdin. -/
theorem initial_withStdin (s : InputStream) :
    (probe.withStdin s).segs = probe.segs ∧
      (probe.withStdin s).initial = probe.cfg probe.core0 none (probe.model0.withStdin s) := ⟨rfl, rfl⟩

/-- Every execution without refusals, for every stdin stream. -/
theorem exec_any (s : InputStream) :
    Omni.Exec probe.segs spec noFilter (probe.withStdin s).initial (Echo 16 s) := by
  rw [(initial_withStdin s).2]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_instr 130 5 (.movI32 .rsi 0x4000a9)
  probe_instr 135 5 (.movI32 .rdx 16)
  probe_trap 140
  cases eof : s.atEof
  · apply Probe.exec_read (boff := 169) (count := 16) <;> (try exact eof) <;> probe_sides
    intro bs read
    have small : 169 + bs.length ≤ probe.size := by
      have := read.2.1
      change 169 + bs.length ≤ 185
      omega
    have below : uns (lenWord bs) < taskSizeMaxX86 := by
      have bound := read.2.1
      unfold uns
      rw [lenWord_toNat bs (by omega)]
      unfold taskSizeMaxX86
      omega
    probe_instrW 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instrW 145 5 (.movI32 .rax 1)
    probe_instrW 150 5 (.movI32 .rdi 1)
    probe_trapW 155
    apply Probe.exec_write_written (boff := 169) <;> (try exact read.1) <;> (try assumption) <;>
      probe_sides
    intro ds delivered
    probe_instrW 157 5 (.movI32 .rax 60)
    probe_instrW 162 5 (.movI32 .rdi 0)
    probe_trapW 167
    probe_exitW 0
    apply Echo.intro read delivered <;> probe_side
  · probe_ret read_eof_iff
    probe_instr 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instr 145 5 (.movI32 .rax 1)
    probe_instr 150 5 (.movI32 .rdi 1)
    probe_trap 155
    probe_ret write_zero_iff
    probe_instr 157 5 (.movI32 .rax 60)
    probe_instr 162 5 (.movI32 .rdi 0)
    probe_trap 167
    probe_exit 0
    apply Echo.intro_eof eof <;> probe_side

/-- Every execution without refusals, for the recorded stdin. -/
theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (Echo 16 (InputStream.ofList stdin)) :=
  exec_any (InputStream.ofList stdin)

/-- Every finite execution under any refusal filter, for the recorded stdin. -/
theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    Echo 16 (InputStream.ofList stdin) trace outcome :=
  Omni.Exec.sound_any exec finite

/-- Reality is admitted: the full read of `ping\n` and its full echo. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 0)
    probe_instr 125 5 (.movI32 .rdi 0)
    probe_instr 130 5 (.movI32 .rsi 0x4000a9)
    probe_instr 135 5 (.movI32 .rdx 16)
    probe_trap 140
    apply Probe.run_read (boff := 169) (count := 16) (bs := observed.stdin) <;> probe_sides
    probe_instrW 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instrW 145 5 (.movI32 .rax 1)
    probe_instrW 150 5 (.movI32 .rdi 1)
    probe_trapW 155
    apply Probe.run_write_written (boff := 169) (ds := observed.stdout) <;> probe_sides
    probe_instrW 157 5 (.movI32 .rax 60)
    probe_instrW 162 5 (.movI32 .rdi 0)
    probe_trapW 167
    probe_exitW 0
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Omni.Exec.no_error exec (fun _ _ post => by cases post)

end ReadEcho

namespace ReadEcho2

open Data.ReadEcho2

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputWith_valid stdin, probe.snapshot_valid layout,
    by unfold ValidBrk; decide +kernel⟩

/-- The probe launched with stdin `s` loads the same segments and starts from the
same registers and memory, with `s` as the model's stdin. -/
theorem initial_withStdin (s : InputStream) :
    (probe.withStdin s).segs = probe.segs ∧
      (probe.withStdin s).initial = probe.cfg probe.core0 none (probe.model0.withStdin s) := ⟨rfl, rfl⟩

/-- Every execution of the mutant without refusals, for every stdin stream: it
reads at most 2 bytes. -/
theorem exec_any (s : InputStream) :
    Omni.Exec probe.segs spec noFilter (probe.withStdin s).initial (Echo 2 s) := by
  rw [(initial_withStdin s).2]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_instr 130 5 (.movI32 .rsi 0x4000a9)
  probe_instr 135 5 (.movI32 .rdx 2)
  probe_trap 140
  cases eof : s.atEof
  · apply Probe.exec_read (boff := 169) (count := 2) <;> (try exact eof) <;> probe_sides
    intro bs read
    have small : 169 + bs.length ≤ probe.size := by
      have := read.2.1
      change 169 + bs.length ≤ 185
      omega
    have below : uns (lenWord bs) < taskSizeMaxX86 := by
      have bound := read.2.1
      unfold uns
      rw [lenWord_toNat bs (by omega)]
      unfold taskSizeMaxX86
      omega
    probe_instrW 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instrW 145 5 (.movI32 .rax 1)
    probe_instrW 150 5 (.movI32 .rdi 1)
    probe_trapW 155
    apply Probe.exec_write_written (boff := 169) <;> (try exact read.1) <;> (try assumption) <;>
      probe_sides
    intro ds delivered
    probe_instrW 157 5 (.movI32 .rax 60)
    probe_instrW 162 5 (.movI32 .rdi 0)
    probe_trapW 167
    probe_exitW 0
    apply Echo.intro read delivered <;> probe_side
  · probe_ret read_eof_iff
    probe_instr 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instr 145 5 (.movI32 .rax 1)
    probe_instr 150 5 (.movI32 .rdi 1)
    probe_trap 155
    probe_ret write_zero_iff
    probe_instr 157 5 (.movI32 .rax 60)
    probe_instr 162 5 (.movI32 .rdi 0)
    probe_trap 167
    probe_exit 0
    apply Echo.intro_eof eof <;> probe_side

theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (Echo 2 (InputStream.ofList stdin)) :=
  exec_any (InputStream.ofList stdin)

/-- Linux's run of the mutant: the read of `pi` and its full echo. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 0)
    probe_instr 125 5 (.movI32 .rdi 0)
    probe_instr 130 5 (.movI32 .rsi 0x4000a9)
    probe_instr 135 5 (.movI32 .rdx 2)
    probe_trap 140
    apply Probe.run_read (boff := 169) (count := 2) (bs := observed.stdin) <;> probe_sides
    probe_instrW 142 3 (.mov .q (.reg .rdx) .rax)
    probe_instrW 145 5 (.movI32 .rax 1)
    probe_instrW 150 5 (.movI32 .rdi 1)
    probe_trapW 155
    apply Probe.run_write_written (boff := 169) (ds := observed.stdout) <;> probe_sides
    probe_instrW 157 5 (.movI32 .rax 60)
    probe_instrW 162 5 (.movI32 .rdi 0)
    probe_trapW 167
    probe_exitW 0
  all_goals probe_side

/-- Mutation: under any refusal filter, the original's observation (5 bytes read,
`ping\n` echoed, exit 0) is not even a prefix of a mutant trace. -/
theorem not_traces_original (refused : RefusalFilter) (fs : Fs.FileSystem) :
    ¬ (probe.behavior refused).traces (Data.ReadEcho.observed.events fs) := by
  intro traced
  obtain ⟨rest, _, pre, post⟩ := Omni.Exec.obsTrace exec traced
  have reads := pre.sublist.countP_le (p := isReadEv)
  have five : (Data.ReadEcho.observed.events fs).countP isReadEv = 5 := rfl
  have two := post.reads_le
  omega

end ReadEcho2

end Silmaril.Process.LPS.Probes
