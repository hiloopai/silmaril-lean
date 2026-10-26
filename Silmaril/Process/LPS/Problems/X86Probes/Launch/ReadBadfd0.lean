module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.ReadBadfd
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.ReadEcho

/-! # `read_badfd0` at every native launch

`read_badfd0.s` is `read(0, buffer, 6); exit(0 - rax)`. Stdin is the launch input's, so the
read returns 0 at end of file and otherwise `k` bytes for some `1 ≤ k ≤ 6` (all available
bytes or a short read): the probe exits 0 or `-k & 255`, that is `0` or one of `250 … 255`.
Linux's run read the harness's empty stdin and exited 0.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-- The outcomes of `read(0, buffer, count); exit(0 - rax)`. -/
inductive ReadThenNeg (count : Nat) : Omni.Post x86ExtNative where
  /-- End of file: the read returns 0, the status is 0. -/
  | eof {final : Config x86ExtNative} {fs : Fs.FileSystem} {code : Word} : code = 0 →
      final.model.halted = some 0 → final.model.killedBy = none →
      ReadThenNeg count [.exitEv code fs] (.halt final)
  /-- The read delivers `bs`, of length `k`; the status is `-k & 255`. -/
  | read {bs : List Byte} {final : Config x86ExtNative} {fs : Fs.FileSystem} {code : Word} (k : Nat) :
      0 < k → k ≤ count → code = negStatus k →
      final.model.halted = some (negStatus k) → final.model.killedBy = none →
      ReadThenNeg count (bs.map (.readEv 0) ++ [.exitEv code fs]) (.halt final)

theorem ReadThenNeg.exitsIn (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : ReadThenNeg 6 trace outcome) :
    Omni.ExitsIn ([0, 250, 251, 252, 253, 254, 255] : List Word) trace outcome := by
  cases post with
  | eof _ halted unkilled => exact ⟨0, halted, by decide, unkilled⟩
  | read k positive atMost _ halted unkilled =>
    refine ⟨_, halted, ?_, unkilled⟩
    rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> first | omega | decide

theorem ReadThenNeg.silent (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : ReadThenNeg 6 trace outcome) : TraceSpec.silent.denote trace := by
  cases post with
  | eof => exact ⟨rfl, rfl⟩
  | read =>
    refine ⟨?_, ?_⟩
    · rw [written_reads]
      rfl
    · rw [writesOtherThan_reads]
      rfl

set_option maxHeartbeats 2000000 in
theorem readBadfd0_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadBadfd0.probe en inp) :
    Omni.Exec Data.ReadBadfd0.probe.segs spec noFilter (Data.ReadBadfd0.probe.launchedAt en inp).initial
      (ReadThenNeg 6) := by
  have := Probe.checked_launchedAt (P := Data.ReadBadfd0.probe) launch.entry launch.input
  show Omni.Exec (Data.ReadBadfd0.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_instr 130 5 (.movI32 .rsi 0x40009d)
  probe_instr 135 5 (.movI32 .rdx 6)
  probe_trap 140
  cases eof : inp.stdin.atEof
  · apply Probe.exec_read (boff := 157) (count := 6)
    case number => rfl
    case running => rfl
    case lazy => rfl
    case rwx => rfl
    case lookup => rfl
    case buffer => probe_side
    case accessible => probe_side
    case clear => probe_side
    case clamp => probe_reg_ne
    case positive => decide
    case small => decide
    case fits => probe_side
    case notEof => exact eof
    intro bs read
    have small : 157 + bs.length ≤ (Data.ReadBadfd0.probe.launchedAt en inp).size := by
      have := read.2.1
      change 157 + bs.length ≤ 163
      omega
    have positive := List.length_pos_iff.mpr read.1
    have atMost := read.2.1
    rw [show lenWord bs = zw (bs.length : Int) from rfl]
    obtain length | length | length | length | length | length :
        bs.length = 1 ∨ bs.length = 2 ∨ bs.length = 3 ∨ bs.length = 4 ∨ bs.length = 5 ∨ bs.length = 6 := by
      omega
    all_goals
      rw [length]
      probe_instrW 142 5 (.movI32 .rdi 0)
      probe_instrW 147 3 (.alu .q .sub (.reg .rdi) .rax)
      probe_instrW 150 5 (.movI32 .rax 60)
      probe_trapW 155
      probe_exitW _
      first
        | exact .read 1 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
        | exact .read 2 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
        | exact .read 3 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
        | exact .read 4 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
        | exact .read 5 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
        | exact .read 6 (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  · probe_ret read_eof_iff
    probe_instr 142 5 (.movI32 .rdi 0)
    probe_instr 147 3 (.alu .q .sub (.reg .rdi) .rax)
    probe_instr 150 5 (.movI32 .rax 60)
    probe_trap 155
    probe_exit 0
    exact .eof (by rfl) (by rfl) (by rfl)

end Silmaril.Process.LPS.Problems.X86Probes
