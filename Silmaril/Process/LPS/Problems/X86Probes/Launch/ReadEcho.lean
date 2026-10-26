module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.ReadEcho

/-! # `read_echo` and `read_echo2` at every native launch

The kit's `ReadEcho.exec_any` is already universal in the stdin stream; replayed at the
symbolic launch it is universal in the whole launch, with the launch input's stdin
(`Echo count inp.stdin`): what is written to stdout is a prefix of what was read, which is a
prefix of stdin, and the status is 0.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem readEcho_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadEcho.probe en inp) :
    Omni.Exec Data.ReadEcho.probe.segs spec noFilter (Data.ReadEcho.probe.launchedAt en inp).initial (Echo 16 inp.stdin) := by
  have := Probe.checked_launchedAt (P := Data.ReadEcho.probe) launch.entry launch.input
  show Omni.Exec (Data.ReadEcho.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_instr 130 5 (.movI32 .rsi 0x4000a9)
  probe_instr 135 5 (.movI32 .rdx 16)
  probe_trap 140
  cases eof : inp.stdin.atEof
  · apply Probe.exec_read (boff := 169) (count := 16)
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
    have small : 169 + bs.length ≤ (Data.ReadEcho.probe.launchedAt en inp).size := by
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

theorem readEcho2_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadEcho2.probe en inp) :
    Omni.Exec Data.ReadEcho2.probe.segs spec noFilter (Data.ReadEcho2.probe.launchedAt en inp).initial (Echo 2 inp.stdin) := by
  have := Probe.checked_launchedAt (P := Data.ReadEcho2.probe) launch.entry launch.input
  show Omni.Exec (Data.ReadEcho2.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 0)
  probe_instr 125 5 (.movI32 .rdi 0)
  probe_instr 130 5 (.movI32 .rsi 0x4000a9)
  probe_instr 135 5 (.movI32 .rdx 2)
  probe_trap 140
  cases eof : inp.stdin.atEof
  · apply Probe.exec_read (boff := 169) (count := 2)
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
    have small : 169 + bs.length ≤ (Data.ReadEcho2.probe.launchedAt en inp).size := by
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

theorem readFrom_reads (fd : Word) (bs : List Byte) (rest : List Event) :
    readFrom fd (bs.map (.readEv fd) ++ rest) = bs ++ readFrom fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readFrom, ih]

theorem readFrom_writes (fd ch : Word) (bs : List Byte) (rest : List Event) :
    readFrom fd (bs.map (.writeEv ch) ++ rest) = readFrom fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readFrom, ih]

theorem written_reads (fd ch : Word) (bs : List Byte) (rest : List Event) :
    written fd (bs.map (.readEv ch) ++ rest) = written fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [written, ih]

theorem writesOtherThan_reads (fd ch : Word) (bs : List Byte) (rest : List Event) :
    writesOtherThan fd (bs.map (.readEv ch) ++ rest) = writesOtherThan fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [writesOtherThan, ih]

theorem Echo.exitsIn {count : Nat} {s : InputStream} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : Echo count s trace outcome) : Omni.ExitsIn [0] trace outcome := by
  cases post with
  | atEof _ halted unkilled => exact ⟨0, halted, List.mem_singleton_self _, unkilled⟩
  | echoed _ _ halted unkilled => exact ⟨0, halted, List.mem_singleton_self _, unkilled⟩

theorem Echo.echo {count : Nat} {s : InputStream} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : Echo count s trace outcome) : TraceSpec.echo.denote trace := by
  cases post with
  | atEof => exact ⟨List.nil_prefix, rfl⟩
  | echoed _ delivered =>
    rw [List.append_assoc]
    refine ⟨?_, ?_⟩
    · rw [written_reads, written_writes, readFrom_reads, readFrom_writes]
      simpa [written, readFrom] using delivered.2
    · rw [writesOtherThan_reads, writesOtherThan_writes]
      rfl

/-- Every execution echoes some stdin stream: the launch-independent form of the
postconditions. -/
def EchoSome (count : Nat) : Omni.Post x86ExtNative := fun trace outcome => ∃ s, Echo count s trace outcome

theorem readEcho_exec_some (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadEcho.probe en inp) :
    Omni.Exec Data.ReadEcho.probe.segs spec noFilter (Data.ReadEcho.probe.launchedAt en inp).initial
      (EchoSome 16) :=
  (readEcho_exec en inp launch).consequence fun _ _ post => ⟨_, post⟩

theorem readEcho2_exec_some (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.ReadEcho2.probe en inp) :
    Omni.Exec Data.ReadEcho2.probe.segs spec noFilter (Data.ReadEcho2.probe.launchedAt en inp).initial
      (EchoSome 2) :=
  (readEcho2_exec en inp launch).consequence fun _ _ post => ⟨_, post⟩

theorem EchoSome.exitsIn {count : Nat} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : EchoSome count trace outcome) : Omni.ExitsIn [0] trace outcome :=
  Echo.exitsIn trace outcome post.choose_spec

theorem EchoSome.echo {count : Nat} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : EchoSome count trace outcome) : TraceSpec.echo.denote trace :=
  Echo.echo trace outcome post.choose_spec

end Silmaril.Process.LPS.Problems.X86Probes
