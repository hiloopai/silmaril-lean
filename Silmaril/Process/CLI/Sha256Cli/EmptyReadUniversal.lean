module

public import Silmaril.Process.CLI.Sha256Cli.Eof
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame
public import Silmaril.Process.CLI.X86Linux.SilentTransport
public import Silmaril.Process.CLI.X86Linux.SyscallInversion

/-! # Every admitted first read on empty input

The successful case is genuine positive-count EOF, with the entire environment
unchanged. Errors may clobber the requested block; their exact frame retains
the code, whose real error continuation exits with status 1. The statements
quantify all admitted syscall replies and keep arbitrary R11 resume values.
There is no promise that a call returns, or that any whole process terminates.

The silent completion transport is an explicit dependency on PR #3052. These
are decoded-byte/model theorems, not claims about unmodeled hardware effects.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.EmptyReadUniversal

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

/-- All returning read choices at EOF: success is exact EOF; errors consume
no unavailable byte and retain descriptors, but may alter their entire buffer. -/
theorem classify {before after : Syscall.State} {fd address count : Nat}
    {descriptor : Descriptor} {event : Event} {result : Result}
    (positive : 0 < count) (opened : before.descriptors fd = some descriptor)
    (readable : descriptor.readable = true)
    (eof : descriptor.input.byteAt descriptor.cursor = none)
    (effect : Syscall.Step before (.read fd address count) event (.returned result) after) :
    (result = .ok 0 ∧ event = .read fd [] ∧ after = before) ∨
      ∃ errno, result = .error errno ∧ event = .error (.read fd address count) errno ∧
        after.exited = none ∧ after.descriptors = before.descriptors := by
  cases effect with
  | readSome _ other _ input nonempty _ _ _ _ =>
    have same := Option.some.inj (other.symm.trans opened)
    subst same
    have first := input 0 nonempty
    simp only [Nat.add_zero, eof] at first
    contradiction
  | readEof => exact Or.inl ⟨rfl, rfl, rfl⟩
  | readZero => omega
  | @readError fd address count consumed other memory errno running openOther
      mode accessible bounded available frame backed =>
    have same := Option.some.inj (openOther.symm.trans opened)
    subst same
    have consumedZero : consumed = 0 := by
      by_contra nonzero
      have first := available 0 (by omega)
      simp only [Nat.add_zero, eof, Option.isSome_none, Bool.false_eq_true] at first
    refine Or.inr ⟨errno, rfl, rfl, running, ?_⟩
    simp only [State.setDescriptor, consumedZero, Nat.add_zero]
    exact Function.update_eq_self_iff.mpr opened.symm
  | readBadDescriptor running invalid =>
    exact False.elim (invalid (by simp [opened, readable]))
  | readBadAddress running invalid => exact Or.inr ⟨_, rfl, rfl, running, rfl⟩

/-- The concrete first-read request has positive count 64. -/
def readRequest : Request := .read 0 0x401620 64

/-- All permitted syscall resumes, including arbitrary R11. -/
def returnedCore (c : Core) (result : Result) (flags : Word) : Core :=
  ((({ Eof.readCore c with rip := 0x40015b }).write .rax (resultWord result)).write
    .rcx 0x40015b).write .r11 flags

@[simp] theorem returned_pc (c : Core) (result : Result) (flags : Word) :
    (returnedCore c result flags).rip = 0x40015b := rfl

@[simp] theorem returned_rax (c : Core) (result : Result) (flags : Word) :
    (returnedCore c result flags).read .rax = resultWord result := by
  simp [returnedCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

@[simp] theorem returned_rsp (c : Core) (result : Result) (flags : Word) :
    (returnedCore c result flags).read .rsp = c.read .rsp := by
  simp [returnedCore, Eof.readCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

theorem error_word_toInt (errno : Errno) :
    (resultWord (.error errno)).toInt = -(errno.value : Int) := by
  have positive := errno.positive
  have bounded := errno.bounded
  exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

theorem error_word_nonzero (errno : Errno) : resultWord (.error errno) ≠ (0 : Word) := by
  intro zero
  have value := congrArg (fun word : Word => word.toInt) zero
  rw [error_word_toInt] at value
  change -(errno.value : Int) = 0 at value
  have := errno.positive
  omega

theorem error_word_msb (errno : Errno) : (resultWord (.error errno)).msb = true := by
  cases flag : (resultWord (.error errno)).msb with
  | false =>
    have nonnegative := BitVec.toInt_nonneg_of_msb_false flag
    rw [error_word_toInt] at nonnegative
    have := errno.positive
    omega
  | true => rfl

/-- Every Linux errno is nonzero and negative in the actual TEST conditions. -/
theorem error_conditions (errno : Errno) :
    X86.Ext.Cond.eval (X86.Ext.logicFlagsN (resultWord (.error errno))) .e = some false ∧
      X86.Ext.Cond.eval (X86.Ext.logicFlagsN (resultWord (.error errno))) .s = some true := by
  simp [X86.Ext.Cond.eval, X86.Ext.logicFlagsN, X86.Ext.isZeroN,
    error_word_msb]

/-- The core at the real failure exit syscall. -/
def errorExitCore (c : Core) (errno : Errno) : Core :=
  { ((((c.write .r8 0).write .rbx 0).write .rbp 64).write .rax 60).write .rdi 1 with
    rip := 0x4002dd, flags := X86.Ext.logicFlagsN (resultWord (.error errno)) }

set_option maxRecDepth 10000 in
theorem errorExit_step (c : Core) (s : Syscall.State) (errno : Errno)
    (intact : Output.Intact s.memory) :
    X86Linux.step (errorExitCore c errno) s.memory =
      .syscall { errorExitCore c errno with rip := 0x4002df } :=
  step_of_entry Binary.ok_4002dd.1 rfl (intact _ (by simp [Binary.transcript]))

theorem errorExit_request (c : Core) (errno : Errno) :
    X86Linux.request { errorExitCore c errno with rip := 0x4002df } = some (.exit 1) := by
  simp [X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber, X86Linux.exitNumber,
    errorExitCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

set_option maxRecDepth 10000 in
/-- Every errno takes the actual ten-retirement error prefix to exit(1).
R11 and all untouched registers remain arbitrary; memory is unchanged. -/
theorem error_prefix (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = resultWord (.error errno)) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨errorExitCore c errno, s⟩ := by
  let c1 : Core := { c with
    rip := 0x40015e,
    flags := X86.Ext.logicFlagsN (resultWord (.error errno)) }
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨c1, s⟩ := by
    apply Output.retire (entry := Binary.i_40015b) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_40015b])
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015b, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, c1, pc, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let c2 : Core := { c1 with rip := 0x400164 }
  have b : Proc.Step X86Linux.isa Env.linux (⟨c1, s⟩ : Output.PS) [] ⟨c2, s⟩ := by
    apply Output.retire (entry := Binary.i_40015e) (by simp [Binary.transcript]) intact running rfl
    have condition := (error_conditions errno).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015e, X86.Ext.exec, c2, c1]
    erw [condition]
  let c3 : Core := { c2.write .r8 0 with
    rip := 0x400167, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have d : Proc.Step X86Linux.isa Env.linux (⟨c2, s⟩ : Output.PS) [] ⟨c3, s⟩ := by
    apply Output.retire (entry := Binary.i_400164) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400164, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c3, c2, c1, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let c4 : Core := { c3.write .rbx 0 with
    rip := 0x400169, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have e : Proc.Step X86Linux.isa Env.linux (⟨c3, s⟩ : Output.PS) [] ⟨c4, s⟩ := by
    apply Output.retire (entry := Binary.i_400167) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400167, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c4, c3, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let c5 : Core := { c4.write .rbp 64 with rip := 0x40016e }
  have f : Proc.Step X86Linux.isa Env.linux (⟨c4, s⟩ : Output.PS) [] ⟨c5, s⟩ := by
    apply Output.retire (entry := Binary.i_400169) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c6 : Core := { c5 with rip := 0x40017c }
  have g : Proc.Step X86Linux.isa Env.linux (⟨c5, s⟩ : Output.PS) [] ⟨c6, s⟩ := by
    apply Output.retire (entry := Binary.i_40016e) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c7 : Core := { c6 with
    rip := 0x40017f,
    flags := X86.Ext.logicFlagsN (resultWord (.error errno)) }
  have h : Proc.Step X86Linux.isa Env.linux (⟨c6, s⟩ : Output.PS) [] ⟨c7, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running rfl
    have value : c6.read .rax = resultWord (.error errno) := by
      change c.read .rax = _
      exact rax
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, c7, value]
    constructor
    · rfl
    · dsimp +instances only [X86.Ext.Sz.bits]
      simp only [BitVec.and_self]
  let c8 : Core := { c7 with rip := 0x4002d3 }
  have i : Proc.Step X86Linux.isa Env.linux (⟨c7, s⟩ : Output.PS) [] ⟨c8, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    have condition := (error_conditions errno).2
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec, c8, c7]
    erw [condition]
  let c9 : Core := { c8.write .rax 60 with rip := 0x4002d8 }
  have j : Proc.Step X86Linux.isa Env.linux (⟨c8, s⟩ : Output.PS) [] ⟨c9, s⟩ := by
    apply Output.retire (entry := Binary.i_4002d3) (by simp [Binary.transcript]) intact running rfl
    rfl
  have k : Proc.Step X86Linux.isa Env.linux (⟨c9, s⟩ : Output.PS) []
      ⟨errorExitCore c errno, s⟩ := by
    apply Output.retire (entry := Binary.i_4002d8) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons a (.cons b (.cons d (.cons e (.cons f (.cons g (.cons h (.cons i (.cons j (.single k)))))))))

/-- Every actual error frame preserves all checked driver instructions. -/
theorem intact_after_read {before after : Syscall.State} {event : Event} {result : Result}
    (intact : Output.Intact before.memory)
    (effect : Syscall.Step before readRequest event (.returned result) after) :
    Output.Intact after.memory := by
  have frame := effect.read_memory_frame
  intro entry member
  have bound := Output.code_end entry member
  exact (X86.Memory.readWith_writesOnly frame .execute entry.address entry.bytes.length
    (Or.inl (by omega))).trans (intact entry member)

/-- The two real EOF retirements keep the environment and arbitrary R11. -/
def eofPaddingCore (c : Core) : Core :=
  { c with rip := 0x4002b7, flags := X86.Ext.logicFlagsN (0 : Word) }

@[simp] theorem eofPaddingCore_rsp (c : Core) :
    (eofPaddingCore c).read .rsp = c.read .rsp := rfl

set_option maxRecDepth 10000 in
theorem eof_prefix (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = 0) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨eofPaddingCore c, s⟩ := by
  let tested : Core := { c with rip := 0x40015e, flags := X86.Ext.logicFlagsN (0 : Word) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_40015b) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_40015b])
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015b, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
  have last : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) []
      ⟨eofPaddingCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_40015e) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (0 : Word)) .e = some true := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015e, X86.Ext.exec, tested, eofPaddingCore]
    erw [condition]
  exact .cons first (.single last)

/-- Completion-only exclusion: after a first-read error, no completed process
execution can report successful exit 0. A call may still block or fail to
complete; the proof imposes no termination or prefix-output premise. -/
theorem no_success_after_error (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = resultWord (.error errno))
    {events : List Event} {final : Output.PS}
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final)
    (stopped : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) : False := by
  obtain ⟨continuation, stopped⟩ :=
    (X86Linux.completed_iff_of_silent (error_prefix c s errno running intact pc rax)).mp
      ⟨execution, stopped⟩
  have status := X86Linux.completed_exit running (errorExit_step c s errno intact)
    (errorExit_request c errno) continuation stopped
  have impossible : (0 : Nat) = 1 := status.2
  omega

/-- A nonvacuous admitted failure completion follows the same real error
prefix and exit syscall. The universal exclusion above does not depend on
choosing this particular completed execution. -/
theorem error_to_exit (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = resultWord (.error errno)) :
    ∃ final : Output.PS,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [.exit 1] final ∧
      Proc.Stop X86Linux.isa Env.linux final (.exited 1) := by
  let final : Output.PS :=
    ⟨{ errorExitCore c errno with rip := 0x4002df }, { s with exited := some 1 }⟩
  have last : Proc.Step X86Linux.isa Env.linux (⟨errorExitCore c errno, s⟩ : Output.PS)
      [.exit 1] final := by
    apply Proc.Step.exit (q := .exit 1) running
    · exact (errorExit_step c s errno intact).symm
    · exact errorExit_request c errno
    · exact Syscall.Step.exit 1 running
  exact ⟨final, by simpa only [List.nil_append] using
    (error_prefix c s errno running intact pc rax).append (.single last), .exited rfl⟩

end Silmaril.Process.CLI.Sha256Cli.EmptyReadUniversal
