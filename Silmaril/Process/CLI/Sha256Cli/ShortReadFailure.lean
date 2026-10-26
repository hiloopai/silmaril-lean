module

public import Silmaril.Process.CLI.Sha256Cli.EmptyReadUniversal

/-! # Generic EOF and error continuations at the repeated read site

The input core and R11 remain arbitrary. EOF executes the actual TEST/JE pair
without changing any register or memory. Errors execute the six actual
retirements to exit1; no finite continuation can report exit0. No syscall
availability, termination, or new generic transport theorem is assumed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortReadFailure

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def paddingCore (c : Core) : Core :=
  { c with rip := 0x4001bc, flags := X86.Ext.logicFlagsN (0 : Word) }

@[simp] theorem padding_read (c : Core) (register : X86.Reg) :
    (paddingCore c).read register = c.read register := rfl

set_option maxRecDepth 10000 in
/-- Genuine returned zero reaches general padding in two actual retirements.
Input/EOF provenance belongs to the preceding admitted positive-count read. -/
theorem eof_prefix (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = 0) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨paddingCore c, s⟩ := by
  let tested : Core := { c with rip := 0x40017a, flags := X86.Ext.logicFlagsN (0 : Word) }
  have test : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400177])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
  have branch : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨paddingCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (0 : Word)) .e = some true := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec, tested, paddingCore]
    erw [condition]
  exact .cons test (.single branch)

def errorExitCore (c : Core) (errno : Errno) : Core :=
  { (c.write .rax 60).write .rdi 1 with rip := 0x4002dd, flags := X86.Ext.logicFlagsN (resultWord (.error errno)) }

@[simp] theorem errorExit_read (c : Core) (errno : Errno) (register : X86.Reg)
    (notResult : register ≠ .rax) (notArgument : register ≠ .rdi) :
    (errorExitCore c errno).read register = c.read register := by
  simp [errorExitCore, X86.State.read, X86.State.write, Machine.RegisterFile.write,
    notResult, notArgument]

set_option maxRecDepth 10000 in
/-- Every modeled errno skips EOF, takes JS, and sets exit1 in six actual
retirements. Memory and every register except RAX/RDI are preserved. -/
theorem error_prefix (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = resultWord (.error errno)) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨errorExitCore c errno, s⟩ := by
  let tested : Core :=
    { c with rip := 0x40017a, flags := X86.Ext.logicFlagsN (resultWord (.error errno)) }
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400177])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let nonzero : Core := { tested with rip := 0x40017c }
  have b : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨nonzero, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running rfl
    have condition := (EmptyReadUniversal.error_conditions errno).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec, nonzero, tested]
    erw [condition]
  let signed : Core := { nonzero with rip := 0x40017f }
  have d : Proc.Step X86Linux.isa Env.linux (⟨nonzero, s⟩ : Output.PS) [] ⟨signed, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, signed, nonzero, tested, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let failed : Core := { signed with rip := 0x4002d3 }
  have e : Proc.Step X86Linux.isa Env.linux (⟨signed, s⟩ : Output.PS) [] ⟨failed, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    have condition := (EmptyReadUniversal.error_conditions errno).2
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec,
      failed, signed, nonzero, tested]
    erw [condition]
  let numbered : Core := { failed.write .rax 60 with rip := 0x4002d8 }
  have f : Proc.Step X86Linux.isa Env.linux (⟨failed, s⟩ : Output.PS) [] ⟨numbered, s⟩ := by
    apply Output.retire (entry := Binary.i_4002d3) (by simp [Binary.transcript]) intact running rfl
    rfl
  have g : Proc.Step X86Linux.isa Env.linux (⟨numbered, s⟩ : Output.PS) [] ⟨errorExitCore c errno, s⟩ := by
    apply Output.retire (entry := Binary.i_4002d8) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons a (.cons b (.cons d (.cons e (.cons f (.single g)))))

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

/-- No finite successful completion can follow a repeated-read error. This
uses the actual instruction segment and shared exit inversion/transport. -/
theorem no_success_after_error (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = resultWord (.error errno))
    {events : List Event} {final : Output.PS}
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final)
    (stopped : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) : False := by
  obtain ⟨continuation, stopped⟩ :=
    (X86Linux.completed_iff_of_silent (error_prefix c s errno running intact pc rax)).mp
      ⟨execution, stopped⟩
  have impossible := (X86Linux.completed_exit running (errorExit_step c s errno intact)
    (errorExit_request c errno) continuation stopped).2
  omega

/-- The error branch is inhabited by an admitted actual exit1 run. -/
theorem error_to_exit (c : Core) (s : Syscall.State) (errno : Errno)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = resultWord (.error errno)) :
    ∃ final : Output.PS,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [.exit 1] final ∧
      Proc.Stop X86Linux.isa Env.linux final (.exited 1) := by
  let final : Output.PS :=
    ⟨{ errorExitCore c errno with rip := 0x4002df }, { s with exited := some 1 }⟩
  have last : Proc.Step X86Linux.isa Env.linux (⟨errorExitCore c errno, s⟩ : Output.PS) [.exit 1] final := by
    apply Proc.Step.exit (q := .exit 1) running
    · exact (errorExit_step c s errno intact).symm
    · exact errorExit_request c errno
    · exact Syscall.Step.exit 1 running
  exact ⟨final, by simpa only [List.nil_append] using
    (error_prefix c s errno running intact pc rax).append (.single last), .exited rfl⟩

end Silmaril.Process.CLI.Sha256Cli.ShortReadFailure
