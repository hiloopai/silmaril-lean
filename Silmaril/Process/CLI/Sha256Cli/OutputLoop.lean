module

public import Silmaril.Process.CLI.Sha256Cli.OutputTransfer
public import Silmaril.X86.Ext.Loop

/-! # Checked output-loop instruction segments

These are actual silent instruction paths. They retain arbitrary syscall R11
and cover every accepted count, including zero, without a progress assumption.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputLoop

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open OutputTransfer

set_option maxRecDepth 10000

/-- Register invariant at the real write syscall. No restriction on R11. -/
structure Ready (c : Core) (off : Fin 65) : Prop where
  pc : c.rip = 0x4002a9
  number : c.read .rax = 1
  fd : c.read .rdi = 1
  pointer : c.read .rsi = BitVec.ofNat 64 (address off)
  size : c.read .rdx = BitVec.ofNat 64 (remaining off)
  offset : c.read .r8 = BitVec.ofNat 64 off.val
  total : c.read .r9 = 65

theorem request_ready (c : Core) (off : Fin 65) : Ready (requestCore c off) off := by
  constructor <;> simp [requestCore, X86.State.read, X86.State.write,
    Machine.RegisterFile.write]

def trapped (c : Core) : Core := { c with rip := 0x4002ab }
def returned (c : Core) (result : Result) (flags : Word) : Core :=
  ((((trapped c).write .rax (resultWord result)).write .rcx 0x4002ab).write .r11 flags)
def tested (c : Core) (result : Result) (flags : Word) : Core :=
  { returned c result flags with rip := 0x4002ae, flags := X86.Ext.logicFlagsN (resultWord result) }
def positive (c : Core) (result : Result) (flags : Word) : Core :=
  { tested c result flags with rip := 0x400290 }
def rejected (c : Core) (result : Result) (flags : Word) : Core :=
  { tested c result flags with rip := 0x4002b0 }
def failure (c : Core) (result : Result) (flags : Word) : Core :=
  { (rejected c result flags).write .rax 60 with rip := 0x4002b5 }

theorem jg_ok (count : Nat) (bound : count ≤ 65) :
    X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord (.ok count))) =
      some (decide (0 < count)) := by
  have small : count < 2 ^ 64 := by omega
  have sign : (BitVec.ofNat 64 count).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    simp only [decide_eq_false_iff_not]
    omega
  have zero : (BitVec.ofNat 64 count == 0#64) = decide (count = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      change count % 2 ^ 64 = 0 at this
      rwa [Nat.mod_eq_of_lt small] at this
    · rintro rfl
      rfl
  by_cases h : count = 0
  · subst count
    decide
  · have nz : decide (count = 0) = false := by simp [h]
    have pos : decide (0 < count) = true := by simp; omega
    simp only [resultWord, X86.Ext.Cond.eval, X86.Ext.logicFlagsN,
      X86.Ext.kNot, X86.Ext.kOr, X86.Ext.kXor, X86.Ext.isZeroN, sign, zero, nz, pos]
    rfl

theorem jg_error (errno : Errno) :
    X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord (.error errno))) = some false := by
  have sign : (resultWord (.error errno)).msb = true := by
    rw [BitVec.msb_eq_decide]
    simp only [resultWord, BitVec.toNat_ofInt, decide_eq_true_eq]
    have := errno.positive
    have := errno.bounded
    omega
  simp only [X86.Ext.Cond.eval, X86.Ext.logicFlagsN, X86.Ext.kNot, X86.Ext.kOr,
    X86.Ext.kXor, sign]
  cases X86.Ext.isZeroN (resultWord (.error errno)) <;> rfl

theorem test_step (c : Core) (result : Result) (flags : Word) (s : Syscall.State)
    (intact : Output.Intact s.memory) (running : s.exited = none) :
    Proc.Step X86Linux.isa Env.linux (⟨returned c result flags, s⟩ : Output.PS) []
      ⟨tested c result flags, s⟩ := by
  apply Output.retire (entry := Binary.i_4002ab) (by simp [Binary.transcript]) intact running
  · rfl
  · simp [Entry.denote, X86Linux.execResult, Binary.i_4002ab, X86.Ext.exec, X86.Ext.readRM,
      X86.Ext.Sz.read, X86.Ext.retire, returned, trapped, tested,
      X86.State.read, X86.State.write, Machine.RegisterFile.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    rw [BitVec.and_self]

theorem branch_positive (c : Core) (count : Nat) (flags : Word) (s : Syscall.State)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (nonzero : 0 < count) (bound : count ≤ 65) :
    Proc.Step X86Linux.isa Env.linux (⟨tested c (.ok count) flags, s⟩ : Output.PS) []
      ⟨positive c (.ok count) flags, s⟩ := by
  apply Output.retire (entry := Binary.i_4002ae) (by simp [Binary.transcript]) intact running
  · rfl
  · have taken := jg_ok count bound
    simp only [nonzero, decide_true] at taken
    simp [Entry.denote, X86Linux.execResult, Binary.i_4002ae, X86.Ext.exec, tested, positive]
    erw [taken]

theorem branch_rejected (c : Core) (result : Result) (flags : Word) (s : Syscall.State)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (notPositive : X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord result)) = some false) :
    Proc.Step X86Linux.isa Env.linux (⟨tested c result flags, s⟩ : Output.PS) []
      ⟨rejected c result flags, s⟩ := by
  apply Output.retire (entry := Binary.i_4002ae) (by simp [Binary.transcript]) intact running
  · rfl
  · simp [Entry.denote, X86Linux.execResult, Binary.i_4002ae, X86.Ext.exec, tested, rejected]
    erw [notPositive]

theorem rejection (c : Core) (result : Result) (flags : Word) (s : Syscall.State)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (notPositive : X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord result)) = some false) :
    Proc.Runs X86Linux.isa Env.linux (⟨returned c result flags, s⟩ : Output.PS) []
      ⟨failure c result flags, s⟩ := by
  have last : Proc.Step X86Linux.isa Env.linux (⟨rejected c result flags, s⟩ : Output.PS) []
      ⟨failure c result flags, s⟩ := by
    apply Output.retire (entry := Binary.i_4002b0) (by simp [Binary.transcript]) intact running
    · rfl
    · rfl
  exact .cons (test_step c result flags s intact running)
    (.cons (branch_rejected c result flags s intact running notPositive) (.single last))

end Silmaril.Process.CLI.Sha256Cli.OutputLoop
