module

public import Silmaril.Process.CLI.Sha256Cli.OutputLoop

/-! # Actual positive-write offset advancement and retry setup -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputLoop

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open OutputTransfer

set_option maxRecDepth 10000

def advanced (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (positive c (.ok count) flags).write .r8 (BitVec.ofNat 64 (off.val + count)) with
    rip := 0x400293, flags := X86.Ext.addFlagsN (BitVec.ofNat 64 off.val) (BitVec.ofNat 64 count) }
def compared (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { advanced c off count flags with rip := 0x400297, flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (off.val + count)) 64 }
def retry (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { compared c off count flags with rip := 0x400299 }
def totalLoaded (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (retry c off count flags).write .rdx 65 with rip := 0x40029c }
def pointerLoaded (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (totalLoaded c off count flags).write .rsi (BitVec.ofNat 64 (0x4015c0 + (off.val + count)))
    with rip := 0x4002a3 }
def numberLoaded (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (pointerLoaded c off count flags).write .rax 1 with rip := 0x4002a6 }
def nextRequest (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (numberLoaded c off count flags).write .rdx (BitVec.ofNat 64 (65 - (off.val + count)))
    with rip := 0x4002a9, flags := X86.Ext.subFlagsN 65 (BitVec.ofNat 64 (off.val + count)) }
def finished (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { compared c off count flags with rip := 0x4002ca }
def successNumber (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (finished c off count flags).write .rax 60 with rip := 0x4002cf }
def success (c : Core) (off : Fin 65) (count : Nat) (flags : Word) : Core :=
  { (successNumber c off count flags).write .rdi 0 with rip := 0x4002d1, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

theorem ja_count (total : Nat) (bound : total ≤ 65) :
    X86.Ext.Cond.a.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 total) 64) =
      some (decide (65 ≤ total)) := by
  rw [X86.Ext.eval_subFlagsN]
  simp only [X86.Ext.Cond.afterCmp, BitVec.ule_eq_decide, BitVec.toNat_ofNat]
  have small : total < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt small]
  apply congrArg some
  rw [Bool.eq_iff_iff]
  simp
  omega

theorem advance (c : Core) (off : Fin 65) (count : Nat) (flags : Word) (s : Syscall.State)
    (ready : Ready c off) (intact : Output.Intact s.memory) (running : s.exited = none)
    (nonzero : 0 < count) (fits : count ≤ remaining off) :
    Proc.Runs X86Linux.isa Env.linux (⟨returned c (.ok count) flags, s⟩ : Output.PS) []
      ⟨compared c off count flags, s⟩ := by
  have h8 : c.regs .r8 = BitVec.ofNat 64 off.val := ready.offset
  have add : Proc.Step X86Linux.isa Env.linux (⟨positive c (.ok count) flags, s⟩ : Output.PS) []
      ⟨advanced c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_400290) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400290, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
        X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, returned, trapped, tested, positive, advanced,
        resultWord, X86.State.read, X86.State.write, Machine.RegisterFile.write, h8]
      dsimp +instances only [X86.Ext.Sz.bits]
      rw [BitVec.ofNat_add]
  have cmp : Proc.Step X86Linux.isa Env.linux (⟨advanced c off count flags, s⟩ : Output.PS) []
      ⟨compared c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_400293) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400293, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, X86.Ext.AluOp.flagsN,
        advanced, compared, X86.State.read, X86.State.write, Machine.RegisterFile.write]
  exact .cons (test_step c (.ok count) flags s intact running)
    (.cons (branch_positive c count flags s intact running nonzero
      (fits.trans (Nat.sub_le 65 off.val))) (.cons add (.single cmp)))

theorem retry_ready (c : Core) (off : Fin 65) (count : Nat) (flags : Word)
    (ready : Ready c off) (unfinished : off.val + count < 65) :
    Ready (nextRequest c off count flags) ⟨off.val + count, unfinished⟩ := by
  have hd : c.regs .rdi = 1 := ready.fd
  have ht : c.regs .r9 = 65 := ready.total
  constructor <;> simp [nextRequest, numberLoaded, pointerLoaded, totalLoaded, retry,
    compared, advanced, positive, tested, returned, trapped, address, remaining,
    X86.State.read, X86.State.write, Machine.RegisterFile.write, hd, ht]

theorem retry_path (c : Core) (off : Fin 65) (count : Nat) (flags : Word) (s : Syscall.State)
    (ready : Ready c off) (intact : Output.Intact s.memory) (running : s.exited = none)
    (unfinished : off.val + count < 65) :
    Proc.Runs X86Linux.isa Env.linux (⟨compared c off count flags, s⟩ : Output.PS) []
      ⟨nextRequest c off count flags, s⟩ := by
  have hd : c.regs .rdi = 1 := ready.fd
  have ht : c.regs .r9 = 65 := ready.total
  have branch : Proc.Step X86Linux.isa Env.linux
      (⟨compared c off count flags, s⟩ : Output.PS) [] ⟨retry c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_400297) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken := ja_count (off.val + count) (by omega)
      simp only [show ¬ 65 ≤ off.val + count by omega, decide_false] at taken
      simp [Entry.denote, X86Linux.execResult, Binary.i_400297, X86.Ext.exec, compared, retry]
      erw [taken]
  have movTotal : Proc.Step X86Linux.isa Env.linux
      (⟨retry c off count flags, s⟩ : Output.PS) [] ⟨totalLoaded c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_400299) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400299, X86.Ext.exec,
        X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire, totalLoaded, retry,
        compared, advanced, positive, tested, returned, trapped,
        X86.State.read, X86.State.write, Machine.RegisterFile.write, ht]
  have lea : Proc.Step X86Linux.isa Env.linux
      (⟨totalLoaded c off count flags, s⟩ : Output.PS) [] ⟨pointerLoaded c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_40029c) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_40029c, X86.Ext.exec, X86.Ext.Mem.addr,
        X86.Ext.Mem.ofReg, X86.Ext.Base.value, X86.Ext.Sz.write, X86.Ext.retire,
        pointerLoaded, totalLoaded, retry, compared, advanced,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
      rw [← BitVec.ofNat_add]
      rw [Nat.add_comm (off.val + count) 0x4015c0]
  have movNum : Proc.Step X86Linux.isa Env.linux
      (⟨pointerLoaded c off count flags, s⟩ : Output.PS) [] ⟨numberLoaded c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_4002a3) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_4002a3, X86.Ext.exec,
        X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
        numberLoaded, pointerLoaded, totalLoaded, retry, compared, advanced, positive, tested,
        returned, trapped, X86.State.read, X86.State.write, Machine.RegisterFile.write, hd]
  have sub : Proc.Step X86Linux.isa Env.linux
      (⟨numberLoaded c off count flags, s⟩ : Output.PS) [] ⟨nextRequest c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_4002a6) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_4002a6, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
        X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, nextRequest, numberLoaded, pointerLoaded,
        totalLoaded, retry, compared, advanced,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
      dsimp +instances only [X86.Ext.Sz.bits]
      rw [BitVec.ofNat_sub_ofNat_of_le 65 (off.val + count) (by omega) (by omega)]
  exact .cons branch (.cons movTotal (.cons lea (.cons movNum (.single sub))))

theorem success_path (c : Core) (off : Fin 65) (count : Nat) (flags : Word) (s : Syscall.State)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (complete : off.val + count = 65) :
    Proc.Runs X86Linux.isa Env.linux (⟨compared c off count flags, s⟩ : Output.PS) []
      ⟨success c off count flags, s⟩ := by
  have branch : Proc.Step X86Linux.isa Env.linux
      (⟨compared c off count flags, s⟩ : Output.PS) [] ⟨finished c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_400297) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken := ja_count 65 (by decide)
      simp only [le_refl, decide_true] at taken
      simp [Entry.denote, X86Linux.execResult, Binary.i_400297, X86.Ext.exec, compared, finished,
        complete]
      erw [taken]
  have movNum : Proc.Step X86Linux.isa Env.linux
      (⟨finished c off count flags, s⟩ : Output.PS) [] ⟨successNumber c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_4002ca) (by simp [Binary.transcript]) intact running
    · rfl
    · rfl
  have zero : Proc.Step X86Linux.isa Env.linux
      (⟨successNumber c off count flags, s⟩ : Output.PS) [] ⟨success c off count flags, s⟩ := by
    apply Output.retire (entry := Binary.i_4002cf) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_4002cf, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
        X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, success, successNumber,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
      dsimp +instances only [X86.Ext.Sz.bits]
      simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  exact .cons branch (.cons movNum (.single zero))

end Silmaril.Process.CLI.Sha256Cli.OutputLoop
