module

public import Silmaril.Process.CLI.Sha256Cli.ShortReadBranches
public import Silmaril.Process.CLI.Sha256Cli.CompressionCallFrame

/-! # Actual full-buffer branch from read counters to compression

The shared counter prefix includes fill64. This module selects its real
fallthrough, supplies the two actual arguments, and covers the optimized first
read's 64-byte return. Memory, source frame and syscall effects are separate.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullRead

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def callCore (c : Core) (fill amount : Nat) : Core :=
  { ((ReadAdvance.countCore c fill amount).write .rsi 0x401620).write .rdi 0x401660 with
    rip := 0x4001a8 }

set_option maxRecDepth 10000 in
/-- Exactly filling the buffer follows the actual compression branch. -/
theorem advance (c : Core) (s : Syscall.State) (fill amount : Nat)
    (full : fill + amount = 64) (running : s.exited = none)
    (intact : Output.Intact s.memory) (pc : c.rip = 0x400185)
    (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨callCore c fill amount, s⟩ := by
  let counted := ReadAdvance.countCore c fill amount
  have arithmetic := ReadAdvance.counters c s fill amount (by omega) running intact pc rax r8 rbp
  let selected : Core := { counted with rip := 0x40019e }
  have branch : Proc.Step X86Linux.isa Env.linux (⟨counted, s⟩ : Output.PS) [] ⟨selected, s⟩ := by
    apply Output.retire (entry := Binary.i_40019c) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.subFlagsN (64 : Word) 64) .ne = some false := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40019c, X86.Ext.exec,
      selected, counted, ReadAdvance.countCore, full]
    erw [condition]
  let blockArg : Core := { selected.write .rsi 0x401620 with rip := 0x4001a3 }
  have block : Proc.Step X86Linux.isa Env.linux (⟨selected, s⟩ : Output.PS) [] ⟨blockArg, s⟩ := by
    apply Output.retire (entry := Binary.i_40019e) (by simp [Binary.transcript]) intact running rfl
    rfl
  have state : Proc.Step X86Linux.isa Env.linux (⟨blockArg, s⟩ : Output.PS) []
      ⟨callCore c fill amount, s⟩ := by
    apply Output.retire (entry := Binary.i_4001a3) (by simp [Binary.transcript]) intact running rfl
    rfl
  simpa only [List.nil_append] using arithmetic.append (.cons branch (.cons block (.single state)))

def firstCallCore (c : Core) : Core := callCore (ShortReadBranches.initialCore c) 0 64

set_option maxRecDepth 10000 in
/-- The optimized first read's actual 64-byte return reaches its full-block CALL.
No assumption about the source bytes or a successful callee is made here. -/
theorem first_to_call (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨firstCallCore c, s⟩ := by
  let tested : Core := { c with rip := 0x40015e, flags := X86.Ext.logicFlagsN (64 : Word) }
  have test : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_40015b) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_40015b])
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015b, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
  let checked : Core := { tested with rip := 0x400164 }
  have nonzero : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40015e) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (64 : Word)) .e = some false := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015e, X86.Ext.exec, checked, tested]
    erw [condition]
  have setup := ShortReadBranches.initial_setup checked s running intact rfl
  let initialized := ShortReadBranches.initialCore checked
  let signed : Core := { initialized with rip := 0x40017f, flags := X86.Ext.logicFlagsN (64 : Word) }
  have signTest : Proc.Step X86Linux.isa Env.linux (⟨initialized, s⟩ : Output.PS) [] ⟨signed, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running rfl
    have amount : c.regs .rax = 64 := rax
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, signed, initialized,
      ShortReadBranches.initialCore, checked, tested, X86.State.read, X86.State.write,
      Machine.RegisterFile.write, amount]
  let positive : Core := { signed with rip := 0x400185 }
  have signBranch : Proc.Step X86Linux.isa Env.linux (⟨signed, s⟩ : Output.PS) [] ⟨positive, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (64 : Word)) .s = some false := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec, positive, signed]
    erw [condition]
  have full := advance positive s 0 64 rfl running intact rfl rax rfl rfl
  simpa only [List.nil_append, firstCallCore, callCore, ReadAdvance.countCore,
    ShortReadBranches.initialCore, positive, signed, initialized, checked, tested,
    X86.State.write, X86.State.read] using
      (Silmaril.Machine.Trace.Runs.cons test (.single nonzero)).append
        (setup.append ((Silmaril.Machine.Trace.Runs.cons signTest (.single signBranch)).append full))

/-- The actual post-compression setup resets the buffer, retaining modular total. -/
def restartCore (c : Core) : Core :=
  { (((((c.write .rdx 64).write .rsi 0x401620).write .r8 0).write .rax 0).write .rdi 0) with
    rip := 0x400175, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

set_option maxRecDepth 10000 in
/-- Six actual return-path instructions reach a fresh positive-capacity read. -/
theorem restart (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = CompressionSite.fullBlock.returnAddress) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨restartCore c, s⟩ := by
  let count : Core := { c.write .rdx 64 with rip := 0x4001b2 }
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨count, s⟩ := by
    apply Output.retire (entry := Binary.i_4001ad) (by simp [Binary.transcript]) intact running
      (by rw [pc]; rfl)
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001ad, X86.Ext.exec,
      X86.Ext.Sz.write, X86.Ext.retire, count, pc,
      CompressionSite.returnAddress, CompressionSite.address]
  let block : Core := { count.write .rsi 0x401620 with rip := 0x4001b7 }
  have b : Proc.Step X86Linux.isa Env.linux (⟨count, s⟩ : Output.PS) [] ⟨block, s⟩ := by
    apply Output.retire (entry := Binary.i_4001b2) (by simp [Binary.transcript]) intact running rfl
    rfl
  let cleared : Core := { block.write .r8 0 with
    rip := 0x4001ba, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have d : Proc.Step X86Linux.isa Env.linux (⟨block, s⟩ : Output.PS) [] ⟨cleared, s⟩ := by
    apply Output.retire (entry := Binary.i_4001b7) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001b7, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, cleared, block]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let jumped : Core := { cleared with rip := 0x400170 }
  have e : Proc.Step X86Linux.isa Env.linux (⟨cleared, s⟩ : Output.PS) [] ⟨jumped, s⟩ := by
    apply Output.retire (entry := Binary.i_4001ba) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001ba, X86.Ext.exec,
      jumped, cleared]
  let number : Core := { jumped.write .rax 0 with
    rip := 0x400172, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have f : Proc.Step X86Linux.isa Env.linux (⟨jumped, s⟩ : Output.PS) [] ⟨number, s⟩ := by
    apply Output.retire (entry := Binary.i_400170) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400170, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, number, jumped]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  have g : Proc.Step X86Linux.isa Env.linux (⟨number, s⟩ : Output.PS) [] ⟨restartCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_400172) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons a (.cons b (.cons d (.cons e (.cons f (.single g)))))

theorem restart_ready (c : Core) (rbp : c.read .rbp = 64) :
    ShortRead.Ready (restartCore c) 0 (c.read .rbx) := by
  change c.regs .rbp = 64 at rbp
  constructor <;> simp [restartCore, X86.State.read, X86.State.write,
    Machine.RegisterFile.write, rbp]

@[simp] theorem restart_rsp (c : Core) : (restartCore c).read .rsp = c.read .rsp := by
  simp [restartCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

end Silmaril.Process.CLI.Sha256Cli.FullRead
