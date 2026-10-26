module

public import Silmaril.Process.CLI.Sha256Cli.EmptyReadUniversal
public import Silmaril.Process.CLI.Sha256Cli.ReadTransfer

/-! # Shared actual read-counter arithmetic through the full-buffer comparison

Six real instructions update the fill, modular total, capacity and pointer.
The boundary permits exactly 64 bytes; selecting the retry or compression
branch is separate. No syscall effects or buffer bytes are assumed here.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ReadAdvance

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

/-- State immediately before the actual full-buffer conditional branch. -/
def countCore (c : Core) (fill amount : Nat) : Core :=
  { ((((c.write .r8 (BitVec.ofNat 64 (fill + amount))).write .rdx 64).write
      .rbx (c.read .rbx + BitVec.ofNat 64 amount)).write
        .rdx (BitVec.ofNat 64 (64 - (fill + amount)))).write
          .rsi (BitVec.ofNat 64 (0x401620 + (fill + amount))) with
    rip := 0x40019c,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (fill + amount)) (64 : Word) }

private theorem capacity_word {filled : Nat} (bound : filled ≤ 64) :
    (64 : Word) - BitVec.ofNat 64 filled = BitVec.ofNat 64 (64 - filled) := by
  exact BitVec.ofNat_sub_ofNat_of_le 64 filled (by omega) (by omega)

private theorem pointer_word (filled : Nat) :
    BitVec.ofNat 64 filled + (0x401620 : Word) =
      BitVec.ofNat 64 (0x401620 + filled) := by
  change BitVec.ofNat 64 filled + BitVec.ofNat 64 0x401620 = _
  rw [BitVec.ofNat_add_ofNat, Nat.add_comm]

set_option maxRecDepth 10000 in
/-- The common arithmetic prefix covers a full input buffer as well as tails. -/
theorem counters (c : Core) (s : Syscall.State) (fill amount : Nat)
    (bound : fill + amount ≤ 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400185) (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨countCore c fill amount, s⟩ := by
  let c1 : Core := { c.write .r8 (BitVec.ofNat 64 (fill + amount)) with
    rip := 0x400188,
    flags := X86.Ext.addFlagsN (BitVec.ofNat 64 fill) (BitVec.ofNat 64 amount) }
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨c1, s⟩ := by
    apply Output.retire (entry := Binary.i_400185) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400185])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400185, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, c1, pc, rax, r8, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    exact congrArg (fun value : Word => Machine.RegisterFile.write c.regs .r8 value)
      (BitVec.ofNat_add_ofNat fill amount)
  let c2 : Core := { c1.write .rdx 64 with rip := 0x40018b }
  have b : Proc.Step X86Linux.isa Env.linux (⟨c1, s⟩ : Output.PS) [] ⟨c2, s⟩ := by
    apply Output.retire (entry := Binary.i_400188) (by simp [Binary.transcript]) intact running rfl
    have value : c1.read .rbp = 64 := by change c.read .rbp = _; exact rbp
    simp [Entry.denote, X86Linux.execResult, Binary.i_400188, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire, c2, value]
    rfl
  let c3 : Core := { c2.write .rbx (c.read .rbx + BitVec.ofNat 64 amount) with
    rip := 0x40018e,
    flags := X86.Ext.addFlagsN (c.read .rbx) (BitVec.ofNat 64 amount) }
  have d : Proc.Step X86Linux.isa Env.linux (⟨c2, s⟩ : Output.PS) [] ⟨c3, s⟩ := by
    apply Output.retire (entry := Binary.i_40018b) (by simp [Binary.transcript]) intact running rfl
    have amountEq : c2.read .rax = BitVec.ofNat 64 amount := by change c.read .rax = _; exact rax
    have totalEq : c2.read .rbx = c.read .rbx := rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40018b, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, c3, amountEq, totalEq]
    constructor <;> rfl
  let c4 : Core := { c3.write .rdx (BitVec.ofNat 64 (64 - (fill + amount))) with
    rip := 0x400191,
    flags := X86.Ext.subFlagsN (64 : Word) (BitVec.ofNat 64 (fill + amount)) }
  have e : Proc.Step X86Linux.isa Env.linux (⟨c3, s⟩ : Output.PS) [] ⟨c4, s⟩ := by
    apply Output.retire (entry := Binary.i_40018e) (by simp [Binary.transcript]) intact running rfl
    have countEq : c3.read .rdx = 64 := rfl
    have fillEq : c3.read .r8 = BitVec.ofNat 64 (fill + amount) := rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40018e, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, c4, countEq, fillEq]
    constructor
    · dsimp +instances only [X86.Ext.Sz.bits]
      exact congrArg (fun value : Word => Machine.RegisterFile.write c3.regs .rdx value)
        (capacity_word bound)
    · rfl
  let c5 : Core := { c4.write .rsi (BitVec.ofNat 64 (0x401620 + (fill + amount))) with
    rip := 0x400198 }
  have f : Proc.Step X86Linux.isa Env.linux (⟨c4, s⟩ : Output.PS) [] ⟨c5, s⟩ := by
    apply Output.retire (entry := Binary.i_400191) (by simp [Binary.transcript]) intact running rfl
    have fillEq : c4.read .r8 = BitVec.ofNat 64 (fill + amount) := rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400191, X86.Ext.exec,
      X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value, X86.Ext.Sz.write,
      X86.Ext.retire, c5, fillEq]
    constructor
    · exact congrArg (fun value : Word => (c4.write .rsi value).regs) (pointer_word (fill + amount))
    · rfl
  let c6 : Core := { c5 with
    rip := 0x40019c,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (fill + amount)) (64 : Word) }
  have g : Proc.Step X86Linux.isa Env.linux (⟨c5, s⟩ : Output.PS) [] ⟨c6, s⟩ := by
    apply Output.retire (entry := Binary.i_400198) (by simp [Binary.transcript]) intact running rfl
    have fillEq : c5.read .r8 = BitVec.ofNat 64 (fill + amount) := rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400198, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, X86.Ext.AluOp.flagsN, c6, fillEq]
    rfl
  simpa only [c6, c5, c4, c3, c2, c1, countCore, X86.State.write, List.nil_append] using
    (Silmaril.Machine.Trace.Runs.cons a (.cons b (.cons d (.cons e (.cons f (.single g))))))

end Silmaril.Process.CLI.Sha256Cli.ReadAdvance
