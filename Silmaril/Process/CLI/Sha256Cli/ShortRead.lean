module

public import Silmaril.Process.CLI.Sha256Cli.ReadAdvance

/-! # The actual read loop for an input shorter than one final block

The counter/pointer arithmetic supports every positive return whose accumulated
fill remains below64. The original below56 APIs remain compatible wrappers. Read data, syscall choices
and stream-cursor evidence are separate premises until explicitly connected.
Nothing here assumes totality, favorable transfer lengths or clean errors.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortRead

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

/-- The exact next-request core after the source's counter/pointer updates.
The redundant RDX write follows the real instructions' order. -/
def nextCore (c : Core) (fill amount : Nat) : Core :=
  { (((((((c.write .r8 (BitVec.ofNat 64 (fill + amount))).write .rdx 64).write
      .rbx (c.read .rbx + BitVec.ofNat 64 amount)).write
        .rdx (BitVec.ofNat 64 (64 - (fill + amount)))).write
          .rsi (BitVec.ofNat 64 (0x401620 + (fill + amount)))).write .rax 0).write .rdi 0) with
    rip := 0x400175, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

/-- Local register premises at the actual repeated-read syscall. The total
counter is a word so its modular arithmetic is explicit. -/
structure Ready (c : Core) (fill : Nat) (total : Word) : Prop where
  pc : c.rip = 0x400175
  number : c.read .rax = 0
  stdin : c.read .rdi = 0
  address : c.read .rsi = BitVec.ofNat 64 (0x401620 + fill)
  capacity : c.read .rdx = BitVec.ofNat 64 (64 - fill)
  filled : c.read .r8 = BitVec.ofNat 64 fill
  total : c.read .rbx = total
  blockSize : c.read .rbp = 64

theorem next_ready (c : Core) (fill amount : Nat) (rbp : c.read .rbp = 64) :
    Ready (nextCore c fill amount) (fill + amount) (c.read .rbx + BitVec.ofNat 64 amount) := by
  change c.regs .rbp = 64 at rbp
  constructor <;>
    simp [nextCore, X86.State.read, X86.State.write, Machine.RegisterFile.write, rbp]

@[simp] theorem next_rsp (c : Core) (fill amount : Nat) :
    (nextCore c fill amount).read .rsp = c.read .rsp := by
  simp [nextCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

theorem Ready.request_below64 {c : Core} {fill : Nat} {total : Word}
    (ready : Ready c fill total) (bound : fill < 64) :
    X86Linux.request { c with rip := 0x400177 } =
      some (.read 0 (0x401620 + fill) (64 - fill)) ∧ 0 < 64 - fill := by
  have addressNat : (BitVec.ofNat 64 (0x401620 + fill)).toNat = 0x401620 + fill :=
    Nat.mod_eq_of_lt (by omega)
  have capacityNat : (BitVec.ofNat 64 (64 - fill)).toNat = 64 - fill :=
    Nat.mod_eq_of_lt (by omega)
  constructor
  · simp [X86Linux.request, X86Linux.readNumber, ready.number, ready.stdin,
      ready.address, ready.capacity, addressNat, capacityNat]
  · omega

/-- Compatibility specialization for existing short-message callers. -/
theorem Ready.request {c : Core} {fill : Nat} {total : Word}
    (ready : Ready c fill total) (bound : fill < 56) :
    X86Linux.request { c with rip := 0x400177 } =
      some (.read 0 (0x401620 + fill) (64 - fill)) ∧ 0 < 64 - fill :=
  ready.request_below64 (by omega)

private theorem continue_condition {filled : Nat} (bound : filled < 64) :
    X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 filled) (64 : Word)) .ne = some true := by
  have all : ∀ index : Fin 64,
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 index.val) (64 : Word))
        .ne = some true := by decide
  exact all ⟨filled, bound⟩

set_option maxRecDepth 10000 in
/-- Nine real instructions advance both counters, prepare the remaining
buffer suffix and branch to the next positive-capacity read. No buffer byte
or environment field changes in this internal segment. -/
theorem advance_below64 (c : Core) (s : Syscall.State) (fill amount : Nat)
    (bound : fill + amount < 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400185)
    (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨nextCore c fill amount, s⟩ := by
  let c6 := ReadAdvance.countCore c fill amount
  have counted := ReadAdvance.counters c s fill amount (by omega) running intact pc rax r8 rbp
  let c7 : Core := { c6 with rip := 0x400170 }
  have h : Proc.Step X86Linux.isa Env.linux (⟨c6, s⟩ : Output.PS) [] ⟨c7, s⟩ := by
    apply Output.retire (entry := Binary.i_40019c) (by simp [Binary.transcript]) intact running rfl
    have condition := continue_condition bound
    simp [Entry.denote, X86Linux.execResult, Binary.i_40019c, X86.Ext.exec, c7, c6, ReadAdvance.countCore]
    erw [condition]
  let c8 : Core := { c7.write .rax 0 with
    rip := 0x400172, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have i : Proc.Step X86Linux.isa Env.linux (⟨c7, s⟩ : Output.PS) [] ⟨c8, s⟩ := by
    apply Output.retire (entry := Binary.i_400170) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400170, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c8, c7, c6, ReadAdvance.countCore, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  have j : Proc.Step X86Linux.isa Env.linux (⟨c8, s⟩ : Output.PS) [] ⟨nextCore c fill amount, s⟩ := by
    apply Output.retire (entry := Binary.i_400172) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400172, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      c8, c7, c6, ReadAdvance.countCore, nextCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  simpa only [List.nil_append] using counted.append (.cons h (.cons i (.single j)))

/-- Compatibility specialization of the actual below64 continuation. -/
theorem advance (c : Core) (s : Syscall.State) (fill amount : Nat)
    (bound : fill + amount < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400185)
    (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨nextCore c fill amount, s⟩ :=
  advance_below64 c s fill amount (by omega) running intact pc rax r8 rbp

end Silmaril.Process.CLI.Sha256Cli.ShortRead
