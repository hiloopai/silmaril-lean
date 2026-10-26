module

public import Silmaril.Process.CLI.Sha256Cli.ShortRead

/-! # Real return branches into the short-input counter loop

The positive return checks, initial register setup and repeated-read branches
use the actual checked instructions. They retain arbitrary syscall R11 values,
all memory and the stack pointer. Input/copy evidence is handled separately.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortReadBranches

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

private theorem positive_conditions {amount : Nat} (positive : 0 < amount) (bound : amount < 64) :
    X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 amount)) .e = some false ∧
      X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 amount)) .s = some false := by
  have all : ∀ index : Fin 63,
      X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 (index.val + 1))) .e = some false ∧
        X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 (index.val + 1))) .s = some false := by decide
  have index : amount - 1 < 63 := by omega
  have restored : amount - 1 + 1 = amount := by omega
  simpa only [restored] using all ⟨amount - 1, index⟩

set_option maxRecDepth 10000 in
/-- TEST/JS establish the positive path, followed by the nine checked counter
and retry instructions. The completed return must leave the buffer below64. -/
theorem positive_common_below64 (c : Core) (s : Syscall.State) (fill amount : Nat)
    (positive : 0 < amount) (bound : fill + amount < 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40017c)
    (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨ShortRead.nextCore c fill amount, s⟩ := by
  let tested : Core := { c with
    rip := 0x40017f, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_40017c])
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let checked : Core := { tested with rip := 0x400185 }
  have last : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    have condition := (positive_conditions positive (by omega : amount < 64)).2
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec, checked, tested]
    erw [condition]
  have continued := ShortRead.advance_below64 checked s fill amount bound running intact rfl rax r8 rbp
  have combined := (Silmaril.Machine.Trace.Runs.cons first (.single last)).append continued
  simpa only [List.nil_append, ShortRead.nextCore, checked, tested, X86.State.write, X86.State.read] using combined

set_option maxRecDepth 10000 in
/-- Any positive repeated-read return takes the actual non-EOF branch, sign
check and counter path back to the next syscall. Thirteen retirements. -/
theorem positive_loop_below64 (c : Core) (s : Syscall.State) (fill amount : Nat)
    (positive : 0 < amount) (bound : fill + amount < 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177)
    (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨ShortRead.nextCore c fill amount, s⟩ := by
  let tested : Core := { c with
    rip := 0x40017a, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400177])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let checked : Core := { tested with rip := 0x40017c }
  have last : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running rfl
    have condition := (positive_conditions positive (by omega : amount < 64)).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec, checked, tested]
    erw [condition]
  have continued := positive_common_below64 checked s fill amount positive bound running intact rfl rax r8 rbp
  have combined := (Silmaril.Machine.Trace.Runs.cons first (.single last)).append continued
  simpa only [List.nil_append, ShortRead.nextCore, checked, tested, X86.State.write, X86.State.read] using combined

/-- The initial positive-read path resets the source's fill/total counters. -/
def initialCore (c : Core) : Core :=
  { ((c.write .r8 0).write .rbx 0).write .rbp 64 with
    rip := 0x40017c, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

set_option maxRecDepth 10000 in
theorem initial_setup (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory) (pc : c.rip = 0x400164) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨initialCore c, s⟩ := by
  let c1 : Core := { c.write .r8 0 with
    rip := 0x400167, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨c1, s⟩ := by
    apply Output.retire (entry := Binary.i_400164) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400164])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400164, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c1, pc, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let c2 : Core := { c1.write .rbx 0 with
    rip := 0x400169, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have b : Proc.Step X86Linux.isa Env.linux (⟨c1, s⟩ : Output.PS) [] ⟨c2, s⟩ := by
    apply Output.retire (entry := Binary.i_400167) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400167, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c2, c1, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let c3 : Core := { c2.write .rbp 64 with rip := 0x40016e }
  have d : Proc.Step X86Linux.isa Env.linux (⟨c2, s⟩ : Output.PS) [] ⟨c3, s⟩ := by
    apply Output.retire (entry := Binary.i_400169) (by simp [Binary.transcript]) intact running rfl
    rfl
  have e : Proc.Step X86Linux.isa Env.linux (⟨c3, s⟩ : Output.PS) [] ⟨initialCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_40016e) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons a (.cons b (.cons d (.single e)))

def firstNextCore (c : Core) (amount : Nat) : Core := ShortRead.nextCore (initialCore c) 0 amount

set_option maxRecDepth 10000 in
/-- The first positive read follows its genuine optimized setup before the
shared sign/counter path. Seventeen real retirements reach the repeated read. -/
theorem first_positive_below64 (c : Core) (s : Syscall.State) (amount : Nat)
    (positive : 0 < amount) (bound : amount < 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = BitVec.ofNat 64 amount) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨firstNextCore c amount, s⟩ := by
  let tested : Core := { c with
    rip := 0x40015e, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_40015b) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_40015b])
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015b, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let checked : Core := { tested with rip := 0x400164 }
  have second : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40015e) (by simp [Binary.transcript]) intact running rfl
    have condition := (positive_conditions positive bound).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_40015e, X86.Ext.exec, checked, tested]
    erw [condition]
  have setup := initial_setup checked s running intact rfl
  have continued := positive_common_below64 (initialCore checked) s 0 amount positive (by simpa using bound)
    running intact rfl rax rfl rfl
  have combined := (Silmaril.Machine.Trace.Runs.cons first (.single second)).append (setup.append continued)
  simpa only [List.nil_append, firstNextCore, initialCore, ShortRead.nextCore, checked, tested,
    X86.State.write] using combined

/-- Existing below56 APIs specialize the shared below64 instruction proofs. -/
theorem positive_common (c : Core) (s : Syscall.State) (fill amount : Nat)
    (positive : 0 < amount) (bound : fill + amount < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40017c) (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨ShortRead.nextCore c fill amount, s⟩ :=
  positive_common_below64 c s fill amount positive (by omega) running intact pc rax r8 rbp

theorem positive_loop (c : Core) (s : Syscall.State) (fill amount : Nat)
    (positive : 0 < amount) (bound : fill + amount < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = BitVec.ofNat 64 amount)
    (r8 : c.read .r8 = BitVec.ofNat 64 fill) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨ShortRead.nextCore c fill amount, s⟩ :=
  positive_loop_below64 c s fill amount positive (by omega) running intact pc rax r8 rbp

theorem first_positive (c : Core) (s : Syscall.State) (amount : Nat)
    (positive : 0 < amount) (bound : amount < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40015b) (rax : c.read .rax = BitVec.ofNat 64 amount) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨firstNextCore c amount, s⟩ :=
  first_positive_below64 c s amount positive (by omega) running intact pc rax

end Silmaril.Process.CLI.Sha256Cli.ShortReadBranches
