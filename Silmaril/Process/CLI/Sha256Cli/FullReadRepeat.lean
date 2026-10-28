module

public import Silmaril.Process.CLI.Sha256Cli.FullRead

/-! # A full return from the repeated read

The actual TEST/JE/TEST/JS path retains the accumulated total and reaches the
shared full-buffer counter path. It does not repeat the first-read setup.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullReadRepeat

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 10000 in
theorem to_call (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = 64)
    (r8 : c.read .r8 = 0) (rbp : c.read .rbp = 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨FullRead.callCore c 0 64, s⟩ := by
  let tested : Core := { c with rip := 0x40017a, flags := X86.Ext.logicFlagsN (64 : Word) }
  have test : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400177])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
  let checked : Core := { tested with rip := 0x40017c }
  have nonzero : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (64 : Word)) .e = some false := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec, checked, tested]
    erw [condition]
  let signed : Core := { checked with rip := 0x40017f, flags := X86.Ext.logicFlagsN (64 : Word) }
  have signTest : Proc.Step X86Linux.isa Env.linux (⟨checked, s⟩ : Output.PS) [] ⟨signed, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running rfl
    have amount : c.regs .rax = 64 := rax
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, signed, checked, tested,
      X86.State.read, amount]
  let positive : Core := { signed with rip := 0x400185 }
  have signBranch : Proc.Step X86Linux.isa Env.linux (⟨signed, s⟩ : Output.PS) [] ⟨positive, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    have condition : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (64 : Word)) .s = some false := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec, positive, signed]
    erw [condition]
  have full := FullRead.advance positive s 0 64 rfl running intact rfl rax r8 rbp
  simpa only [List.nil_append, FullRead.callCore, ReadAdvance.countCore,
    positive, signed, checked, tested, X86.State.write, X86.State.read] using
      (Silmaril.Machine.Trace.Runs.cons test (.cons nonzero (.cons signTest (.single signBranch)))).append full

end Silmaril.Process.CLI.Sha256Cli.FullReadRepeat
