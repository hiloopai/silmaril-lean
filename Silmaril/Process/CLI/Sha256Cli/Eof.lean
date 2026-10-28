module

public import Silmaril.Process.CLI.Sha256Cli.Output

/-! # The genuine positive-count EOF path into empty-message padding

The real read requests 64 bytes. The constructed admitted EOF keeps memory and
descriptors unchanged, and the real TEST/JE reach the empty padding branch.
This is an existence claim for an admitted EOF, not environment progress.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Eof

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def readCore (c : Core) : Core :=
  { (((c.write .rax 0).write .rdi 0).write .rsi 0x401620).write .rdx 64 with rip := 0x400159 }

def returned (c : Core) : Core :=
  ((({ readCore c with rip := 0x40015b }).write .rax 0).write .rcx 0x40015b).write .r11 0

def tested (c : Core) : Core :=
  { returned c with flags := X86.Ext.logicFlagsN (0 : Word), rip := 0x40015e }

def paddingCore (c : Core) : Core := { tested c with rip := 0x4002b7 }

set_option maxRecDepth 10000 in
theorem read_to_padding (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory) {descriptor : Descriptor}
    (stdinOpen : s.descriptors 0 = some descriptor) (readable : descriptor.readable = true)
    (eof : descriptor.input.byteAt descriptor.cursor = none)
    (writable : s.memory.Permitted .write 0x401620 64) :
    Proc.Runs X86Linux.isa Env.linux ⟨readCore c, s⟩ [.read 0 []] ⟨paddingCore c, s⟩ := by
  have read : Proc.Step X86Linux.isa Env.linux (⟨readCore c, s⟩ : Output.PS)
      [.read 0 []] ⟨returned c, s⟩ := by
    apply Proc.Step.call (q := .read 0 0x401620 64) (r := .ok 0) running
    · exact (step_of_entry Binary.ok_400159.1 rfl
        (intact _ (by simp [Binary.transcript]))).symm
    · simp [X86Linux.isa, X86Linux.request, X86Linux.readNumber, readCore,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
    · exact Syscall.Step.readEof running stdinOpen readable eof writable
    · exact ⟨0, rfl⟩
  have test : Proc.Step X86Linux.isa Env.linux (⟨returned c, s⟩ : Output.PS) [] ⟨tested c, s⟩ := by
    apply Output.retire (entry := Binary.i_40015b) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_40015b, X86.Ext.exec,
        X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, returned, readCore, tested,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have jump : Proc.Step X86Linux.isa Env.linux (⟨tested c, s⟩ : Output.PS) [] ⟨paddingCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_40015e) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (0 : Word)) .e = some true := by decide
      simp [Entry.denote, X86Linux.execResult, Binary.i_40015e, X86.Ext.exec, tested, paddingCore]
      erw [taken]
  exact .cons read (.cons test (.single jump))

/-- The observed empty read is backed by a genuine positive request. -/
theorem request_positive (c : Core) :
    X86Linux.request { readCore c with rip := 0x40015b } = some (.read 0 0x401620 64) ∧
      (0 : Nat) < 64 := by
  constructor
  · simp [X86Linux.request, X86Linux.readNumber, readCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write]
  · decide

end Silmaril.Process.CLI.Sha256Cli.Eof
