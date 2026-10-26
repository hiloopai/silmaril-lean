module

public import Silmaril.Process.CLI.Sha256Cli.Eof

/-! # The streaming read's positive-count EOF branch

The actual second read site uses the remaining capacity after a partial block.
This local machine segment preserves the buffer and reaches the general
padding entry. The caller still owes the fill/total/input-memory invariant;
this theorem neither assumes nor establishes a complete driver execution.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ReadTransfer

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def readCore (c : Core) (fill : Fin 64) : Core :=
  { (((((c.write .rax 0).write .rdi 0).write .rsi
      (BitVec.ofNat 64 (0x401620 + fill.val))).write .rdx
        (BitVec.ofNat 64 (64 - fill.val))).write .r8 (BitVec.ofNat 64 fill.val))
      with rip := 0x400175 }

def returned (c : Core) (fill : Fin 64) : Core :=
  ((({ readCore c fill with rip := 0x400177 }).write .rax 0).write .rcx 0x400177).write .r11 0

def tested (c : Core) (fill : Fin 64) : Core :=
  { returned c fill with flags := X86.Ext.logicFlagsN (0 : Word), rip := 0x40017a }

def paddingCore (c : Core) (fill : Fin 64) : Core :=
  { tested c fill with rip := 0x4001bc }

private theorem word_bounds : ∀ fill : Fin 64,
    (BitVec.ofNat 64 (0x401620 + fill.val)).toNat = 0x401620 + fill.val ∧
    (BitVec.ofNat 64 (64 - fill.val)).toNat = 64 - fill.val := by decide

/-- The EOF event comes from a strictly positive request, at the buffer's
remaining suffix. A zero-count read cannot satisfy this cut-point request. -/
theorem request_positive (c : Core) (fill : Fin 64) :
    X86Linux.request { readCore c fill with rip := 0x400177 } =
      some (.read 0 (0x401620 + fill.val) (64 - fill.val)) ∧ 0 < 64 - fill.val := by
  constructor
  · simp [X86Linux.request, X86Linux.readNumber, readCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write, (word_bounds fill).1,
      (word_bounds fill).2]
  · have := fill.isLt
    omega

set_option maxRecDepth 10000 in
/-- The real read/TEST/JE sequence reaches the supplied-prefix padding path.
No input or buffer byte changes on genuine EOF. -/
theorem eof_to_padding (c : Core) (s : Syscall.State) (fill : Fin 64)
    (running : s.exited = none) (intact : Output.Intact s.memory) {descriptor : Descriptor}
    (stdinOpen : s.descriptors 0 = some descriptor) (readable : descriptor.readable = true)
    (eof : descriptor.input.byteAt descriptor.cursor = none)
    (writable : s.memory.Permitted .write (0x401620 + fill.val) (64 - fill.val)) :
    Proc.Runs X86Linux.isa Env.linux ⟨readCore c fill, s⟩ [.read 0 []]
      ⟨paddingCore c fill, s⟩ := by
  have read : Proc.Step X86Linux.isa Env.linux (⟨readCore c fill, s⟩ : Output.PS)
      [.read 0 []] ⟨returned c fill, s⟩ := by
    apply Proc.Step.call (q := .read 0 (0x401620 + fill.val) (64 - fill.val)) (r := .ok 0) running
    · exact (step_of_entry Binary.ok_400175.1 rfl
        (intact _ (by simp [Binary.transcript]))).symm
    · exact (request_positive c fill).1
    · exact Syscall.Step.readEof running stdinOpen readable eof writable
    · exact ⟨0, rfl⟩
  have test : Proc.Step X86Linux.isa Env.linux (⟨returned c fill, s⟩ : Output.PS) []
      ⟨tested c fill, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
        X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, returned, readCore, tested,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have branch : Proc.Step X86Linux.isa Env.linux (⟨tested c fill, s⟩ : Output.PS) []
      ⟨paddingCore c fill, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (0 : Word)) .e = some true := by decide
      simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec,
        tested, paddingCore]
      erw [taken]
  exact .cons read (.cons test (.single branch))

theorem padding_fill (c : Core) (fill : Fin 64) :
    (paddingCore c fill).read .r8 = BitVec.ofNat 64 fill.val := by rfl

theorem padding_total (c : Core) (fill : Fin 64) :
    (paddingCore c fill).read .rbx = c.read .rbx := by
  simp [paddingCore, tested, returned, readCore, X86.State.read, X86.State.write,
    Machine.RegisterFile.write]

end Silmaril.Process.CLI.Sha256Cli.ReadTransfer
