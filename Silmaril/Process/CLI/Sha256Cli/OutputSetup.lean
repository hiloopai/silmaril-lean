module

public import Silmaril.Process.CLI.Sha256Cli.OutputFrame

/-! # The real newline store and first write request -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputSetup

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def afterNewline (c : Core) : Core := { c with rip := 0x400278 }
def cleared (c : Core) : Core :=
  { (afterNewline c).write .r8 0 with rip := 0x40027b, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
def stdoutCore (c : Core) : Core := { (cleared c).write .rdi 1 with rip := 0x400280 }
def sizeCore (c : Core) : Core := { (stdoutCore c).write .r9 65 with rip := 0x400286 }
def jumped (c : Core) : Core := { sizeCore c with rip := 0x400299 }
def countCore (c : Core) : Core := { (jumped c).write .rdx 65 with rip := 0x40029c }
def addressCore (c : Core) : Core := { (countCore c).write .rsi 0x4015c0 with rip := 0x4002a3 }
def numberCore (c : Core) : Core := { (addressCore c).write .rax 1 with rip := 0x4002a6 }
def prepared (c : Core) : Core :=
  { (numberCore c).write .rdx 65 with rip := 0x4002a9, flags := X86.Ext.subFlagsN (65 : Word) 0 }

theorem writeCore_prepared (c : Core) : Output.writeCore (prepared c) = prepared c := by
  apply Eq.mpr (X86.State.mk.injEq _ _ _ _ _ _ _ _)
  refine ⟨?_, rfl, rfl, rfl⟩
  funext register
  cases register <;> rfl

theorem expected_parts (message : List Byte) :
    (Sha256.expected message).take 64 ++ [0x0a] = Sha256.expected message := by
  have length : ((Silmaril.Crypto.SHA256.digest (message.map UInt8.ofBitVec)).flatMap
      Sha256.hexByte).length = 64 := by
    rw [Sha256.flatMap_hexByte_length, Silmaril.Crypto.SHA256.digest_length]
  simp only [Sha256.expected, List.take_append, length, Nat.sub_self, List.take_zero,
    List.append_nil]
  rw [List.take_of_length_le (by omega)]

set_option maxRecDepth 10000 in
theorem setup (c : Core) (s : Syscall.State) (message : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory) (pc : c.rip = 0x400271)
    (digits : s.memory.readBytes 0x4015c0 64 = some ((Sha256.expected message).take 64))
    (writable : s.memory.Permitted .write 0x401600 1)
    (readable : s.memory.Permitted .read 0x401600 1) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨prepared c, { s with memory := after }⟩ ∧
      after.readBytes 0x4015c0 65 = some (Sha256.expected message) ∧
      Output.Intact after ∧
      Memory.WritesWithin s.memory after (fun a => a = 0x401600) := by
  obtain ⟨after, stored, frame⟩ := X86.Ext.storeN_isSome
    (address := (0x401600 : Word)) (k := 1) (v := 0x0a) writable
  have oneByte : X86.Ext.leBytes (0x0a : Word) 1 = [0x0a] := rfl
  rw [oneByte] at frame
  have firstEffect : Binary.i_400271.denote c s.memory = .retired (afterNewline c) after := by
    change X86Linux.execResult (X86.Ext.retire (c.rip + 7)
      ((X86.Ext.storeN s.memory
        ((X86.Ext.Mem.ofRip 0x1388).addr c (c.rip + 7)) 1 (0x0a : Word)).map fun m => (c, m))) = _
    have addr : (X86.Ext.Mem.ofRip 0x1388).addr c (c.rip + 7) = (0x401600 : Word) := by
      simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value, pc]
    rw [addr, stored]
    simp [X86.Ext.retire, X86Linux.execResult, pc, afterNewline]
  have a : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) []
      ⟨afterNewline c, { s with memory := after }⟩ :=
    .retire running ((step_of_entry Binary.ok_400271.1
      (by simp [pc, Binary.i_400271]) (intact _ (by simp [Binary.transcript]))).trans firstEffect).symm
  have code : Output.Intact after := Output.intact_of_store intact frame (by decide)
  have b : Proc.Step X86Linux.isa Env.linux
      (⟨afterNewline c, { s with memory := after }⟩ : Output.PS) []
        ⟨cleared c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_400278)
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400278, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, cleared, afterNewline,
      X86.State.read, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  have d : Proc.Step X86Linux.isa Env.linux
      (⟨cleared c, { s with memory := after }⟩ : Output.PS) []
        ⟨stdoutCore c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_40027b)
      (by simp [Binary.transcript]) code running rfl
    rfl
  have e : Proc.Step X86Linux.isa Env.linux
      (⟨stdoutCore c, { s with memory := after }⟩ : Output.PS) []
        ⟨sizeCore c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_400280)
      (by simp [Binary.transcript]) code running rfl
    rfl
  have f : Proc.Step X86Linux.isa Env.linux
      (⟨sizeCore c, { s with memory := after }⟩ : Output.PS) []
        ⟨jumped c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_400286)
      (by simp [Binary.transcript]) code running rfl
    rfl
  have g : Proc.Step X86Linux.isa Env.linux
      (⟨jumped c, { s with memory := after }⟩ : Output.PS) []
        ⟨countCore c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_400299)
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400299, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      jumped, sizeCore, countCore, X86.State.read, X86.State.write]
  have h : Proc.Step X86Linux.isa Env.linux
      (⟨countCore c, { s with memory := after }⟩ : Output.PS) []
        ⟨addressCore c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_40029c)
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40029c, X86.Ext.exec,
      X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value, X86.Ext.Sz.write,
      X86.Ext.retire, addressCore, countCore, jumped, sizeCore, stdoutCore, cleared,
      X86.State.read, X86.State.write]
  have i : Proc.Step X86Linux.isa Env.linux
      (⟨addressCore c, { s with memory := after }⟩ : Output.PS) []
        ⟨numberCore c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_4002a3)
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4002a3, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      numberCore, addressCore, countCore, jumped, sizeCore, stdoutCore,
      X86.State.read, X86.State.write]
  have j : Proc.Step X86Linux.isa Env.linux
      (⟨numberCore c, { s with memory := after }⟩ : Output.PS) []
        ⟨prepared c, { s with memory := after }⟩ := by
    apply Output.retire (s := { s with memory := after }) (entry := Binary.i_4002a6)
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4002a6, X86.Ext.exec, X86.Ext.aluStep,
      X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, prepared, numberCore, addressCore,
      countCore, jumped, sizeCore, stdoutCore, cleared, X86.State.read, X86.State.write]
  have digitsAfter : after.readBytes 0x4015c0 64 = some ((Sha256.expected message).take 64) :=
    (frame.readWith_disjoint .read 0x4015c0 64 (Or.inl (by decide))).trans digits
  have newline : after.readBytes 0x401600 1 = some [0x0a] := frame.readWith_self readable
  have answer := Memory.readBytes_append digitsAfter newline
  rw [expected_parts] at answer
  refine ⟨after, .cons a (.cons b (.cons d (.cons e (.cons f (.cons g (.cons h (.cons i (.single j)))))))),
    answer, code, ?_⟩
  exact frame.writesWithin (by
    intro offset bound
    change offset < 1 at bound
    change (0x401600 : Nat) + offset = 0x401600
    omega)

end Silmaril.Process.CLI.Sha256Cli.OutputSetup
