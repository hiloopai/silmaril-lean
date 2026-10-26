module

public import Silmaril.Process.CLI.Sha256Cli.PaddingShort
public import Silmaril.Process.CLI.Sha256Cli.SingleBlockReference

/-! # The actual bit-length serialization instructions

The five real instructions shift the caller's 64-bit total, set compression
arguments, reverse the word and store its eight bytes. The word-level theorem
retains wrapping arithmetic. Its short-input corollary identifies the bytes
with the existing canonical padding, for every message length below 56.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LengthStore

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Padding (blockAddress)

def swapped (total : Word) : Word := X86.Ext.byteSwap64 (total <<< 3)
def encoded (total : Word) : List Byte := X86.Ext.leBytes (swapped total) 8

theorem encoded_length (total : Word) : (encoded total).length = 8 :=
  X86.Ext.length_leBytes _ _

def callCore (c : Core) (total : Word) : Core :=
  { ((c.write .rbx (swapped total)).write .rsi 0x401620).write .rdi 0x401660 with
    rip := 0x400229, flags := X86.Ext.ShiftOp.shl.flags total 3 c.flags }

theorem arguments (c : Core) (total : Word) :
    (callCore c total).read .rsi = 0x401620 ∧
    (callCore c total).read .rdi = 0x401660 ∧
    (callCore c total).read .rsp = c.read .rsp := by
  simp [callCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

set_option maxRecDepth 10000 in
theorem store (c : Core) (s : Syscall.State) (total : Word) (prefixBytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400211) (rbx : c.read .rbx = total)
    (initialBytes : s.memory.readBytes blockAddress 56 = some prefixBytes)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨callCore c total, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some (prefixBytes ++ encoded total) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + 56 ≤ a ∧ a < blockAddress + 64) ∧ Output.Intact after := by
  let c1 : Core := { c.write .rbx (total <<< 3) with
    rip := 0x400215, flags := X86.Ext.ShiftOp.shl.flags total 3 c.flags }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨c1, s⟩ := by
    apply Output.retire (entry := Binary.i_400211) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400211])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400211, X86.Ext.exec,
      X86.Ext.Count.raw, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.ShiftOp.result,
      c1, pc, rbx, X86.State.write]
    rfl
  let c2 : Core := { c1.write .rsi 0x401620 with rip := 0x40021a }
  have second : Proc.Step X86Linux.isa Env.linux (⟨c1, s⟩ : Output.PS) [] ⟨c2, s⟩ := by
    apply Output.retire (entry := Binary.i_400215) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c3 : Core := { c2.write .rdi 0x401660 with rip := 0x40021f }
  have third : Proc.Step X86Linux.isa Env.linux (⟨c2, s⟩ : Output.PS) [] ⟨c3, s⟩ := by
    apply Output.retire (entry := Binary.i_40021a) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c4 : Core := { c3.write .rbx (swapped total) with rip := 0x400222 }
  have fourth : Proc.Step X86Linux.isa Env.linux (⟨c3, s⟩ : Output.PS) [] ⟨c4, s⟩ := by
    apply Output.retire (entry := Binary.i_40021f) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40021f, X86.Ext.exec,
      X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      c4, c3, c2, c1, X86.State.read, X86.State.write, swapped]
    rfl
  have permission : s.memory.Permitted .write 0x401658 8 :=
    X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide)
  obtain ⟨after, written, stored⟩ := X86.Ext.storeN_isSome
    (address := (0x401658 : Word)) (v := swapped total) permission
  rw [show X86.Ext.leBytes (swapped total) 8 = encoded total from rfl] at stored
  have lastEffect : Binary.i_400222.denote c4 s.memory =
      .retired { c4 with rip := 0x400229 } after := by
    simp [Entry.denote, X86Linux.execResult, Binary.i_400222, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.bytes,
      X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value,
      X86.Ext.retire, c4]
    erw [written]
    rfl
  have last : Proc.Step X86Linux.isa Env.linux (⟨c4, s⟩ : Output.PS) []
      ⟨{ c4 with rip := 0x400229 }, { s with memory := after }⟩ :=
    .retire running ((step_of_entry Binary.ok_400222.1 rfl
      (intact _ (by simp [Binary.transcript]))).trans lastEffect).symm
  have prefixRead : after.readBytes blockAddress 56 = some prefixBytes :=
    (stored.readWith_disjoint .read blockAddress 56 (Or.inl (by decide))).trans initialBytes
  have lastPermission : s.memory.Permitted .read 0x401658
      (encoded total).length := by
    simpa only [encoded_length] using
      (X86.Ext.Memory.Permitted.sub readable (start := 0x401658) (len := 8)
        (by decide) (by decide) (by decide))
  have lastRead : after.readBytes (blockAddress + 56) 8 = some (encoded total) := by
    change after.readWith .read (0x401658 : Word).toNat 8 = _
    simpa only [encoded_length] using stored.readWith_self lastPermission
  have fullRead : after.readBytes blockAddress 64 = some (prefixBytes ++ encoded total) :=
    @Memory.readBytes_append after blockAddress 56 8 prefixBytes (encoded total) prefixRead lastRead
  have endCore : { c4 with rip := 0x400229 } = callCore c total := by
    simp only [c1, c2, c3, c4, callCore, X86.State.write]
    congr 1
    funext register
    by_cases same : register = .rbx <;> simp [Machine.RegisterFile.write, same]
  refine ⟨after, ?_, fullRead, ?_,
    Output.intact_of_store intact stored (by decide)⟩
  · have run := Silmaril.Machine.Trace.Runs.cons first
      (.cons second (.cons third (.cons fourth (.single last))))
    simpa only [List.nil_append, endCore] using run
  · apply stored.writesWithin
    intro i hi
    simp only [encoded_length] at hi
    dsimp [blockAddress]
    omega

/-- An explicit bounded value certificate connects the actual word store to
the canonical big-endian bit-length field for every short input length. -/
theorem encoded_short : ∀ n : Fin 56,
    encoded (BitVec.ofNat 64 n.val) =
      (Silmaril.Crypto.natToBytesBE64 (n.val * 8)).map UInt8.toBitVec := by decide

/-- The real length store finishes the canonical single block; message and
zero-fill bytes must have been established by the preceding actual segment. -/
theorem short_block (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400211) (rbx : c.read .rbx = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress 56 =
      some (message ++ (0x80 :: List.replicate (55 - message.length) 0)))
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨callCore c (BitVec.ofNat 64 message.length), { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some (SingleBlockReference.block message) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + 56 ≤ a ∧ a < blockAddress + 64) ∧ Output.Intact after := by
  have bytes : (message ++ (0x80 :: List.replicate (55 - message.length) 0)) ++
      encoded (BitVec.ofNat 64 message.length) = SingleBlockReference.block message := by
    rw [encoded_short ⟨message.length, short⟩]
    exact (SingleBlockReference.block_expansion message short).symm
  simpa only [bytes] using store c s (BitVec.ofNat 64 message.length) _ running intact pc rbx
    initialBytes writable readable

end Silmaril.Process.CLI.Sha256Cli.LengthStore
