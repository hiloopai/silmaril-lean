module

public import Silmaril.Process.CLI.Sha256Cli.PaddingStream

/-! # The actual leading pad store for a short message

The real LEA/store/CMP/JBE/JE/NOP path reaches the zero-fill loop for an
already copied message of length 0 through 54. Its exact message bytes and R8
index are caller premises; no read event or total input-length counter is
silently inferred. The separately proved 55-byte case takes JE directly to
length setup, executing five instructions and no NOP or zero-fill iteration.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.PaddingShort

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)
open Padding (blockAddress zeroFinished)

/-- Short-message entry to the actual zero-fill loop. -/
def loopEntryCore (c : Core) (count : Nat) : Core :=
  { c.write .rax (BitVec.ofNat 64 (count + 1)) with
    rip := 0x400200,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (count + 1)) (56 : Word) }

/-- The actual JE selects the no-zero-fill path exactly at length 55. -/
def readyCore (c : Core) (count : Nat) : Core :=
  { loopEntryCore c count with rip := if count = 55 then 0x400211 else 0x400200 }

private theorem next_index (index : Fin 56) :
    BitVec.ofNat 64 index.val + (1 : Word) = BitVec.ofNat 64 (index.val + 1) := by
  have all : ∀ i : Fin 56, BitVec.ofNat 64 i.val + (1 : Word) =
      BitVec.ofNat 64 (i.val + 1) := by decide
  exact all index

private theorem pad_address (index : Fin 56) :
    BitVec.ofNat 64 index.val + (0x401620 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (blockAddress + index.val) := by
  have all : ∀ i : Fin 56,
      BitVec.ofNat 64 i.val + (0x401620 : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (blockAddress + i.val) := by decide
  exact all index

private theorem branches (index : Fin 56) :
    X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 1)) (56 : Word))
        .be = some true ∧
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 1)) (56 : Word))
        .e = some (decide (index.val = 55)) := by
  have all : ∀ i : Fin 56,
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 1)) (56 : Word))
          .be = some true ∧
        X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 1)) (56 : Word))
          .e = some (decide (i.val = 55)) := by decide
  exact all index

set_option maxRecDepth 10000 in
/-- The checked instructions append the real 0x80 pad byte and reach either
the zero-fill loop or its distinct length 55 exit. They preserve every message
byte and every other byte outside the new pad position. -/
theorem enter_pad (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress message.length = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨readyCore c message.length, { s with memory := after }⟩ ∧
      after.readBytes blockAddress (message.length + 1) = some (message ++ [0x80]) ∧
      Memory.WritesWithin s.memory after
        (fun a => a = blockAddress + message.length) ∧
      Output.Intact after := by
  let index : Fin 56 := ⟨message.length, short⟩
  let advanced : Core := { c.write .rax (BitVec.ofNat 64 (message.length + 1)) with
    rip := 0x4001c0 }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨advanced, s⟩ := by
    apply Output.retire (entry := Binary.i_4001bc) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_4001bc])
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001bc, X86.Ext.exec,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.Mem.addr, X86.Ext.Mem.ofReg,
      X86.Ext.Base.value, r8, pc, advanced, X86.State.write]
    exact congrArg (fun value : Word => Machine.RegisterFile.write c.regs .rax value)
      (next_index index)
  have addressNat : (BitVec.ofNat 64 (blockAddress + message.length)).toNat =
      blockAddress + message.length := by
    apply Nat.mod_eq_of_lt
    dsimp [blockAddress]
    omega
  have permission : s.memory.Permitted .write
      (BitVec.ofNat 64 (blockAddress + message.length)).toNat 1 := by
    rw [addressNat]
    exact X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by omega)
  obtain ⟨after, written, stored⟩ := X86.Ext.storeN_isSome
    (v := (0x80 : Word)) permission
  have addressEq :
      (X86.Ext.Mem.ofReg .r8 none 0x401620).addr advanced 0x4001c8 =
        BitVec.ofNat 64 (blockAddress + message.length) := by
    have value : advanced.read .r8 = BitVec.ofNat 64 message.length := by
      simpa [advanced] using r8
    simpa only [X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value,
      Option.map_none, Option.getD_none, BitVec.add_zero, value] using pad_address index
  have storeEffect : Binary.i_4001c0.denote advanced s.memory =
      .retired { advanced with rip := 0x4001c8 } after := by
    have value : (0x80 : BitVec 8).setWidth 64 = (0x80 : Word) := by decide
    change X86Linux.execResult (X86.Ext.retire 0x4001c8
      ((X86.Ext.storeN s.memory
        ((X86.Ext.Mem.ofReg .r8 none 0x401620).addr advanced 0x4001c8)
        1 ((0x80 : BitVec 8).setWidth 64)).map fun a => (advanced, a))) = _
    rw [addressEq, value, written]
    rfl
  have second : Proc.Step X86Linux.isa Env.linux (⟨advanced, s⟩ : Output.PS) []
      ⟨{ advanced with rip := 0x4001c8 }, { s with memory := after }⟩ :=
    .retire running ((step_of_entry Binary.ok_4001c0.1 rfl
      (intact _ (by simp [Binary.transcript]))).trans storeEffect).symm
  have bytes : X86.Ext.leBytes (0x80 : Word) 1 = [0x80] := by decide
  rw [addressNat, bytes] at stored
  have code : Output.Intact after := Output.intact_of_store intact stored (by
    dsimp [blockAddress]
    omega)
  let compared : Core := { advanced with
    rip := 0x4001cc,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (message.length + 1)) (56 : Word) }
  have third : Proc.Step X86Linux.isa Env.linux
      (⟨{ advanced with rip := 0x4001c8 }, { s with memory := after }⟩ : Output.PS) []
        ⟨compared, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001c8) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001c8, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire,
      X86.Ext.AluOp.flagsN, compared, advanced, X86.State.read, X86.State.write]
  have fourth : Proc.Step X86Linux.isa Env.linux
      (⟨compared, { s with memory := after }⟩ : Output.PS) []
        ⟨{ compared with rip := 0x4001fc }, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001cc) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    have taken := (branches index).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001cc, X86.Ext.exec, compared]
    erw [taken]
  have suffix : Proc.Runs X86Linux.isa Env.linux
      (⟨{ compared with rip := 0x4001fc }, { s with memory := after }⟩ : Output.PS) []
        ⟨readyCore c message.length, { s with memory := after }⟩ := by
    by_cases boundary : message.length = 55
    · have last : Proc.Step X86Linux.isa Env.linux
          (⟨{ compared with rip := 0x4001fc }, { s with memory := after }⟩ : Output.PS) []
            ⟨readyCore c message.length, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001fc) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        have taken := (branches index).2
        simp [index, boundary] at taken
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001fc, X86.Ext.exec,
          compared, advanced, readyCore, loopEntryCore, boundary]
        erw [taken]
      exact .single last
    · have fifth : Proc.Step X86Linux.isa Env.linux
          (⟨{ compared with rip := 0x4001fc }, { s with memory := after }⟩ : Output.PS) []
            ⟨{ compared with rip := 0x4001fe }, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001fc) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        have notTaken := (branches index).2
        simp [index, boundary] at notTaken
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001fc, X86.Ext.exec, compared]
        erw [notTaken]
      have last : Proc.Step X86Linux.isa Env.linux
          (⟨{ compared with rip := 0x4001fe }, { s with memory := after }⟩ : Output.PS) []
            ⟨readyCore c message.length, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001fe) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001fe, X86.Ext.exec,
          X86.Ext.retire, compared, advanced, readyCore, loopEntryCore, boundary]
      exact .cons fifth (.single last)
  have prefixRead : after.readBytes blockAddress message.length = some message :=
    (stored.readWith_disjoint .read blockAddress message.length (Or.inl (by omega))).trans
      initialBytes
  have readPermission : s.memory.Permitted .read (blockAddress + message.length) 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by omega)
  have padRead : after.readBytes (blockAddress + message.length) 1 = some [0x80] :=
    stored.readWith_self readPermission
  refine ⟨after, ?_, Memory.readBytes_append prefixRead padRead, ?_, code⟩
  · exact .cons first (.cons second (.cons third (.cons fourth suffix)))
  · exact stored.writesWithin (by intro i hi; simp only [List.length_singleton] at hi; omega)

/-- Lengths 0 through 54 execute six instructions to the zero-fill loop. -/
theorem enter_loop (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 55)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress message.length = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨loopEntryCore c message.length, { s with memory := after }⟩ ∧
      after.readBytes blockAddress (message.length + 1) = some (message ++ [0x80]) ∧
      Memory.WritesWithin s.memory after (fun a => a = blockAddress + message.length) ∧
      Output.Intact after := by
  have notBoundary : message.length ≠ 55 := by omega
  simpa [readyCore, notBoundary, loopEntryCore] using
    enter_pad c s message (by omega) running intact pc r8 initialBytes writable readable

/-- Exactly 55 message bytes take the real JE straight to 0x400211. The pad
byte completes the first 56 bytes; there is no NOP or zero-fill iteration. -/
theorem boundary55 (c : Core) (s : Syscall.State) (message : List Byte)
    (length : message.length = 55)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = 55)
    (initialBytes : s.memory.readBytes blockAddress 55 = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 = some (message ++ [0x80]) ∧
      Memory.WritesWithin s.memory after (fun a => a = blockAddress + 55) ∧
      Output.Intact after := by
  simpa [readyCore, loopEntryCore, length, zeroFinished] using
    enter_pad c s message (by omega) running intact pc
      (by rw [length]; exact r8) (by simpa only [length] using initialBytes) writable readable

/-- The actual pad-byte branch and zero-fill loop preserve an arbitrary short
message and establish the entire prefix before bit-length serialization. -/
theorem padded_prefix (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 55)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress message.length = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished (loopEntryCore c message.length), { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 =
        some (message ++ (0x80 :: List.replicate (55 - message.length) 0)) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + message.length ≤ a ∧ a < blockAddress + 56) ∧
      Output.Intact after := by
  obtain ⟨middle, entered, prefixRead, frame, code⟩ :=
    enter_loop c s message short running intact pc r8 initialBytes writable readable
  obtain ⟨after, filled, padded, suffixFrame, finalCode⟩ := PaddingStream.after_message
    (loopEntryCore c message.length) { s with memory := middle } message short
      running code rfl (by simp [loopEntryCore, X86.State.read, X86.State.write])
      ((frame.permitted_iff _ _ _).mpr writable) ((frame.permitted_iff _ _ _).mpr readable) prefixRead
  exact ⟨after, by simpa only [List.nil_append] using entered.append filled, padded,
    (frame.mono (by intro a ha; have := short; omega)).trans
      (suffixFrame.mono (by intro a ha; omega)), finalCode⟩

/-- All short messages that fit in one final block, including the distinct
55-byte branch, reach the same length-setup core. Input/read evidence and the
total-length counter remain independent caller obligations. -/
theorem single_block_prefix (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress message.length = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 =
        some (message ++ (0x80 :: List.replicate (55 - message.length) 0)) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + message.length ≤ a ∧ a < blockAddress + 56) ∧
      Output.Intact after := by
  by_cases boundary : message.length = 55
  · obtain ⟨after, run, bytes, frame, code⟩ := boundary55 c s message boundary running intact pc
      (by simpa [boundary] using r8) (by simpa only [boundary] using initialBytes) writable readable
    refine ⟨after, run, ?_, ?_, code⟩
    · simpa only [boundary, Nat.sub_self, List.replicate_zero] using bytes
    · exact frame.mono (by intro a ha; rw [boundary]; omega)
  · have smaller : message.length < 55 := by omega
    have result := padded_prefix c s message smaller running intact pc r8 initialBytes writable readable
    simpa only [zeroFinished, loopEntryCore, X86.State.write, Machine.RegisterFile.write_shadow]
      using result

end Silmaril.Process.CLI.Sha256Cli.PaddingShort
