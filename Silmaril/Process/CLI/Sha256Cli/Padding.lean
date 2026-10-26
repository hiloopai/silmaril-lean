module

public import Silmaril.Process.CLI.Sha256Cli.EmptySupport
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame
public import Silmaril.X86.Ext.Store

/-! # The minimal filter's actual empty-message padding path

The byte stores below execute the checked instructions, retaining opaque
successor memories. They establish bytes and footprints; no totality or
whole-driver execution premise is used.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Padding

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)

def blockAddress : Nat := 0x401620

private theorem oneByte (byte : Byte) : X86.Ext.leBytes (byte.setWidth 64) 1 = [byte] := by
  have all : ∀ b : Byte, X86.Ext.leBytes (b.setWidth 64) 1 = [b] := by decide
  exact all byte

private theorem store_byte {entry : Entry} {operand : X86.Ext.Mem} {value : Byte}
    (decoded : entry.Decodes)
    (instruction : entry.instr = .ext (.movI8 (.mem operand) value))
    {c : Core} {s : Syscall.State} {next address : Word}
    (running : s.exited = none) (pc : c.rip.toNat = entry.address)
    (fetch : s.memory.fetchBytes entry.address entry.bytes.length = some entry.bytes)
    (nextEq : c.rip + BitVec.ofNat 64 entry.bytes.length = next)
    (addressEq : operand.addr c next = address)
    (writable : s.memory.Permitted .write address.toNat 1) :
    ∃ after : Memory,
      Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) []
        ⟨{ c with rip := next }, { s with memory := after }⟩ ∧
      Stored s.memory after address.toNat [value] := by
  obtain ⟨after, written, frame⟩ := X86.Ext.storeN_isSome (v := value.setWidth 64) writable
  have effect : entry.denote c s.memory = .retired { c with rip := next } after := by
    simp only [Entry.denote, instruction, X86.Ext.exec, nextEq,
      X86.Ext.writeRM8, addressEq, written, Option.map_some, X86.Ext.retire,
      X86Linux.execResult]
  rw [oneByte] at frame
  exact ⟨after, .retire running ((step_of_entry decoded pc fetch).trans effect).symm, frame⟩

/-- Entry to the zero-fill loop after setting the leading pad byte. -/
def loopCore (c : Core) : Core :=
  { (c.write .rbx 0).write .rax 1 with
    rip := 0x400200, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

set_option maxRecDepth 10000 in
/-- The four actual instructions in the empty-message branch establish the
leading 0x80 byte, zero bit-count register and zero-fill index 1. -/
theorem enter_empty_loop (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4002b7)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨loopCore c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 1 = some [0x80] ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress ≤ a ∧ a < blockAddress + 1) ∧
      Output.Intact after := by
  have permission : s.memory.Permitted .write 0x401620 1 :=
    X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide)
  obtain ⟨after, first, stored⟩ := store_byte (c := c) (s := s) Binary.ok_4002b7.1 rfl running
    (by simp [pc, Binary.i_4002b7]) (intact _ (by simp [Binary.transcript]))
    (next := 0x4002be) (address := 0x401620) (by rw [pc]; rfl)
    (by simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value]) permission
  have code : Output.Intact after := Output.intact_of_store intact stored (by decide)
  let c1 : Core := { c with rip := 0x4002be }
  let c2 : Core := { c1.write .rbx 0 with
    rip := 0x4002c0, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have second : Proc.Step X86Linux.isa Env.linux
      (⟨c1, { s with memory := after }⟩ : Output.PS) [] ⟨c2, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4002be) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4002be, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      c1, c2, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let c3 : Core := { c2.write .rax 1 with rip := 0x4002c5 }
  have third : Proc.Step X86Linux.isa Env.linux
      (⟨c2, { s with memory := after }⟩ : Output.PS) [] ⟨c3, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4002c0) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    rfl
  have fourth : Proc.Step X86Linux.isa Env.linux
      (⟨c3, { s with memory := after }⟩ : Output.PS) []
        ⟨loopCore c, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4002c5) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4002c5, X86.Ext.exec,
      c3, c2, c1, loopCore, X86.State.write]
  refine ⟨after, .cons first (.cons second (.cons third (.single fourth))), ?_, ?_, code⟩
  · exact stored.readWith_self (X86.Ext.Memory.Permitted.sub readable
      (by decide) (by decide) (by decide))
  · exact stored.writesWithin (by
      intro i hi
      simp only [List.length_singleton] at hi
      dsimp [blockAddress]
      omega)

/-- The result of one actual zero-fill loop iteration. -/
def iterationCore (c : Core) (index : Fin 55) : Core :=
  { c.write .rax (BitVec.ofNat 64 (index.val + 2)) with
    rip := if index.val = 54 then 0x400211 else 0x400200,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (56 : Word) }

private theorem increment_value (index : Fin 55) :
    BitVec.ofNat 64 (index.val + 1) + (1 : Word) =
      BitVec.ofNat 64 (index.val + 2) := by
  have all : ∀ i : Fin 55, BitVec.ofNat 64 (i.val + 1) + (1 : Word) =
      BitVec.ofNat 64 (i.val + 2) := by decide
  exact all index

private theorem byte_address (index : Fin 55) :
    BitVec.ofNat 64 (index.val + 2) + (0x40161f : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (blockAddress + index.val + 1) := by
  have all : ∀ i : Fin 55,
      BitVec.ofNat 64 (i.val + 2) + (0x40161f : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (blockAddress + i.val + 1) := by decide
  exact all index

private theorem loop_condition (index : Fin 55) :
    X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (56 : Word))
      .ne = some (decide (index.val ≠ 54)) := by
  have all : ∀ i : Fin 55,
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 2)) (56 : Word))
        .ne = some (decide (i.val ≠ 54)) := by decide
  exact all index

set_option maxRecDepth 10000 in
/-- ADD, byte store, CMP and JNE execute one real loop iteration. The final
iteration falls through to the bit-length setup; all prior ones branch back. -/
theorem zero_iteration (c : Core) (s : Syscall.State) (index : Fin 55)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400200)
    (rax : c.read .rax = BitVec.ofNat 64 (index.val + 1))
    (writable : s.memory.Permitted .write (blockAddress + index.val + 1) 1) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨iterationCore c index, { s with memory := after }⟩ ∧
      Stored s.memory after (blockAddress + index.val + 1) [0] ∧
      Output.Intact after := by
  let added : Core := { c.write .rax (BitVec.ofNat 64 (index.val + 2)) with
    rip := 0x400204, flags := X86.Ext.addFlagsN (BitVec.ofNat 64 (index.val + 1)) (1 : Word) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨added, s⟩ := by
    apply Output.retire (entry := Binary.i_400200) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400200])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400200, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      added, pc, rax, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    exact congrArg (fun value : Word => Machine.RegisterFile.write c.regs .rax value)
      (increment_value index)
  have addressNat : (BitVec.ofNat 64 (blockAddress + index.val + 1)).toNat =
      blockAddress + index.val + 1 := by
    apply Nat.mod_eq_of_lt
    have bound := index.isLt
    dsimp [blockAddress]
    omega
  have permission : s.memory.Permitted .write
      (BitVec.ofNat 64 (blockAddress + index.val + 1)).toNat 1 := by
    rw [addressNat]
    exact writable
  obtain ⟨after, second, stored⟩ := store_byte (c := added) (s := s) Binary.ok_400204.1 rfl
    running rfl (intact _ (by simp [Binary.transcript]))
    (next := 0x40020b) (address := BitVec.ofNat 64 (blockAddress + index.val + 1)) rfl
    (by
      simpa [X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value,
        added, X86.State.read, X86.State.write] using byte_address index) permission
  rw [addressNat] at stored
  have code : Output.Intact after := Output.intact_of_store intact stored (by
    dsimp [blockAddress]
    omega)
  let compared : Core := { added with
    rip := 0x40020f,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (56 : Word) }
  have third : Proc.Step X86Linux.isa Env.linux
      (⟨{ added with rip := 0x40020b }, { s with memory := after }⟩ : Output.PS) []
        ⟨compared, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_40020b) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40020b, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.Sz.read,
      X86.Ext.retire, X86.Ext.AluOp.flagsN,
      compared, added, X86.State.read, X86.State.write]
  have fourth : Proc.Step X86Linux.isa Env.linux
      (⟨compared, { s with memory := after }⟩ : Output.PS) []
        ⟨iterationCore c index, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_40020f) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    have condition := loop_condition index
    simp [Entry.denote, X86Linux.execResult, Binary.i_40020f, X86.Ext.exec,
      compared, added, iterationCore, X86.State.write]
    erw [condition]
    by_cases last : index.val = 54 <;> simp [last]
  exact ⟨after, .cons first (.cons second (.cons third (.single fourth))), stored, code⟩

private theorem extend_prefix {before after : Memory} (index : Fin 55)
    (stored : Stored before after (blockAddress + index.val + 1) [0])
    (initialBytes : before.readBytes blockAddress (index.val + 1) =
      some (0x80 :: List.replicate index.val 0))
    (readable : before.Permitted .read blockAddress 64) :
    after.readBytes blockAddress (index.val + 2) =
      some (0x80 :: List.replicate (index.val + 1) 0) := by
  have low := (stored.readWith_disjoint .read blockAddress (index.val + 1)
    (Or.inl (by omega))).trans initialBytes
  have permission : before.Permitted .read (blockAddress + index.val + 1) 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by
      have bound := index.isLt
      omega)
  have high : after.readBytes (blockAddress + (index.val + 1)) 1 = some [0] := by
    simpa only [Nat.add_assoc, List.length_singleton, Memory.readBytes] using
      stored.readWith_self permission
  have joined := Memory.readBytes_append low high
  have bytes : (0x80 :: List.replicate index.val (0 : Byte)) ++ [0] =
      0x80 :: List.replicate (index.val + 1) 0 := by
    rw [List.cons_append]
    have last : [(0 : Byte)] = List.replicate 1 0 := rfl
    rw [last, List.replicate_append_replicate]
  simpa only [bytes, Nat.add_assoc] using joined

/-- The exact loop-exit register and flag state. -/
def zeroFinished (c : Core) : Core :=
  { c.write .rax 56 with
    rip := 0x400211,
    flags := X86.Ext.subFlagsN (56 : Word) 56 }

set_option maxRecDepth 10000 in
/-- A finite sequence of real loop iterations fills all bytes before the
64-bit bit length. `remaining` counts iterations before the final one;
the theorem establishes one admitted local execution, not process liveness. -/
theorem zero_fill (remaining : Nat) :
    ∀ (c : Core) (s : Syscall.State), remaining < 55 →
      s.exited = none → Output.Intact s.memory → c.rip = 0x400200 →
      c.read .rax = BitVec.ofNat 64 (55 - remaining) →
      s.memory.Permitted .write blockAddress 64 →
      s.memory.Permitted .read blockAddress 64 →
      s.memory.readBytes blockAddress (55 - remaining) =
        some (0x80 :: List.replicate (54 - remaining) 0) →
      ∃ after : Memory,
        Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
          ⟨zeroFinished c, { s with memory := after }⟩ ∧
        after.readBytes blockAddress 56 = some (0x80 :: List.replicate 55 0) ∧
        Memory.WritesWithin s.memory after
          (fun a => blockAddress ≤ a ∧ a < blockAddress + 56) ∧
        Output.Intact after := by
  induction remaining with
  | zero =>
    intro c s bound running intact pc rax writable readable initialBytes
    let index : Fin 55 := ⟨54, by decide⟩
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by dsimp [index]; omega)
        (by dsimp [index]; omega)
    obtain ⟨after, run, stored, code⟩ := zero_iteration c s index running intact pc rax permission
    refine ⟨after, ?_, extend_prefix index stored initialBytes readable, ?_, code⟩
    · simpa [iterationCore, index, zeroFinished] using run
    · exact stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        dsimp [index]
        omega)
  | succ remaining ih =>
    intro c s bound running intact pc rax writable readable initialBytes
    let index : Fin 55 := ⟨54 - (remaining + 1), by omega⟩
    have indexValue : index.val + 1 = 55 - (remaining + 1) := by dsimp [index]; omega
    have nextValue : index.val + 2 = 55 - remaining := by dsimp [index]; omega
    have nextCount : index.val + 1 = 54 - remaining := by dsimp [index]; omega
    have notLast : index.val ≠ 54 := by dsimp [index]; omega
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by
        have indexBound := index.isLt
        omega)
    obtain ⟨middle, run, stored, code⟩ := zero_iteration c s index running intact pc
      (by simpa only [indexValue] using rax) permission
    have nextPrefix : middle.readBytes blockAddress (55 - remaining) =
        some (0x80 :: List.replicate (54 - remaining) 0) := by
      have firstPrefix : s.memory.readBytes blockAddress (index.val + 1) =
          some (0x80 :: List.replicate index.val 0) := by
        simpa only [indexValue, index] using initialBytes
      have extended := extend_prefix index stored firstPrefix readable
      simpa only [nextValue, nextCount] using extended
    obtain ⟨after, suffix, bytes, frame, finalCode⟩ := ih (iterationCore c index)
      { s with memory := middle } (by omega) running code
      (by simp [iterationCore, notLast])
      (by simp [iterationCore, nextValue, X86.State.read, X86.State.write])
      (stored.permitted writable) (stored.permitted readable) nextPrefix
    refine ⟨after, ?_, bytes, ?_, finalCode⟩
    · have combined := run.append suffix
      simpa only [List.nil_append, zeroFinished, iterationCore, X86.State.write,
        Machine.RegisterFile.write_shadow] using combined
    · exact (stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        have indexBound := index.isLt
        omega)).trans frame

/-- The whole 224-instruction empty padding prefix (branch plus 55 loop
iterations) establishes the first 56 bytes and reaches bit-length setup. -/
theorem empty_prefix (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4002b7)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished (loopCore c), { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 = some (0x80 :: List.replicate 55 0) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress ≤ a ∧ a < blockAddress + 56) ∧
      Output.Intact after := by
  obtain ⟨middle, branch, initialBytes, frame, code⟩ :=
    enter_empty_loop c s running intact pc writable readable
  obtain ⟨after, loop, bytes, loopFrame, finalCode⟩ := zero_fill 54 (loopCore c)
    { s with memory := middle } (by decide) running code rfl
    (by simp [loopCore, X86.State.read, X86.State.write])
    ((frame.permitted_iff _ _ _).mpr writable)
    ((frame.permitted_iff _ _ _).mpr readable) initialBytes
  exact ⟨after, by simpa only [List.nil_append] using branch.append loop,
    bytes, (frame.mono (by intro a ha; omega)).trans loopFrame, finalCode⟩

/-- The actual compression CALL cut point, including its argument registers. -/
def lengthCore (c : Core) : Core :=
  { ((c.write .rbx 0).write .rsi 0x401620).write .rdi 0x401660 with
    rip := 0x400229,
    flags := X86.Ext.ShiftOp.shl.flags (0 : Word) 3 c.flags }

@[simp] theorem lengthCore_args (c : Core) :
    (lengthCore c).read .rsi = 0x401620 ∧
      (lengthCore c).read .rdi = 0x401660 ∧
      (lengthCore c).read .rsp = c.read .rsp := by
  simp [lengthCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

set_option maxRecDepth 10000 in
/-- The real length/argument instructions store the empty message's final
eight zero bytes and reach the compression CALL with the entire 64-byte pad. -/
theorem store_empty_length (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400211) (rbx : c.read .rbx = 0)
    (initialBytes : s.memory.readBytes blockAddress 56 =
      some (0x80 :: List.replicate 55 0))
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨lengthCore c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some EmptySupport.emptyBlock ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + 56 ≤ a ∧ a < blockAddress + 64) ∧
      Output.Intact after := by
  let c1 : Core := { c.write .rbx 0 with
    rip := 0x400215, flags := X86.Ext.ShiftOp.shl.flags (0 : Word) 3 c.flags }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨c1, s⟩ := by
    apply Output.retire (entry := Binary.i_400211) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400211])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400211, X86.Ext.exec,
      X86.Ext.Count.raw, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.ShiftOp.result,
      c1, pc, rbx, X86.State.write]
  let c2 : Core := { c1.write .rsi 0x401620 with rip := 0x40021a }
  have second : Proc.Step X86Linux.isa Env.linux (⟨c1, s⟩ : Output.PS) [] ⟨c2, s⟩ := by
    apply Output.retire (entry := Binary.i_400215) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c3 : Core := { c2.write .rdi 0x401660 with rip := 0x40021f }
  have third : Proc.Step X86Linux.isa Env.linux (⟨c2, s⟩ : Output.PS) [] ⟨c3, s⟩ := by
    apply Output.retire (entry := Binary.i_40021a) (by simp [Binary.transcript]) intact running rfl
    rfl
  let c4 : Core := { c3.write .rbx 0 with rip := 0x400222 }
  have fourth : Proc.Step X86Linux.isa Env.linux (⟨c3, s⟩ : Output.PS) [] ⟨c4, s⟩ := by
    apply Output.retire (entry := Binary.i_40021f) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40021f, X86.Ext.exec,
      X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      c4, c3, c2, c1, X86.State.read, X86.State.write]
    rfl
  have permission : s.memory.Permitted .write 0x401658 8 :=
    X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide)
  obtain ⟨after, written, stored⟩ := X86.Ext.storeN_isSome
    (address := (0x401658 : Word)) (v := (0 : Word)) permission
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
  have zeros : X86.Ext.leBytes (0 : Word) 8 = List.replicate 8 0 := by decide
  rw [zeros] at stored
  have prefixRead : after.readBytes blockAddress 56 =
      some (0x80 :: List.replicate 55 0) :=
    (stored.readWith_disjoint .read blockAddress 56 (Or.inl (by decide))).trans initialBytes
  have lastRead : after.readBytes (blockAddress + 56) 8 = some (List.replicate 8 0) :=
    stored.readWith_self (X86.Ext.Memory.Permitted.sub readable
      (by decide) (by decide) (by decide))
  have fullRead := Memory.readBytes_append prefixRead lastRead
  refine ⟨after, ?_, ?_, ?_, Output.intact_of_store intact stored (by decide)⟩
  · have run := Silmaril.Machine.Trace.Runs.cons first
      (.cons second (.cons third (.cons fourth (.single last))))
    have endCore : { c4 with rip := 0x400229 } = lengthCore c := by
      simp only [c1, c2, c3, c4, lengthCore, X86.State.write]
      congr 1
      funext register
      by_cases same : register = .rbx <;> simp [Machine.RegisterFile.write, same]
    simpa only [List.nil_append, endCore] using run
  · simpa only [List.cons_append, List.replicate_append_replicate, EmptySupport.emptyBlock]
      using fullRead
  · exact stored.writesWithin (by
      intro i hi
      rw [List.length_replicate] at hi
      dsimp [blockAddress]
      omega)

/-- The entire empty padding path reaches the real compression CALL with its
complete block, preserving all memory outside the 64-byte block. -/
theorem empty_block (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4002b7)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨lengthCore (zeroFinished (loopCore c)), { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some EmptySupport.emptyBlock ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress ≤ a ∧ a < blockAddress + 64) ∧
      Output.Intact after := by
  obtain ⟨middle, loop, bytes, frame, code⟩ :=
    empty_prefix c s running intact pc writable readable
  obtain ⟨after, suffix, padded, lengthFrame, finalCode⟩ :=
    store_empty_length (zeroFinished (loopCore c)) { s with memory := middle }
      running code rfl
      (by simp [zeroFinished, loopCore, X86.State.read, X86.State.write, Machine.RegisterFile.write])
      bytes ((frame.permitted_iff _ _ _).mpr writable) ((frame.permitted_iff _ _ _).mpr readable)
  exact ⟨after, by simpa only [List.nil_append] using loop.append suffix, padded,
    (frame.mono (by intro a ha; omega)).trans
      (lengthFrame.mono (by intro a ha; omega)), finalCode⟩

end Silmaril.Process.CLI.Sha256Cli.Padding
