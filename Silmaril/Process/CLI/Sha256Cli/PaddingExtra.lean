module

public import Silmaril.Process.CLI.Sha256Cli.PaddingStream

/-! # Original long-tail marker and first-block zero fill

The 56..63-byte branch executes its own checked instruction addresses. Its
first block contains the copied tail, marker, and zeros through offset 63.
The distinct length-63 branch skips the zero loop and retains CMP-63 flags.
No compression result, final length block or driver progress is assumed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.PaddingExtra

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI Silmaril.Process.CLI.X86Linux Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)
open Padding (blockAddress)

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

/-- Exact entry after the original long-tail branch sequence. -/
def entryCore (c : Core) (count : Nat) : Core :=
  { c.write .rax (BitVec.ofNat 64 (count + 1)) with
    rip := if count = 63 then 0x4001e9 else 0x4001d8,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (count + 1)) (63 : Word) }

private theorem branches (index : Fin 64) (long : 56 ≤ index.val) :
    X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 1)) (56 : Word))
        .be = some false ∧
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 1)) (63 : Word))
        .a = some (decide (index.val = 63)) := by
  have all : ∀ i : Fin 64, 56 ≤ i.val →
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 1)) (56 : Word))
          .be = some false ∧
        X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 1)) (63 : Word))
          .a = some (decide (i.val = 63)) := by decide
  exact all index long

private theorem next_index (index : Fin 64) :
    BitVec.ofNat 64 index.val + (1 : Word) = BitVec.ofNat 64 (index.val + 1) := by
  have all : ∀ i : Fin 64, BitVec.ofNat 64 i.val + (1 : Word) =
      BitVec.ofNat 64 (i.val + 1) := by decide
  exact all index

private theorem pad_address (index : Fin 64) :
    BitVec.ofNat 64 index.val + (0x401620 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (blockAddress + index.val) := by
  have all : ∀ i : Fin 64,
      BitVec.ofNat 64 i.val + (0x401620 : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (blockAddress + i.val) := by decide
  exact all index

set_option maxRecDepth 10000 in
/-- The checked instructions append the real 0x80 pad byte and reach either
the zero-to-64 loop or its distinct length 63 exit. They preserve every message
byte and every other byte outside the new pad position. -/
theorem enter_pad (c : Core) (s : Syscall.State) (message : List Byte)
    (room : message.length < 64)
    (long : 56 ≤ message.length)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc)
    (r8 : c.read .r8 = BitVec.ofNat 64 message.length)
    (initialBytes : s.memory.readBytes blockAddress message.length = some message)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨entryCore c message.length, { s with memory := after }⟩ ∧
      after.readBytes blockAddress (message.length + 1) = some (message ++ [0x80]) ∧
      Memory.WritesWithin s.memory after
        (fun a => a = blockAddress + message.length) ∧
      Output.Intact after := by
  let index : Fin 64 := ⟨message.length, room⟩
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
        ⟨{ compared with rip := 0x4001ce }, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001cc) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    have condition := (branches index long).1
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001cc, X86.Ext.exec, compared]
    erw [condition]
  let compared63 : Core := { compared with
    rip := 0x4001d2,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (message.length + 1)) (63 : Word) }
  have fifth : Proc.Step X86Linux.isa Env.linux
      (⟨{ compared with rip := 0x4001ce }, { s with memory := after }⟩ : Output.PS) []
        ⟨compared63, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001ce) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001ce, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire,
      X86.Ext.AluOp.flagsN, compared63, compared, advanced, X86.State.read, X86.State.write]
  have suffix : Proc.Runs X86Linux.isa Env.linux
      (⟨compared63, { s with memory := after }⟩ : Output.PS) []
        ⟨entryCore c message.length, { s with memory := after }⟩ := by
    by_cases boundary : message.length = 63
    · have last : Proc.Step X86Linux.isa Env.linux
          (⟨compared63, { s with memory := after }⟩ : Output.PS) []
            ⟨entryCore c message.length, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001d2) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        have condition := (branches index long).2
        simp [index, boundary] at condition
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001d2, X86.Ext.exec,
          compared63, compared, advanced, entryCore, boundary]
        erw [condition]
      exact .single last
    · have sixth : Proc.Step X86Linux.isa Env.linux
          (⟨compared63, { s with memory := after }⟩ : Output.PS) []
            ⟨{ compared63 with rip := 0x4001d4 }, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001d2) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        have condition := (branches index long).2
        simp [index, boundary] at condition
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001d2, X86.Ext.exec, compared63]
        erw [condition]
      have last : Proc.Step X86Linux.isa Env.linux
          (⟨{ compared63 with rip := 0x4001d4 }, { s with memory := after }⟩ : Output.PS) []
            ⟨entryCore c message.length, { s with memory := after }⟩ := by
        apply Output.retire (entry := Binary.i_4001d4) (s := { s with memory := after })
          (by simp [Binary.transcript]) code running rfl
        simp [Entry.denote, X86Linux.execResult, Binary.i_4001d4, X86.Ext.exec,
          X86.Ext.retire, compared63, compared, advanced, entryCore, boundary]
      exact .cons sixth (.single last)
  have prefixRead : after.readBytes blockAddress message.length = some message :=
    (stored.readWith_disjoint .read blockAddress message.length (Or.inl (by omega))).trans
      initialBytes
  have readPermission : s.memory.Permitted .read (blockAddress + message.length) 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by omega)
  have padRead : after.readBytes (blockAddress + message.length) 1 = some [0x80] :=
    stored.readWith_self readPermission
  refine ⟨after, ?_, Memory.readBytes_append prefixRead padRead, ?_, code⟩
  · exact .cons first (.cons second (.cons third (.cons fourth (.cons fifth suffix))))
  · exact stored.writesWithin (by intro i hi; simp only [List.length_singleton] at hi; omega)

/-- The zero-to-64 loop exits before the real argument setup. -/
def zeroFinished (c : Core) : Core :=
  { c.write .rax 64 with
    rip := 0x4001e9, flags := X86.Ext.subFlagsN (64 : Word) 64 }

/-- The result of one actual zero-fill loop iteration. -/
def iterationCore (c : Core) (index : Fin 63) : Core :=
  { c.write .rax (BitVec.ofNat 64 (index.val + 2)) with
    rip := if index.val = 62 then 0x4001e9 else 0x4001d8,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (64 : Word) }

private theorem increment_value (index : Fin 63) :
    BitVec.ofNat 64 (index.val + 1) + (1 : Word) =
      BitVec.ofNat 64 (index.val + 2) := by
  have all : ∀ i : Fin 63, BitVec.ofNat 64 (i.val + 1) + (1 : Word) =
      BitVec.ofNat 64 (i.val + 2) := by decide
  exact all index

private theorem byte_address (index : Fin 63) :
    BitVec.ofNat 64 (index.val + 2) + (0x40161f : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (blockAddress + index.val + 1) := by
  have all : ∀ i : Fin 63,
      BitVec.ofNat 64 (i.val + 2) + (0x40161f : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (blockAddress + i.val + 1) := by decide
  exact all index

private theorem loop_condition (index : Fin 63) :
    X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (64 : Word))
      .ne = some (decide (index.val ≠ 62)) := by
  have all : ∀ i : Fin 63,
      X86.Ext.Cond.eval (X86.Ext.subFlagsN (BitVec.ofNat 64 (i.val + 2)) (64 : Word))
        .ne = some (decide (i.val ≠ 62)) := by decide
  exact all index

set_option maxRecDepth 10000 in
/-- ADD, byte store, CMP and JNE execute one real loop iteration. The final
iteration falls through to the extra-padding argument setup; all prior ones branch back. -/
theorem zero_iteration (c : Core) (s : Syscall.State) (index : Fin 63)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001d8)
    (rax : c.read .rax = BitVec.ofNat 64 (index.val + 1))
    (writable : s.memory.Permitted .write (blockAddress + index.val + 1) 1) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨iterationCore c index, { s with memory := after }⟩ ∧
      Stored s.memory after (blockAddress + index.val + 1) [0] ∧
      Output.Intact after := by
  let added : Core := { c.write .rax (BitVec.ofNat 64 (index.val + 2)) with
    rip := 0x4001dc, flags := X86.Ext.addFlagsN (BitVec.ofNat 64 (index.val + 1)) (1 : Word) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨added, s⟩ := by
    apply Output.retire (entry := Binary.i_4001d8) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_4001d8])
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001d8, X86.Ext.exec,
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
  obtain ⟨after, second, stored⟩ := store_byte (c := added) (s := s) Binary.ok_4001dc.1 rfl
    running rfl (intact _ (by simp [Binary.transcript]))
    (next := 0x4001e3) (address := BitVec.ofNat 64 (blockAddress + index.val + 1)) rfl
    (by
      simpa [X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value,
        added, X86.State.read, X86.State.write] using byte_address index) permission
  rw [addressNat] at stored
  have code : Output.Intact after := Output.intact_of_store intact stored (by
    dsimp [blockAddress]
    omega)
  let compared : Core := { added with
    rip := 0x4001e7,
    flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (index.val + 2)) (64 : Word) }
  have third : Proc.Step X86Linux.isa Env.linux
      (⟨{ added with rip := 0x4001e3 }, { s with memory := after }⟩ : Output.PS) []
        ⟨compared, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001e3) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001e3, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.Sz.read,
      X86.Ext.retire, X86.Ext.AluOp.flagsN,
      compared, added, X86.State.read, X86.State.write]
  have fourth : Proc.Step X86Linux.isa Env.linux
      (⟨compared, { s with memory := after }⟩ : Output.PS) []
        ⟨iterationCore c index, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_4001e7) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    have condition := loop_condition index
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001e7, X86.Ext.exec,
      compared, added, iterationCore, X86.State.write]
    erw [condition]
    by_cases last : index.val = 62 <;> simp [last]
  exact ⟨after, .cons first (.cons second (.cons third (.single fourth))), stored, code⟩

private theorem append_zero {before after : Memory} (index : Fin 63) {bytes : List Byte}
    (stored : Stored before after (blockAddress + index.val + 1) [0])
    (initialBytes : before.readBytes blockAddress (index.val + 1) = some bytes)
    (readable : before.Permitted .read blockAddress 64) :
    after.readBytes blockAddress (index.val + 2) = some (bytes ++ [0]) := by
  have low := (stored.readWith_disjoint .read blockAddress (index.val + 1)
    (Or.inl (by omega))).trans initialBytes
  have permission : before.Permitted .read (blockAddress + index.val + 1) 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by
      have bound := index.isLt
      omega)
  have high : after.readBytes (blockAddress + (index.val + 1)) 1 = some [0] := by
    simpa only [Nat.add_assoc, List.length_singleton, Memory.readBytes] using
      stored.readWith_self permission
  simpa only [Nat.add_assoc] using Memory.readBytes_append low high

set_option maxRecDepth 10000 in
/-- Actual loop execution appends zeros and leaves the supplied prefix intact.
Its footprint starts strictly after that prefix. `remaining + 1` is the exact
number of byte-store iterations constructed here. -/
theorem zero_fill_prefix (remaining : Nat) :
    ∀ (c : Core) (s : Syscall.State) (bytes : List Byte), remaining < 63 →
      s.exited = none → Output.Intact s.memory → c.rip = 0x4001d8 →
      c.read .rax = BitVec.ofNat 64 (63 - remaining) →
      s.memory.Permitted .write blockAddress 64 →
      s.memory.Permitted .read blockAddress 64 →
      s.memory.readBytes blockAddress (63 - remaining) = some bytes →
      ∃ after : Memory,
        Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
          ⟨zeroFinished c, { s with memory := after }⟩ ∧
        after.readBytes blockAddress 64 = some (bytes ++ List.replicate (remaining + 1) 0) ∧
        Memory.WritesWithin s.memory after
          (fun a => blockAddress + (63 - remaining) ≤ a ∧ a < blockAddress + 64) ∧
        Output.Intact after := by
  induction remaining with
  | zero =>
    intro c s bytes bound running intact pc rax writable readable initialBytes
    let index : Fin 63 := ⟨62, by decide⟩
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by dsimp [index]; omega)
        (by dsimp [index]; omega)
    obtain ⟨after, run, stored, code⟩ :=
      zero_iteration c s index running intact pc rax permission
    refine ⟨after, ?_, append_zero index stored initialBytes readable, ?_, code⟩
    · simpa [iterationCore, index, zeroFinished] using run
    · exact stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        dsimp [index]
        omega)
  | succ remaining ih =>
    intro c s bytes bound running intact pc rax writable readable initialBytes
    let index : Fin 63 := ⟨62 - (remaining + 1), by omega⟩
    have indexValue : index.val + 1 = 63 - (remaining + 1) := by dsimp [index]; omega
    have nextValue : index.val + 2 = 63 - remaining := by dsimp [index]; omega
    have notLast : index.val ≠ 62 := by dsimp [index]; omega
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by
        have indexBound := index.isLt
        omega)
    obtain ⟨middle, run, stored, code⟩ := zero_iteration c s index running intact pc
      (by simpa only [indexValue] using rax) permission
    have nextRead : middle.readBytes blockAddress (63 - remaining) = some (bytes ++ [0]) := by
      have firstRead : s.memory.readBytes blockAddress (index.val + 1) = some bytes := by
        simpa only [indexValue] using initialBytes
      simpa only [nextValue] using append_zero index stored firstRead readable
    obtain ⟨after, suffix, padded, frame, finalCode⟩ := ih (iterationCore c index)
      { s with memory := middle } (bytes ++ [0]) (by omega) running code
      (by simp [iterationCore, notLast])
      (by simp [iterationCore, nextValue, X86.State.read, X86.State.write])
      (stored.permitted writable) (stored.permitted readable) nextRead
    refine ⟨after, ?_, ?_, ?_, finalCode⟩
    · have combined := run.append suffix
      simpa only [List.nil_append, zeroFinished, iterationCore, X86.State.write,
        Machine.RegisterFile.write_shadow] using combined
    · simpa only [List.append_assoc, List.singleton_append, List.replicate_succ] using padded
    · exact (stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        have indexBound := index.isLt
        omega)).trans (frame.mono (by intro a ha; omega))

/-- The same local fact indexed by the meaningful byte count. The first
`count` bytes are retained and the remaining bytes up to offset 64 become zero. -/
theorem fill_to_length (c : Core) (s : Syscall.State) (count : Nat) (bytes : List Byte)
    (positive : 1 ≤ count) (bound : count < 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001d8) (rax : c.read .rax = BitVec.ofNat 64 count)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64)
    (initialBytes : s.memory.readBytes blockAddress count = some bytes) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some (bytes ++ List.replicate (64 - count) 0) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + count ≤ a ∧ a < blockAddress + 64) ∧
      Output.Intact after := by
  have restored : 63 - (63 - count) = count := by omega
  have length : 63 - count + 1 = 64 - count := by omega
  simpa only [restored, length] using zero_fill_prefix (63 - count) c s bytes
    (by omega) running intact pc (by simpa only [restored] using rax)
    writable readable (by simpa only [restored] using initialBytes)


/-- First of the two canonical long-tail padding blocks. -/
def block (tail : List Byte) : List Byte :=
  tail ++ (0x80 :: List.replicate (63 - tail.length) 0)

theorem block_length (tail : List Byte) (room : tail.length < 64) :
    (block tail).length = 64 := by
  simp only [block, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- Both branches reach argument setup; their flags intentionally differ. -/
def completedCore (c : Core) (count : Nat) : Core :=
  if count = 63 then entryCore c count else zeroFinished c

/-- The original marker and, when needed, zero loop produce the whole first
padding block. Length 63 executes no zero-fill iteration. -/
theorem first_block (c : Core) (s : Syscall.State) (tail : List Byte)
    (room : tail.length < 64) (long : 56 ≤ tail.length)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x4001bc) (fill : c.read .r8 = BitVec.ofNat 64 tail.length)
    (copied : s.memory.readBytes blockAddress tail.length = some tail)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨completedCore c tail.length, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 64 = some (block tail) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + tail.length ≤ a ∧ a < blockAddress + 64) ∧
      Output.Intact after := by
  obtain ⟨middle, marker, marked, markFrame, code⟩ :=
    enter_pad c s tail room long running intact pc fill copied writable readable
  by_cases boundary : tail.length = 63
  · refine ⟨middle, ?_, ?_, markFrame.mono ?_, code⟩
    · simpa only [completedCore, ite_eq_left boundary] using marker
    · simpa only [boundary, block, Nat.sub_self, List.replicate_zero,
        List.append_nil, show 63 + 1 = 64 by decide] using marked
    · intro address atMarker
      omega
  · obtain ⟨after, zeroRun, padded, zeroFrame, finalCode⟩ :=
      fill_to_length (entryCore c tail.length) { s with memory := middle }
        (tail.length + 1) (tail ++ [0x80]) (by omega) (by omega) running code
        (by simp [entryCore, boundary])
        (by simp [entryCore, X86.State.read, X86.State.write])
        ((markFrame.permitted_iff _ _ _).mpr writable)
        ((markFrame.permitted_iff _ _ _).mpr readable) marked
    refine ⟨after, ?_, ?_, ?_, finalCode⟩
    · simpa only [List.nil_append, completedCore, ite_eq_right boundary,
        zeroFinished, entryCore, X86.State.write, Machine.RegisterFile.write_shadow]
        using marker.append zeroRun
    · have count : 64 - (tail.length + 1) = 63 - tail.length := by omega
      simpa only [block, count, List.append_assoc, List.singleton_append] using padded
    · exact (markFrame.mono (by intro address atMarker; omega)).trans
        (zeroFrame.mono (by intro address inside; omega))

/-- Actual argument registers immediately before the extra-padding CALL. -/
def callCore (c : Core) (count : Nat) : Core :=
  { ((completedCore c count).write .rsi 0x401620).write .rdi 0x401660 with
    rip := 0x4001f3 }

@[simp] theorem callCore_registers (c : Core) (count : Nat) :
    (callCore c count).read .rdi = 0x401660 ∧
      (callCore c count).read .rsi = 0x401620 ∧
      (callCore c count).read .rbx = c.read .rbx ∧
      (callCore c count).read .rsp = c.read .rsp := by
  by_cases boundary : count = 63 <;>
    simp [callCore, completedCore, entryCore, zeroFinished, boundary, X86.State.read,
    X86.State.write, Machine.RegisterFile.write]

set_option maxRecDepth 10000 in
/-- Both real MOV instructions reach the original CALL without changing memory. -/
theorem arguments (c : Core) (s : Syscall.State) (count : Nat)
    (running : s.exited = none) (intact : Output.Intact s.memory) :
    Proc.Runs X86Linux.isa Env.linux ⟨completedCore c count, s⟩ []
      ⟨callCore c count, s⟩ := by
  have pc : (completedCore c count).rip = 0x4001e9 := by
    by_cases boundary : count = 63 <;> simp [completedCore, entryCore, zeroFinished, boundary]
  let middle : Core := { (completedCore c count).write .rsi 0x401620 with rip := 0x4001ee }
  have first : Proc.Step X86Linux.isa Env.linux
      (⟨completedCore c count, s⟩ : Output.PS) [] ⟨middle, s⟩ := by
    apply Output.retire (entry := Binary.i_4001e9) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_4001e9])
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001e9, X86.Ext.exec,
      X86.Ext.Sz.write, X86.Ext.retire, middle, pc]
  have second : Proc.Step X86Linux.isa Env.linux (⟨middle, s⟩ : Output.PS) []
      ⟨callCore c count, s⟩ := by
    apply Output.retire (entry := Binary.i_4001ee) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons first (.single second)

end Silmaril.Process.CLI.Sha256Cli.PaddingExtra
