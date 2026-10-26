module

public import Silmaril.Process.CLI.Sha256Cli.Hex
public import Silmaril.Process.CLI.Sha256Cli.Output

/-! # The compiled driver's hexadecimal lookup prefix

These eleven actual instructions read one digest byte at the compiler's
word-reversing index, look up both digits in the loaded table, and store the
canonical hex pair. All instruction fetches use the checked transcription.
The memory is unchanged through the nine-instruction prefix; the two stores
have an exact two-byte footprint. No whole-run assumption, totality claim or
unknown-instruction crash is used. The 32-iteration control invariant and
startup-to-completion composition remain separate obligations.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.HexLookup

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext

/-- The XOR reverses bytes within each little-endian state word. -/
def sourceIndex (index : Fin 32) : Nat := ((BitVec.ofNat 64 index.val) ^^^ 3).toNat

theorem sourceIndex_lt (index : Fin 32) : sourceIndex index < 32 := by
  have all : ∀ i : Fin 32, sourceIndex i < 32 := by decide
  exact all index

def lowDigit (byte : Byte) : Byte := EmptySupport.hexDigits.getD (byte.toNat % 16) 0
def highDigit (byte : Byte) : Byte := EmptySupport.hexDigits.getD (byte.toNat / 16) 0

private theorem lowBits (byte : Byte) :
    ((byte.setWidth 32 &&& (15 : BitVec 32)).setWidth 64) =
      BitVec.ofNat 64 (byte.toNat % 16) := by
  have all : ∀ b : Byte, ((b.setWidth 32 &&& (15 : BitVec 32)).setWidth 64) =
      BitVec.ofNat 64 (b.toNat % 16) := by decide
  exact all byte

private theorem highBits (byte : Byte) :
    (byte.setWidth 64 >>> 4) = BitVec.ofNat 64 (byte.toNat / 16) := by
  have all : ∀ b : Byte, (b.setWidth 64 >>> 4) =
      BitVec.ofNat 64 (b.toNat / 16) := by decide
  exact all byte

private theorem highMask (byte : Byte) :
    (((BitVec.ofNat 32 (byte.toNat / 16)) &&& (15 : BitVec 32)).setWidth 64) =
      BitVec.ofNat 64 (byte.toNat / 16) := by
  have all : ∀ b : Byte,
      (((BitVec.ofNat 32 (b.toNat / 16)) &&& (15 : BitVec 32)).setWidth 64) =
        BitVec.ofNat 64 (b.toNat / 16) := by decide
  exact all byte

private theorem byteLoad (memory : Memory) {base count : Nat} {bytes : List Byte}
    (read : memory.readBytes base count = some bytes) (offset : Nat) (bound : offset < count)
    (small : base + offset < 2 ^ 64) :
    loadN memory (BitVec.ofNat 64 (base + offset)) 1 =
      some ((bytes.getD offset 0).setWidth 64) := by
  have held := holdsLE_byte_of_readBytes read bound
  have address : (BitVec.ofNat 64 (base + offset)).toNat = base + offset :=
    Nat.mod_eq_of_lt small
  rw [← address] at held
  have loaded := loadN_of_holdsLE held
  have byteNorm : ∀ b : Byte, BitVec.ofNat 64 ((b.setWidth 64).toNat % 2 ^ (8 * 1)) =
      b.setWidth 64 := by decide
  simpa only [byteNorm] using loaded

private theorem movx_byte (c : Core) (memory : Memory) (dst : Silmaril.X86.Reg)
    (operand : Mem) (length : Nat) (byte : Byte)
    (read : loadN memory (operand.addr c (c.rip + BitVec.ofNat 64 length)) 1 =
      some (byte.setWidth 64)) :
    X86Linux.execResult (exec (.movx false .d .b dst (.mem operand)) c memory length) =
      .retired { c.write dst (byte.setWidth 64) with rip := c.rip + BitVec.ofNat 64 length } memory := by
  have shape : exec (.movx false .d .b dst (.mem operand)) c memory length =
      retire (c.rip + BitVec.ofNat 64 length)
        ((loadN memory (operand.addr c (c.rip + BitVec.ofNat 64 length)) 1).map fun word =>
          (Sz.d.write c dst ((word.setWidth 8).setWidth 32), memory)) := by
    simp only [exec, readNarrow, Option.map_map]
    rfl
  have mapped := congrArg (fun loaded : Option Word =>
    X86Linux.execResult (retire (c.rip + BitVec.ofNat 64 length)
      (loaded.map fun word => (Sz.d.write c dst ((word.setWidth 8).setWidth 32), memory)))) read
  rw [shape]
  refine mapped.trans ?_
  simp only [Option.map_some, retire, X86Linux.execResult, Sz.write]
  congr 2
  simp

def first (c : Core) (index : Fin 32) : Core :=
  { c.write .rdx (BitVec.ofNat 64 index.val) with rip := 0x400233 }

def second (c : Core) (index : Fin 32) : Core :=
  { (first c index).write .rdx ((BitVec.ofNat 64 index.val) ^^^ 3) with rip := 0x400237, flags := logicFlagsN ((BitVec.ofNat 64 index.val) ^^^ 3) }

def third (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (second c index).write .rdx (byte.setWidth 64) with rip := 0x40023e }

def fourth (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (third c index byte).write .rcx (byte.setWidth 64) with rip := 0x400241 }

def fifth (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (fourth c index byte).write .rdx (BitVec.ofNat 64 (byte.toNat % 16))
    with rip := 0x400244, flags := logicFlagsN (byte.setWidth 32 &&& (15 : BitVec 32)) }

def sixth (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (fifth c index byte).write .rcx (BitVec.ofNat 64 (byte.toNat / 16))
    with rip := 0x400248, flags := ShiftOp.shr.flags (byte.setWidth 64) 4 (fifth c index byte).flags }

def seventh (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (sixth c index byte).write .rdx ((lowDigit byte).setWidth 64) with rip := 0x40024f }

def eighth (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (seventh c index byte).write .rcx (BitVec.ofNat 64 (byte.toNat / 16))
    with rip := 0x400252, flags := logicFlagsN ((BitVec.ofNat 32 (byte.toNat / 16)) &&& (15 : BitVec 32)) }

def ninth (c : Core) (index : Fin 32) (byte : Byte) : Core :=
  { (eighth c index byte).write .rcx ((highDigit byte).setWidth 64) with rip := 0x400259 }

set_option maxRecDepth 10000 in
theorem lookup_prefix (c : Core) (s : Syscall.State) (index : Fin 32) (bytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400230) (rax : c.read .rax = BitVec.ofNat 64 index.val)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
      ⟨ninth c index (bytes.getD (sourceIndex index) 0), s⟩ := by
  let byte := bytes.getD (sourceIndex index) 0
  have a : Proc.Step X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨first c index, s⟩ := by
    apply Output.retire (entry := Binary.i_400230) (by simp [Binary.transcript]) intact running
    · simp [Binary.i_400230, pc]
    · simp [Entry.denote, Binary.i_400230, exec, Sz.read, Sz.write, writeRM, retire,
        first, rax, pc, X86Linux.execResult]
  have b : Proc.Step X86Linux.isa Env.linux ⟨first c index, s⟩ [] ⟨second c index, s⟩ := by
    apply Output.retire (entry := Binary.i_400233) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_400233, exec, Sz.read, Sz.write, writeRM, readRM,
        retire, aluStep, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
        first, second, X86Linux.execResult, Silmaril.X86.State.read, Silmaril.X86.State.write,
        Silmaril.Machine.RegisterFile.write]
      exact ⟨rfl, rfl⟩
  have sourceAddress : (Mem.ofReg .rdx none 0x401660).addr (second c index) 0x40023e =
      BitVec.ofNat 64 (0x401660 + sourceIndex index) := by
    simp only [Mem.addr, Mem.ofReg, Base.value, second, first,
      Silmaril.X86.State.read, Silmaril.X86.State.write,
      Silmaril.Machine.RegisterFile.write, Option.map_none, Option.getD_none,
      ite_true]
    have all : ∀ i : Fin 32,
        ((BitVec.ofNat 64 i.val) ^^^ 3) + 0 + (0x401660 : BitVec 32).signExtend 64 =
          BitVec.ofNat 64 (0x401660 + sourceIndex i) := by decide
    exact all index
  have sourceLoad : loadN s.memory ((Mem.ofReg .rdx none 0x401660).addr (second c index) 0x40023e) 1 =
      some (byte.setWidth 64) := by
    rw [sourceAddress]
    apply byteLoad s.memory stateRead (sourceIndex index) (sourceIndex_lt index)
    have bound := sourceIndex_lt index
    omega
  have d : Proc.Step X86Linux.isa Env.linux ⟨second c index, s⟩ [] ⟨third c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_400237) (by simp [Binary.transcript]) intact running
    · rfl
    · exact movx_byte (second c index) s.memory .rdx (Mem.ofReg .rdx none 0x401660) 7 byte sourceLoad
  have e : Proc.Step X86Linux.isa Env.linux ⟨third c index byte, s⟩ [] ⟨fourth c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_40023e) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_40023e, exec, Sz.read, Sz.write, writeRM, retire,
        first, second, third, fourth, X86Linux.execResult,
        Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write]
  have f : Proc.Step X86Linux.isa Env.linux ⟨fourth c index byte, s⟩ [] ⟨fifth c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_400241) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_400241, exec, Sz.read, Sz.write, writeRM, readRM,
        retire, aluStep, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
        first, second, third, fourth, fifth, X86Linux.execResult,
        Silmaril.X86.State.read, Silmaril.X86.State.write,
        Silmaril.Machine.RegisterFile.write]
      constructor
      · exact congrArg (fun w : Word =>
          ((c.regs.write .rdx (byte.setWidth 64)).write .rcx (byte.setWidth 64)).write .rdx w)
          (lowBits byte)
      · rfl
  have g : Proc.Step X86Linux.isa Env.linux ⟨fifth c index byte, s⟩ [] ⟨sixth c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_400244) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_400244, exec, Sz.read, Sz.write, writeRM, readRM,
        retire, Count.raw, ShiftOp.result, first, second, third, fourth, fifth, sixth,
        X86Linux.execResult, Silmaril.X86.State.read, Silmaril.X86.State.write,
        Silmaril.Machine.RegisterFile.write]
      exact congrArg (fun w : Word =>
        (((c.regs.write .rdx (byte.setWidth 64)).write .rcx (byte.setWidth 64)).write
          .rdx (BitVec.ofNat 64 (byte.toNat % 16))).write .rcx w) (highBits byte)
  have lowBound : byte.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have highBound : byte.toNat / 16 < 16 := by
    have byteBound := byte.isLt
    omega
  have tableAddress : ∀ n : Fin 16,
      BitVec.ofNat 64 n.val + 0 + (0x4004b0 : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (0x4004b0 + n.val) := by decide
  have lowAddress : (Mem.ofReg .rdx none 0x4004b0).addr (sixth c index byte) 0x40024f =
      BitVec.ofNat 64 (0x4004b0 + byte.toNat % 16) := by
    simp only [Mem.addr, Mem.ofReg, Base.value, sixth, fifth, fourth, third, second, first,
      Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write,
      Option.map_none, Option.getD_none, reduceCtorEq, ite_true, ite_false]
    exact tableAddress ⟨_, lowBound⟩
  have lowLoad : loadN s.memory ((Mem.ofReg .rdx none 0x4004b0).addr (sixth c index byte) 0x40024f) 1 =
      some ((lowDigit byte).setWidth 64) := by
    rw [lowAddress]
    apply byteLoad s.memory tableRead (byte.toNat % 16) lowBound
    omega
  have h : Proc.Step X86Linux.isa Env.linux ⟨sixth c index byte, s⟩ [] ⟨seventh c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_400248) (by simp [Binary.transcript]) intact running
    · rfl
    · exact movx_byte (sixth c index byte) s.memory .rdx (Mem.ofReg .rdx none 0x4004b0) 7 (lowDigit byte) lowLoad
  have j : Proc.Step X86Linux.isa Env.linux ⟨seventh c index byte, s⟩ [] ⟨eighth c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_40024f) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, Binary.i_40024f, exec, Sz.read, Sz.write, writeRM, readRM,
        retire, aluStep, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
        first, second, third, fourth, fifth, sixth, seventh, eighth, X86Linux.execResult,
        Silmaril.X86.State.read, Silmaril.X86.State.write,
        Silmaril.Machine.RegisterFile.write]
      constructor
      · exact congrArg (fun w : Word =>
          ((((c.regs.write .rdx (byte.setWidth 64)).write .rcx (byte.setWidth 64)).write
            .rdx (BitVec.ofNat 64 (byte.toNat % 16))).write
            .rcx (BitVec.ofNat 64 (byte.toNat / 16))).write .rdx ((lowDigit byte).setWidth 64)
            |>.write .rcx w) (highMask byte)
      · rfl
  have highAddress : (Mem.ofReg .rcx none 0x4004b0).addr (eighth c index byte) 0x400259 =
      BitVec.ofNat 64 (0x4004b0 + byte.toNat / 16) := by
    simp only [Mem.addr, Mem.ofReg, Base.value, eighth,
      Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write,
      Option.map_none, Option.getD_none, ite_true]
    exact tableAddress ⟨_, highBound⟩
  have highLoad : loadN s.memory ((Mem.ofReg .rcx none 0x4004b0).addr (eighth c index byte) 0x400259) 1 =
      some ((highDigit byte).setWidth 64) := by
    rw [highAddress]
    apply byteLoad s.memory tableRead (byte.toNat / 16) highBound
    omega
  have k : Proc.Step X86Linux.isa Env.linux ⟨eighth c index byte, s⟩ [] ⟨ninth c index byte, s⟩ := by
    apply Output.retire (entry := Binary.i_400252) (by simp [Binary.transcript]) intact running
    · rfl
    · exact movx_byte (eighth c index byte) s.memory .rcx (Mem.ofReg .rcx none 0x4004b0) 7 (highDigit byte) highLoad
  exact .cons a (.cons b (.cons d (.cons e (.cons f (.cons g (.cons h (.cons j (.single k))))))))

/-- Reuse the established lowercase-table fact at the nibble boundary. -/
theorem tableDigit (n : Fin 16) :
    EmptySupport.hexDigits.getD n.val 0 = Sha256.hexDigit n.val := by
  have same := congrArg (fun bytes : Option Byte => bytes.getD 0) (Driver.hexDigit_table n)
  simpa only [EmptySupport.hexDigits, List.getD_eq_getElem?_getD, Option.getD_some] using same

theorem digits_eq_hexByte (byte : Byte) :
    [highDigit byte, lowDigit byte] = Sha256.hexByte (UInt8.ofBitVec byte) := by
  have lo := tableDigit ⟨byte.toNat % 16, Nat.mod_lt _ (by decide)⟩
  have hiBound : byte.toNat / 16 < 16 := by have := byte.isLt; omega
  have hi := tableDigit ⟨byte.toNat / 16, hiBound⟩
  change [EmptySupport.hexDigits.getD (byte.toNat / 16) 0,
    EmptySupport.hexDigits.getD (byte.toNat % 16) 0] = _
  rw [lo, hi]
  rfl

set_option maxRecDepth 10000 in
/-- Nine actual lookup instructions and the two real stores establish one
canonical hex pair, with an exact two-byte memory frame and no trace events. -/
theorem lookup_store (c : Core) (s : Syscall.State) (index : Fin 32) (bytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400230) (rax : c.read .rax = BitVec.ofNat 64 index.val)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits)
    (writable : s.memory.Permitted .write (0x4015c0 + 2 * index.val) 2)
    (readable : s.memory.Permitted .read (0x4015c0 + 2 * index.val) 2) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨{ ninth c index (bytes.getD (sourceIndex index) 0) with rip := 0x400267 },
          { s with memory := after }⟩ ∧
      after.readBytes (0x4015c0 + 2 * index.val) 2 =
        some (Sha256.hexByte (UInt8.ofBitVec (bytes.getD (sourceIndex index) 0))) ∧
      Memory.WritesWithin s.memory after
        (fun a => 0x4015c0 + 2 * index.val ≤ a ∧ a < 0x4015c0 + 2 * index.val + 2) := by
  let byte := bytes.getD (sourceIndex index) 0
  have prefixRun := lookup_prefix c s index bytes running intact pc rax stateRead tableRead
  have rax' : (ninth c index byte).read .rax = BitVec.ofNat 64 index.val := by
    simp [ninth, eighth, seventh, sixth, fifth, fourth, third, second, first,
      Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write]
    exact rax
  have low : ((ninth c index byte).read .rdx).setWidth 8 = lowDigit byte := by
    simp [ninth, eighth, seventh, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write]
  have high : ((ninth c index byte).read .rcx).setWidth 8 = highDigit byte := by simp [ninth]
  obtain ⟨after, stores, result, frame⟩ := Hex.store_pair (ninth c index byte) s index
    (highDigit byte) (lowDigit byte) running rfl rax' low high
    (intact Binary.i_400259 (by simp [Binary.transcript]))
    (intact Binary.i_400260 (by simp [Binary.transcript])) writable readable
  exact ⟨after, prefixRun.append stores, (digits_eq_hexByte byte) ▸ result, frame⟩

/-- For the empty result, the compiled byte permutation is exactly the
canonical serialized digest, using the existing proved digest vector. -/
theorem empty_permutation :
    (List.finRange 32).map (fun i => UInt8.ofBitVec
      (EmptySupport.emptyStateBytes.getD (sourceIndex i) 0)) =
      Silmaril.Crypto.SHA256.digest [] := by
  rw [Silmaril.Crypto.SHA256.digest_empty]
  decide

end Silmaril.Process.CLI.Sha256Cli.HexLookup
