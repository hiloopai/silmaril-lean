module

public import Silmaril.X86.Ext.Encoding
public import Silmaril.X86.Ext.Flags

/-!
# Semantics of the extended x86-64 model

`exec i s memory` executes one decoded `Ext.Instr` on the register state
`X86.State` and a `Process.Memory`, and advances RIP by the length of the
canonical encoding (`encode`). It is a handwritten local model following the
Intel SDM instruction reference; it is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware description.

## Registers

* 64-bit writes replace the register. 32-bit writes zero-extend to 64 bits
  (SDM Vol. 1, 3.4.1.1): `Sz.read_write`, `write_d_read`, `write_d_high`.
* Byte-register writes (SETcc) replace bits 7:0 and keep bits 63:8
  (`writeByte_read_low`, `writeByte_read_high`). Only the low byte of each of the
  sixteen registers is a byte register; AH, CH, DH, BH are not modeled.

## Memory

A memory operand's effective address is `base + (index << scale) + disp`
modulo 2^64, where `base` is a register's value, zero (base-less addressing) or
the address of the *next* instruction (RIP-relative). `Mem.addr` therefore
takes that address as an argument, and so do `readRM`, `writeRM`, `readNarrow`
and `writeRM8`; `exec` passes the `next` it already computes. Loads and stores of 1, 2, 4 or 8 bytes are little-endian and go
through `Process.Memory`, which checks the permission of the whole span (which
must lie below 2^64) and faults on unbacked bytes. There are no alignment checks,
no canonical-address checks (`#GP`/`#SS`) and no atomicity.

The only segmentation is `Base.fs`, whose effective address adds `State.fsBase`
(`Mem.addr_fs`). There is no segment limit, no descriptor and no `#GP` of its
own: an `fs:` address that is not backed fails the ordinary permission check
like any other. `fsBase` is never written -- the model has no `wrfsbase` and no
MSR writes -- so it is a parameter of the run.
An instruction whose memory destination is also a source (for example
`add [m], r`) reads, computes, and then writes; if the write is not permitted
the instruction faults with no effect. `loadN_storeN` states load-after-store.

## Outcomes

`Result.ok` carries the successor state. `dataFault` is a failed memory
access, `divideError` is `#DE` (divisor zero or quotient too large; never a
value), `undefinedCondition c` is a SETcc, Jcc or CMOVcc whose condition `c`
depends on an architecturally undefined flag (`Cond.eval` is `none`), and
`trap` is UD2. CMOVcc reads its source before evaluating its condition.
A faulting instruction has no partial effect.

## Choices where the SDM leaves room

* Shifts and rotates whose masked count is zero still write their (unchanged)
  destination: a 32-bit register destination is zero-extended and a memory
  destination needs write permission. The flags are unchanged, as the SDM
  specifies. The SDM does not spell out either destination effect for a zero
  count; this is a modeling decision.
* The count of `shift ... (.imm n)` is the unmasked imm8, masked at execution.
* `bitcount` has its LZCNT/TZCNT/POPCNT meaning. That meaning assumes the
  CPUID feature named by `Instr.requires`; `exec` does not model processors
  without it (where `F3 0F BD`/`BC` execute as BSR/BSF and `F3 0F B8` raises
  #UD).

`exec_ofInsn` proves that on the embedded stack subset `exec` is exactly
`X86.Insn.exec`, with a failed stack access as `dataFault`.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (wordByte encodeWords)

/-! ## Register views -/

namespace Sz

/-- Read the low `sz.bits` bits of a register. -/
def read (sz : Sz) (s : State) (r : Reg) : BitVec sz.bits := (s.read r).setWidth sz.bits

/-- Write a register at size `sz`: 32-bit values are zero-extended. -/
def write (sz : Sz) (s : State) (r : Reg) (v : BitVec sz.bits) : State :=
  s.write r (v.setWidth 64)

@[simp] theorem read_write (sz : Sz) (s : State) (r : Reg) (v : BitVec sz.bits) :
    sz.read (sz.write s r v) r = v := by
  simp only [read, write, State.read_write_same]
  rw [BitVec.setWidth_setWidth_of_le _ (by cases sz <;> decide), BitVec.setWidth_eq]

theorem read_write_other (sz : Sz) (s : State) (r q : Reg) (v : BitVec sz.bits) (h : q ≠ r) :
    (sz.write s r v).read q = s.read q := by
  simp [write, h]

@[simp] theorem write_rip (sz : Sz) (s : State) (r : Reg) (v : BitVec sz.bits) :
    (sz.write s r v).rip = s.rip := rfl

@[simp] theorem write_flags (sz : Sz) (s : State) (r : Reg) (v : BitVec sz.bits) :
    (sz.write s r v).flags = s.flags := rfl

@[simp] theorem read_q (s : State) (r : Reg) : Sz.q.read s r = s.read r := by
  simp [read]

@[simp] theorem write_q (s : State) (r : Reg) (v : BitVec 64) : Sz.q.write s r v = s.write r v := by
  simp [write]

end Sz

/-- The view law of 32-bit writes: the register holds the zero-extension. -/
theorem write_d_read (s : State) (r : Reg) (v : BitVec 32) :
    (Sz.d.write s r v).read r = v.setWidth 64 := by
  simp [Sz.write]

/-- A 32-bit write clears bits 63:32. -/
theorem write_d_high (s : State) (r : Reg) (v : BitVec 32) :
    ((Sz.d.write s r v).read r).extractLsb' 32 32 = 0#32 := by
  rw [write_d_read]
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  simp

/-- A byte-register write: bits 7:0 replaced, bits 63:8 kept. -/
def writeByte (s : State) (r : Reg) (v : BitVec 8) : State :=
  s.write r ((s.read r &&& ~~~(0xFF#64)) ||| v.setWidth 64)

theorem writeByte_read_low (s : State) (r : Reg) (v : BitVec 8) :
    ((writeByte s r v).read r).setWidth 8 = v := by
  ext i hi
  simp [writeByte]

theorem writeByte_read_high (s : State) (r : Reg) (v : BitVec 8) :
    (writeByte s r v).read r >>> 8 = s.read r >>> 8 := by
  ext i hi
  have key : ∀ j < 56, (~~~(0xFF#64)).getLsbD (8 + j) = true := by decide
  simp only [writeByte, State.read_write_same, BitVec.getElem_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases h : 8 + i < 64
  · rw [key i (by omega)]; simp
  · simp [BitVec.getLsbD_of_ge (s.read r) (8 + i) (by omega)]

theorem writeByte_read_other (s : State) (r q : Reg) (v : BitVec 8) (h : q ≠ r) :
    (writeByte s r v).read q = s.read q := by
  simp [writeByte, h]

/-! ## Little-endian memory access -/

/-- The low `k` bytes of `v`, least significant first. -/
def leBytes (v : Word) (k : Nat) : List Byte := List.ofFn fun i : Fin k => wordByte v i

/-- The little-endian value of a byte list. -/
def leValue : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

@[simp] theorem length_leBytes (v : Word) (k : Nat) : (leBytes v k).length = k := by
  simp [leBytes]

theorem leBytes_eight (v : Word) : leBytes v 8 = encodeWords [v] := by
  rw [X86.encodeWords_singleton]
  simp [leBytes, List.ofFn_succ]

private theorem wordByte_succ (v : Word) (i : Nat) : wordByte v (i + 1) = wordByte (v >>> 8) i := by
  simp only [wordByte]
  ext j hj
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  congr 1
  omega

private theorem wordByte_zero (v : Word) : (wordByte v 0).toNat = v.toNat % 256 := by
  simp [wordByte]

theorem leValue_leBytes (v : Word) (k : Nat) : leValue (leBytes v k) = v.toNat % 2 ^ (8 * k) := by
  induction k generalizing v with
  | zero => simp [leBytes, leValue, Nat.mod_one]
  | succ k ih =>
    have := ih (v >>> 8)
    simp only [leBytes] at this
    simp only [leBytes, List.ofFn_succ, leValue, Fin.val_zero, Fin.val_succ, wordByte_succ]
    rw [this]
    simp only [wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add, Nat.mod_mul]
    simp

/-- Load `k` bytes at `address`, zero-extended to 64 bits. -/
def loadN (memory : Memory) (address : Word) (k : Nat) : Option Word :=
  (memory.readBytes address.toNat k).map fun bytes => BitVec.ofNat 64 (leValue bytes)

/-- Store the low `k` bytes of `v` at `address`. -/
def storeN (memory : Memory) (address : Word) (k : Nat) (v : Word) : Option Memory :=
  memory.writeBytes address.toNat (leBytes v k)

/-- A store changes only its own bytes and no mapping. -/
theorem storeN_writesOnly {memory after : Memory} {address : Word} {k : Nat} {v : Word}
    (h : storeN memory address k v = some after) :
    Memory.WritesOnly memory after address.toNat k := by
  simpa using Memory.writeBytes_writesOnly h

/-- Load after store: reading back the bytes of a store, when readable, gives
the stored value truncated to the access size. -/
theorem loadN_storeN {memory after : Memory} {address : Word} {k : Nat} {v : Word}
    (h : storeN memory address k v = some after)
    (readable : memory.Permitted .read address.toNat k) :
    loadN after address k = some (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * k))) := by
  have frame := storeN_writesOnly h
  have read := Memory.readWith_eq after .read address.toNat (leBytes v k)
    (by
      have : after.checkSpan .read address.toNat k = memory.checkSpan .read address.toNat k :=
        X86.Memory.checkSpan_congr frame.1 _ _ _
      simpa [Memory.Permitted, this] using readable)
    (fun index bound => Memory.writeBytes_get h index bound)
  simp only [length_leBytes] at read
  simp [loadN, Memory.readBytes, read, leValue_leBytes]

theorem loadN_storeN_eight {memory after : Memory} {address : Word} {v : Word}
    (h : storeN memory address 8 v = some after)
    (readable : memory.Permitted .read address.toNat 8) :
    loadN after address 8 = some v := by
  rw [loadN_storeN h readable]
  simp [Nat.mod_eq_of_lt v.isLt]

/-- Only the low `k` bytes of the value reach memory, so narrowing it first
changes nothing. -/
theorem storeN_setWidth (memory : Memory) (address : Word) (n : Narrow) (v : Word) :
    storeN memory address n.bytes ((v.setWidth n.bits).setWidth 64) =
      storeN memory address n.bytes v := by
  unfold storeN
  congr 1
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [length_leBytes] at h1
  simp only [leBytes, List.getElem_ofFn]
  ext j hj
  have hlt : 8 * i + j < n.bits := by
    have : n.bits = 8 * n.bytes := n.bits_eq
    omega
  simp only [Machine.LittleEndian.wordByte, BitVec.getElem_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  have h64 : n.bits ≤ 64 := by cases n <;> decide
  simp [hlt, show 8 * i + j < 64 by omega]

/-- A load whose span avoids a store's span is unaffected by the store. -/
theorem loadN_storeN_disjoint {memory after : Memory} {address other : Word} {k j : Nat}
    {v : Word} (h : storeN memory address k v = some after)
    (disjoint : other.toNat + j ≤ address.toNat ∨ address.toNat + k ≤ other.toNat) :
    loadN after other j = loadN memory other j := by
  simp only [loadN, Memory.readBytes,
    X86.Memory.readWith_writesOnly (storeN_writesOnly h) .read other.toNat j disjoint]

/-! ## Operands -/

/-- The scaled index value. -/
def Index.value (i : Index) (s : State) : Word := s.read i.reg <<< i.scale.toNat

/-- The value a base contributes to an effective address. `next` is the
address of the instruction *after* the one being executed, which is what
RIP-relative addressing is relative to (Intel SDM, Vol. 2, 2.2.1.6). -/
def Base.value : Base → State → Word → Word
  | .reg r, s, _ => s.read r
  | .none, _, _ => 0#64
  | .rip, _, next => next
  | .fs, s, _ => s.fsBase

@[simp] theorem Base.value_reg (r : Reg) (s : State) (next : Word) :
    Base.value (.reg r) s next = s.read r := rfl

@[simp] theorem Base.value_none (s : State) (next : Word) :
    Base.value .none s next = 0#64 := rfl

@[simp] theorem Base.value_rip (s : State) (next : Word) :
    Base.value .rip s next = next := rfl

@[simp] theorem Base.value_fs (s : State) (next : Word) :
    Base.value .fs s next = s.fsBase := rfl

/-- The effective address, modulo 2^64. `next` is the address of the following
instruction; it is used only by RIP-relative operands. -/
def Mem.addr (m : Mem) (s : State) (next : Word) : Word :=
  m.base.value s next + ((m.index.map fun i => i.value s).getD 0#64) + m.disp.signExtend 64

/-- An operand with a base register or no base at all does not depend on the
address of the next instruction. -/
theorem Mem.addr_congr_of_ne_rip {m : Mem} (h : m.base ≠ .rip) (s : State) (n₁ n₂ : Word) :
    m.addr s n₁ = m.addr s n₂ := by
  cases hb : m.base with
  | reg r => simp [Mem.addr, hb]
  | none => simp [Mem.addr, hb]
  | fs => simp [Mem.addr, hb]
  | rip => exact absurd hb h

/-- The effective address of an `fs:` operand is the FS base plus the index and
displacement. This is the whole of segmentation in the model: no limit check,
no descriptor lookup, and no fault of its own -- an out-of-range address simply
fails the ordinary `Process.Memory` permission check like any other. -/
@[simp] theorem Mem.addr_fs (index : Option Index) (d : BitVec 32) (s : State) (next : Word) :
    (Mem.ofFs index d).addr s next =
      s.fsBase + ((index.map fun i => i.value s).getD 0#64) + d.signExtend 64 := rfl

/-- `fs:[disp32]`, the stack-protector canary operand: the FS base plus the
displacement. -/
@[simp] theorem Mem.addr_fsAt (d : BitVec 32) (s : State) (next : Word) :
    (Mem.fsAt d).addr s next = s.fsBase + d.signExtend 64 := by
  simp [Mem.fsAt, Mem.addr, Mem.ofFs]

/-- Read an `r/m` operand at size `sz`. -/
def readRM (sz : Sz) (op : RM) (s : State) (memory : Memory) (next : Word) :
    Option (BitVec sz.bits) :=
  match op with
  | .reg r => some (sz.read s r)
  | .mem m => (loadN memory (m.addr s next) sz.bytes).map fun v => v.setWidth sz.bits

/-- Write an `r/m` operand at size `sz` (32-bit register writes zero-extend). -/
def writeRM (sz : Sz) (op : RM) (v : BitVec sz.bits) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match op with
  | .reg r => some (sz.write s r v, memory)
  | .mem m => (storeN memory (m.addr s next) sz.bytes (v.setWidth 64)).map fun after => (s, after)

/-- Read an 8- or 16-bit `r/m` operand (a byte register is a low byte). -/
def readNarrow (n : Narrow) (op : RM) (s : State) (memory : Memory) (next : Word) :
    Option (BitVec n.bits) :=
  match op with
  | .reg r => some ((s.read r).setWidth n.bits)
  | .mem m => (loadN memory (m.addr s next) n.bytes).map fun v => v.setWidth n.bits

/-- The mask of the low `n.bits` bits. -/
def narrowMask : Narrow → Word
  | .b => 0xFF#64
  | .w => 0xFFFF#64

/-- Write an 8- or 16-bit `r/m` operand. A register destination keeps the bits
above the ones written: an 8-bit write replaces bits 7:0 and a 16-bit write
bits 15:0, neither zero-extending (SDM Vol. 1, 3.4.1.1 — only 32-bit writes
zero-extend). -/
def writeNarrow (n : Narrow) (op : RM) (v : BitVec n.bits) (s : State) (memory : Memory)
    (next : Word) : Option (State × Memory) :=
  match op with
  | .reg r => some (s.write r ((s.read r &&& ~~~(narrowMask n)) ||| v.setWidth 64), memory)
  | .mem m => (storeN memory (m.addr s next) n.bytes (v.setWidth 64)).map fun after => (s, after)

/-- An 8-bit write to a register is exactly `writeByte`. -/
@[simp] theorem writeNarrow_reg_b (r : Reg) (v : BitVec 8) (s : State) (memory : Memory)
    (next : Word) :
    writeNarrow .b (.reg r) v s memory next = some (writeByte s r v, memory) := rfl

/-- Write a byte `r/m` operand. -/
def writeRM8 (op : RM) (v : BitVec 8) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match op with
  | .reg r => some (writeByte s r v, memory)
  | .mem m => (storeN memory (m.addr s next) 1 (v.setWidth 64)).map fun after => (s, after)

/-! ## Execution -/

/-- The outcome of executing one instruction. -/
inductive Result where
  /-- Retired, with the successor state (RIP included) and memory. -/
  | ok (core : State) (memory : Memory)
  /-- A data access was not permitted or not backed. -/
  | dataFault
  /-- `#DE`: division by zero, or a quotient that does not fit. -/
  | divideError
  /-- A SETcc, Jcc or CMOVcc whose condition depends on an undefined flag. -/
  | undefinedCondition (c : Cond)
  /-- UD2. -/
  | trap

/-- Finish an instruction: set RIP, or report a data fault. -/
def retire (next : Word) : Option (State × Memory) → Result
  | some (t, m) => .ok { t with rip := next } m
  | none => .dataFault

/-- A two-operand ALU operation with destination `dst` and second operand `y`. -/
def aluStep (sz : Sz) (op : AluOp) (dst : RM) (y : BitVec sz.bits) (s : State) (memory : Memory)
    (next : Word) : Option (State × Memory) :=
  match readRM sz dst s memory next with
  | none => none
  | some x =>
    if op = .cmp then some ({ s with flags := AluOp.flagsN op x y }, memory)
    else (writeRM sz dst (AluOp.resultN op x y) s memory next).map fun r =>
      ({ r.1 with flags := AluOp.flagsN op x y }, r.2)

/-- The direction-1 ALU form: the destination is a register and the second
operand is the `r/m`. -/
def aluStepR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) (s : State) (memory : Memory)
    (next : Word) : Option (State × Memory) :=
  match readRM sz src s memory next with
  | none => none
  | some y =>
    let x := sz.read s dst
    if op = .cmp then some ({ s with flags := AluOp.flagsN op x y }, memory)
    else some ({ sz.write s dst (AluOp.resultN op x y) with flags := AluOp.flagsN op x y }, memory)

/-- The shift count before masking. -/
def Count.raw (count : Count) (s : State) : BitVec 8 :=
  match count with
  | .cl => (s.read .rcx).setWidth 8
  | .one => 1#8
  | .imm n => n

/-- The byte reversal of BSWAP at the operand size. -/
def byteSwap : (sz : Sz) → BitVec sz.bits → BitVec sz.bits
  | .d, v => byteSwap32 v
  | .q, v => byteSwap64 v

/-- DIV/IDIV at size `sz`: quotient and remainder of `RDX:RAX` (or `EDX:EAX`)
by `y`, or `none` for `#DE`. Signed division truncates toward zero. -/
def divide (sz : Sz) (signed : Bool) (hi lo y : BitVec sz.bits) :
    Option (BitVec sz.bits × BitVec sz.bits) :=
  if signed then
    let n : Int := (hi ++ lo).toInt
    let d : Int := y.toInt
    if d = 0 then none
    else
      let q := n.tdiv d
      if q < -(2 ^ (sz.bits - 1)) ∨ 2 ^ (sz.bits - 1) ≤ q then none
      else some (BitVec.ofInt sz.bits q, BitVec.ofInt sz.bits (n.tmod d))
  else
    let n : Nat := hi.toNat * 2 ^ sz.bits + lo.toNat
    let d : Nat := y.toNat
    if d = 0 then none
    else if 2 ^ sz.bits ≤ n / d then none
    else some (BitVec.ofNat sz.bits (n / d), BitVec.ofNat sz.bits (n % d))

/-- The encoded length of an instruction. -/
def Instr.length (i : Instr) : Nat := (encode i).length

/-- Execute one decoded instruction using the consumed byte length. The default
is the canonical encoding length, preserving the existing canonical API. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat := i.length) : Result :=
  let next := s.rip + BitVec.ofNat 64 length
  match i with
  | .mov sz dst src => retire next (writeRM sz dst (sz.read s src) s memory next)
  | .movI sz dst imm => retire next (writeRM sz dst (imm.signExtend sz.bits) s memory next)
  | .movI16 dst imm =>
    retire next
      (match dst with
       | .reg r => some (s.write r (((s.read r) &&& ~~~(0xFFFF#64)) ||| imm.setWidth 64), memory)
       | .mem m => (storeN memory (m.addr s next) 2 (imm.setWidth 64)).map fun a => (s, a))
  | .movI32 dst imm => retire next (some (Sz.d.write s dst imm, memory))
  | .movabs dst imm => retire next (some (s.write dst imm, memory))
  | .load sz dst src =>
    retire next ((readRM sz (.mem src) s memory next).map fun v => (sz.write s dst v, memory))
  | .store n dst src =>
    retire next (writeNarrow n dst ((s.read src).setWidth n.bits) s memory next)
  | .movx sx sz n dst src =>
    retire next ((readNarrow n src s memory next).map fun v =>
      (sz.write s dst (if sx then v.signExtend sz.bits else v.setWidth sz.bits), memory))
  | .movsxd dst src =>
    retire next ((readRM .d src s memory next).map fun v => (s.write dst (v.signExtend 64), memory))
  | .lea sz dst src =>
    retire next (some (Sz.write sz s dst ((src.addr s next).setWidth sz.bits), memory))
  | .alu sz op dst src => retire next (aluStep sz op dst (sz.read s src) s memory next)
  | .aluR sz op dst src => retire next (aluStepR sz op dst src s memory next)
  | .aluI sz op dst imm => retire next (aluStep sz op dst (imm.signExtend sz.bits) s memory next)
  | .aluI8 sz op dst imm => retire next (aluStep sz op dst (imm.signExtend sz.bits) s memory next)
  | .aluA sz op imm =>
    retire next (aluStep sz op (.reg .rax) (imm.signExtend sz.bits) s memory next)
  | .test sz dst src =>
    retire next ((readRM sz dst s memory next).map fun x =>
      ({ s with flags := logicFlagsN (x &&& sz.read s src) }, memory))
  | .test8 dst src =>
    retire next ((readNarrow .b dst s memory next).map fun x =>
      ({ s with flags := logicFlagsN (x &&& (s.read src).setWidth 8) }, memory))
  | .testI8 dst imm =>
    retire next ((readNarrow .b dst s memory next).map fun x =>
      ({ s with flags := logicFlagsN (x &&& imm) }, memory))
  | .testA8 imm =>
    retire next (some ({ s with flags := logicFlagsN ((s.read .rax).setWidth 8 &&& imm) }, memory))
  | .cmpI8 dst imm =>
    retire next ((readNarrow .b dst s memory next).map fun x =>
      ({ s with flags := subFlagsN x imm }, memory))
  | .cmpA8 imm =>
    retire next (some ({ s with flags := subFlagsN ((s.read .rax).setWidth 8) imm }, memory))
  | .testA sz imm =>
    retire next (some ({ s with
      flags := logicFlagsN (sz.read s .rax &&& imm.signExtend sz.bits) }, memory))
  | .incdec sz dec dst =>
    match readRM sz dst s memory next with
    | none => .dataFault
    | some x =>
      retire next
        ((writeRM sz dst (if dec then x - 1#sz.bits else x + 1#sz.bits) s memory next).map fun r =>
          ({ r.1 with flags := if dec then decFlagsN x s.flags else incFlagsN x s.flags }, r.2))
  | .pushRM src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some v => retire next (pushWord s memory v)
  | .bswap sz dst => retire next (some (sz.write s dst (byteSwap sz (sz.read s dst)), memory))
  | .unary sz .neg dst =>
    match readRM sz dst s memory next with
    | none => .dataFault
    | some x => retire next ((writeRM sz dst (0#sz.bits - x) s memory next).map fun r =>
        ({ r.1 with flags := negFlagsN x }, r.2))
  | .unary sz .not dst =>
    match readRM sz dst s memory next with
    | none => .dataFault
    | some x => retire next (writeRM sz dst (~~~x) s memory next)
  | .imul sz dst src =>
    retire next ((readRM sz src s memory next).map fun y =>
      ({ sz.write s dst (sz.read s dst * y) with flags := imulFlags (sz.read s dst) y }, memory))
  | .mul sz src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some y =>
      let product := (sz.read s .rax).toNat * y.toNat
      let lo := BitVec.ofNat sz.bits product
      let hi := BitVec.ofNat sz.bits (product / 2 ^ sz.bits)
      retire next (some ({ sz.write (sz.write s .rax lo) .rdx hi with
        flags := mulFlags (hi != 0#sz.bits) }, memory))
  | .shift sz op dst count =>
    let c := (count.raw s).toNat % sz.bits
    match readRM sz dst s memory next with
    | none => .dataFault
    | some x => retire next ((writeRM sz dst (op.result x c) s memory next).map fun r =>
        ({ r.1 with flags := op.flags x c s.flags }, r.2))
  | .cxd sz =>
    retire next (some (sz.write s .rdx
      (if (sz.read s .rax).msb then BitVec.allOnes sz.bits else 0#sz.bits), memory))
  | .cxe .d =>
    retire next (some (Sz.d.write s .rax (((s.read .rax).setWidth 16).signExtend 32), memory))
  | .cxe .q => retire next (some (s.write .rax ((Sz.d.read s .rax).signExtend 64), memory))
  | .div sz signed src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some y =>
      match divide sz signed (sz.read s .rdx) (sz.read s .rax) y with
      | none => .divideError
      | some (q, r) =>
        retire next (some ({ sz.write (sz.write s .rax q) .rdx r with flags := undefinedFlags },
          memory))
  | .cmov sz c dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some value =>
      match c.eval s.flags with
      | none => .undefinedCondition c
      | some taken =>
        retire next (some (sz.write s dst (if taken then value else sz.read s dst), memory))
  | .setcc c dst =>
    match c.eval s.flags with
    | none => .undefinedCondition c
    | some v => retire next (writeRM8 dst (if v then 1#8 else 0#8) s memory next)
  | .jmp rel => .ok { s with rip := next + rel.signExtend 64 } memory
  | .jmp8 rel => .ok { s with rip := next + rel.signExtend 64 } memory
  | .jcc8 c rel =>
    match c.eval s.flags with
    | none => .undefinedCondition c
    | some true => .ok { s with rip := next + rel.signExtend 64 } memory
    | some false => .ok { s with rip := next } memory
  | .jcc c rel =>
    match c.eval s.flags with
    | none => .undefinedCondition c
    | some true => .ok { s with rip := next + rel.signExtend 64 } memory
    | some false => .ok { s with rip := next } memory
  | .call rel =>
    match pushWord s memory next with
    | none => .dataFault
    | some (t, m) => .ok { t with rip := next + rel.signExtend 64 } m
  | .ret =>
    match popWord s memory with
    | none => .dataFault
    | some (target, t) => .ok { t with rip := target } memory
  | .push src => retire next (pushWord s memory (s.read src))
  | .pop dst => retire next ((popWord s memory).map fun r => (r.2.write dst r.1, memory))
  | .ud2 => .trap
  | .nop _ => retire next (some (s, memory))
  | .endbr64 => retire next (some (s, memory))
  | .mov8 dst src =>
    retire next ((readNarrow .b src s memory next).map fun v => (writeByte s dst v, memory))
  | .movI8 dst imm => retire next (writeRM8 dst imm s memory next)
  | .leave =>
    let t := s.write .rsp (s.read .rbp)
    retire next ((popWord t memory).map fun r => (r.2.write .rbp r.1, memory))
  | .bitcount op sz dst src =>
    retire next ((readRM sz src s memory next).map fun x =>
      ({ sz.write s dst (BitVec.ofNat sz.bits (op.count x)) with flags := op.flags x }, memory))

/-- Execute a semantic instruction using the number of bytes actually consumed.
This length drives fallthrough, relative control flow, CALL return addresses
and RIP-relative data addresses. -/
def execWithLength (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  exec i s memory length

@[simp] theorem execWithLength_canonical (i : Instr) (s : State) (memory : Memory) :
    execWithLength i i.length s memory = exec i s memory := rfl

/-- CMOV reads its source even when the condition would be false. -/
theorem cmov_dataFault (sz : Sz) (c : Cond) (dst : Reg) (src : RM) (length : Nat)
    (s : State) (memory : Memory)
    (h : readRM sz src s memory (s.rip + BitVec.ofNat 64 length) = none) :
    execWithLength (.cmov sz c dst src) length s memory = .dataFault := by
  simp [execWithLength, exec, h]

/-- A defined false 32-bit CMOV still clears bits 63:32. -/
theorem cmov_d_false (c : Cond) (dst src : Reg) (length : Nat)
    (s : State) (memory : Memory) (h : c.eval s.flags = some false) :
    execWithLength (.cmov .d c dst (.reg src)) length s memory =
      .ok { Sz.d.write s dst (Sz.d.read s dst) with
        rip := s.rip + BitVec.ofNat 64 length } memory := by
  simp [execWithLength, exec, readRM, h, retire]

/-! ## Agreement with the embedded subset -/

theorem length_ofInsn (i : X86.Insn) : (ofInsn i).length = i.length := by
  rw [Instr.length, encode_ofInsn, X86.Insn.length_encode]

theorem length_ofInstr (i : X86.Instr) : (ofInstr i).length = i.length := by
  rw [Instr.length, encode_ofInstr, X86.length_encode]

/-- On the register subset, `exec` is `X86.step`. -/
theorem exec_ofInstr (i : X86.Instr) (s : State) (memory : Memory) :
    exec (ofInstr i) s memory = .ok (X86.step i s) memory := by
  have hl := length_ofInstr i
  cases i with
  | movRR dst src =>
    simp only [ofInstr] at hl ⊢
    simp [exec, hl, retire, writeRM, X86.step, X86.Instr.exec]
  | movRI dst imm =>
    simp only [ofInstr] at hl ⊢
    simp [exec, hl, retire, writeRM, X86.step, X86.Instr.exec]
  | alu op dst src =>
    simp only [ofInstr] at hl ⊢
    by_cases hc : op = .cmp
    · subst hc
      simp [exec, hl, retire, aluStep, readRM, X86.step, X86.Instr.exec, X86.execAlu,
        AluOp.flagsN_eq]
    · simp [exec, hl, retire, aluStep, readRM, writeRM, hc, X86.step, X86.Instr.exec,
        X86.execAlu, AluOp.flagsN_eq, AluOp.resultN_eq]
  | aluI op dst imm =>
    simp only [ofInstr] at hl ⊢
    by_cases hc : op = .cmp
    · subst hc
      simp [exec, hl, retire, aluStep, readRM, X86.step, X86.Instr.exec, X86.execAlu,
        AluOp.flagsN_eq]
    · simp [exec, hl, retire, aluStep, readRM, writeRM, hc, X86.step, X86.Instr.exec,
        X86.execAlu, AluOp.flagsN_eq, AluOp.resultN_eq]
  | neg dst =>
    simp only [ofInstr] at hl ⊢
    simp [exec, hl, retire, readRM, writeRM, X86.step, X86.Instr.exec, negFlagsN_eq]
    rfl
  | not dst =>
    simp only [ofInstr] at hl ⊢
    simp [exec, hl, retire, readRM, writeRM, X86.step, X86.Instr.exec]
    rfl

/-- On the stack subset, `exec` is `X86.Insn.exec`, with a failed stack access
reported as `dataFault`. -/
theorem exec_ofInsn (i : X86.Insn) (s : State) (memory : Memory) :
    exec (ofInsn i) s memory =
      match i.exec s memory with
      | some (t, m) => .ok t m
      | none => .dataFault := by
  have hl := length_ofInsn i
  cases i with
  | base i =>
    rw [ofInsn, exec_ofInstr]
    rfl
  | push src =>
    simp only [ofInsn] at hl ⊢
    simp only [exec, hl, X86.Insn.exec]
    cases pushWord s memory (s.read src) <;> rfl
  | pop dst =>
    simp only [ofInsn] at hl ⊢
    simp only [exec, hl, X86.Insn.exec]
    cases popWord s memory <;> rfl
  | call rel =>
    simp only [ofInsn] at hl ⊢
    simp only [exec, hl, X86.Insn.exec]
    cases pushWord s memory (s.rip + BitVec.ofNat 64 (X86.Insn.call rel).length) <;> rfl
  | ret =>
    simp only [ofInsn] at hl ⊢
    simp only [exec, X86.Insn.exec]
    cases popWord s memory <;> rfl

end Silmaril.X86.Ext
