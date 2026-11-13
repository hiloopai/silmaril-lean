module

public import Silmaril.X86.Features.Ext.IntExt.Encoding
public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Ext.Semantics

/-!
# Integer extensions: semantics

`exec i length s memory` executes one instruction of the lane on the extended
state, following the operation sections of the Intel SDM Vol. 2 instruction
pages. Only the integer part of the state (`State.core`: registers, flags,
FS base) and memory are involved; the vector, mask, MXCSR and x87 state are
unchanged. RIP advances by the consumed length; RIP-relative operands are
relative to the next instruction.

Register and memory access reuse the integer machine (`Ext.readRM`,
`Ext.writeRM`, `Ext.loadN`, `Ext.storeN`): 32-bit register writes
zero-extend, memory is little-endian, and an access that is not permitted is a
`dataFault`.

## Flags

Every flag the SDM defines is computed exactly; a flag the SDM leaves
undefined becomes `none` (unknown), as in `X86.Ext`. An instruction that reads
an unknown flag (ADC/SBB and ADCX read CF, ADOX reads OF) is `unmodeled`
(chaos) on such a state rather than given a value.

## Undefined results and other chaos

* BSF/BSR with a zero source: the destination is undefined (SDM), so the
  instruction is `unmodeled`; otherwise ZF = 0 and CF, OF, SF, AF, PF are
  unknown.
* BT/BTS/BTR/BTC with a memory operand and a register bit offset address a
  bit string beyond the operand (the offset is signed). The model accesses the
  operand-sized word at `ea + size * (offset div bits)`, the access the SDM
  describes; since a processor may access less, a refused access is
  `unmodeled` rather than a fault. The immediate forms mask the offset and
  access the operand itself.
* SHLD/SHRD with a masked count of zero leave the flags unchanged and write a
  register destination back (so a 32-bit register is zero-extended; measured
  on an i7-8700); with a memory destination the zero-count case is
  `unmodeled`.

## Choices measured on hardware

CMPXCHG at 32 bits writes exactly one register: the destination when the
comparison succeeds (zero-extended) and EAX when it fails (zero-extended),
leaving the other register's upper half unchanged. This is the behaviour of
the oracle (an i7-8700) and of the SDM's operation section read literally.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntExt

open Silmaril.X86 (Reg Word Flags)
open Silmaril.X86.Ext (Sz RM Mem readRM writeRM loadN storeN parityN isZeroN addFlagsN subFlagsN
  logicFlagsN imulFlags mulFlags tzcntN lzcntN byteSwap)
open Silmaril.Process (Memory)

/-- The integer state. -/
abbrev Core := X86.State

/-- The outcome on the integer state. -/
inductive Out where
  | ok (core : Core) (memory : Memory)
  | dataFault
  | unmodeled

def Out.ofOption : Option (Core × Memory) → Out
  | some (c, m) => .ok c m
  | none => .dataFault

/-- Replace the flags. -/
def setFlags (c : Core) (f : Flags) : Core := { c with flags := f }

@[simp] theorem setFlags_rip (c : Core) (f : Flags) : (setFlags c f).rip = c.rip := rfl

/-! ## Arithmetic -/

section Arith

variable {n : Nat}

/-- `x + y + c`. -/
def adcValue (x y : BitVec n) (c : Bool) : BitVec n := x + y + BitVec.ofNat n c.toNat

/-- The unsigned carry out of `x + y + c`. -/
def adcCarry (x y : BitVec n) (c : Bool) : Bool := decide (2 ^ n ≤ x.toNat + y.toNat + c.toNat)

/-- `x - (y + c)`. -/
def sbbValue (x y : BitVec n) (c : Bool) : BitVec n := x - y - BitVec.ofNat n c.toNat

/-- The borrow of `x - (y + c)`. -/
def sbbBorrow (x y : BitVec n) (c : Bool) : Bool := decide (x.toNat < y.toNat + c.toNat)

/-- ADC: CF the unsigned carry, OF the signed overflow, AF the carry out of
bit 3, SF, ZF, PF from the result. -/
def adcFlags (x y : BitVec n) (c : Bool) : Flags :=
  let r := adcValue x y c
  ⟨some (adcCarry x y c), some (parityN r), some ((x ^^^ y ^^^ r).getLsbD 4), some (isZeroN r),
    some r.msb, some (decide (r.toInt ≠ x.toInt + y.toInt + c.toNat))⟩

/-- SBB: CF the borrow, OF the signed overflow, AF the borrow out of bit 3. -/
def sbbFlags (x y : BitVec n) (c : Bool) : Flags :=
  let r := sbbValue x y c
  ⟨some (sbbBorrow x y c), some (parityN r), some ((x ^^^ y ^^^ r).getLsbD 4), some (isZeroN r),
    some r.msb, some (decide (r.toInt ≠ x.toInt - y.toInt - c.toNat))⟩

def CarryOp.value : CarryOp → BitVec n → BitVec n → Bool → BitVec n
  | .adc => adcValue | .sbb => sbbValue

def CarryOp.flags : CarryOp → BitVec n → BitVec n → Bool → Flags
  | .adc => adcFlags | .sbb => sbbFlags

/-- The full signed product, as the low and high halves. -/
def imulWide (x y : BitVec n) : BitVec n × BitVec n :=
  let p := x.toInt * y.toInt
  (BitVec.ofInt n p, BitVec.ofInt n (p / 2 ^ n))

/-- The signed product does not fit in `n` bits. -/
def imulWideOverflow (x y : BitVec n) : Bool :=
  decide ((BitVec.ofInt n (x.toInt * y.toInt)).toInt ≠ x.toInt * y.toInt)

/-- The unsigned product, as the low and high halves. -/
def mulWide (x y : BitVec n) : BitVec n × BitVec n :=
  let p := x.toNat * y.toNat
  (BitVec.ofNat n p, BitVec.ofNat n (p / 2 ^ n))

/-- Deposit the low bits of `src` at the set bits of `mask` (PDEP). -/
def pdepN (src mask : BitVec n) : BitVec n :=
  BitVec.ofNat n ((List.range n).foldl (fun (acc : Nat × Nat) i =>
    if mask.getLsbD i then ((if src.getLsbD acc.2 then acc.1 + 2 ^ i else acc.1), acc.2 + 1)
    else acc) (0, 0)).1

/-- Gather the bits of `src` at the set bits of `mask` into the low bits (PEXT). -/
def pextN (src mask : BitVec n) : BitVec n :=
  BitVec.ofNat n ((List.range n).foldl (fun (acc : Nat × Nat) i =>
    if mask.getLsbD i then ((if src.getLsbD i then acc.1 + 2 ^ acc.2 else acc.1), acc.2 + 1)
    else acc) (0, 0)).1

/-- BEXTR: `len` bits of `src` from bit `start`, with control `start = ctl[7:0]`,
`len = ctl[15:8]`; bits beyond the operand read as zero. -/
def bextrN (src ctl : BitVec n) : BitVec n :=
  let start := ctl.toNat % 256
  let len := (ctl.toNat / 256) % 256
  BitVec.ofNat n ((src.toNat >>> start) % 2 ^ len)

/-- BZHI: clear the bits from `idx[7:0]` up. -/
def bzhiN (src idx : BitVec n) : BitVec n :=
  let k := idx.toNat % 256
  if k < n then src &&& BitVec.ofNat n (2 ^ k - 1) else src

end Arith

/-! ## Flags of the BMI instructions -/

section BmiFlags

variable {n : Nat}

/-- ANDN: SF, ZF from the result, CF and OF cleared, AF and PF undefined. -/
def andnFlags (r : BitVec n) : Flags :=
  ⟨some false, none, none, some (isZeroN r), some r.msb, some false⟩

/-- BEXTR: ZF from the result, CF and OF cleared, AF, SF, PF undefined. -/
def bextrFlags (r : BitVec n) : Flags :=
  ⟨some false, none, none, some (isZeroN r), none, some false⟩

/-- BZHI: ZF, SF from the result, CF set when the index is at least the operand
size, OF cleared, AF and PF undefined. -/
def bzhiFlags (r idx : BitVec n) : Flags :=
  ⟨some (decide (n ≤ idx.toNat % 256)), none, none, some (isZeroN r), some r.msb, some false⟩

/-- BLSR, BLSMSK, BLSI. -/
def BlsOp.value : BlsOp → BitVec n → BitVec n
  | .blsr, x => (x - 1) &&& x
  | .blsmsk, x => (x - 1) ^^^ x
  | .blsi, x => (0 - x) &&& x

/-- BLSR: ZF, SF from the result, CF set when the source is zero. BLSMSK: SF
from the result, CF set when the source is zero, ZF cleared. BLSI: ZF, SF from
the result, CF set when the source is nonzero. OF is cleared and AF, PF are
undefined for all three. -/
def BlsOp.flags : BlsOp → BitVec n → Flags
  | .blsr, x => ⟨some (isZeroN x), none, none, some (isZeroN ((x - 1) &&& x)),
      some ((x - 1) &&& x).msb, some false⟩
  | .blsmsk, x => ⟨some (isZeroN x), none, none, some false, some ((x - 1) ^^^ x).msb, some false⟩
  | .blsi, x => ⟨some (!isZeroN x), none, none, some (isZeroN ((0 - x) &&& x)),
      some ((0 - x) &&& x).msb, some false⟩

end BmiFlags

/-! ## Register effects -/

/-- The three-operand VEX forms on their operand values: `v` is the `vvvv`
register's value and `y` the `r/m` operand's. -/
def vopCore (op : Vop) (sz : Sz) (dst vr : Reg) (y : BitVec sz.bits) (c : Core) : Core :=
  let v := sz.read c vr
  match op with
  | .andn => setFlags (sz.write c dst (~~~v &&& y)) (andnFlags (~~~v &&& y))
  | .bextr => setFlags (sz.write c dst (bextrN y v)) (bextrFlags (bextrN y v))
  | .bzhi => setFlags (sz.write c dst (bzhiN y v)) (bzhiFlags (bzhiN y v) v)
  | .pdep => sz.write c dst (pdepN v y)
  | .pext => sz.write c dst (pextN v y)
  | .sarx => sz.write c dst (y.sshiftRight (v.toNat % sz.bits))
  | .shlx => sz.write c dst (y <<< (v.toNat % sz.bits))
  | .shrx => sz.write c dst (y >>> (v.toNat % sz.bits))
  | .mulx =>
    let p := mulWide (sz.read c .rdx) y
    sz.write (sz.write c vr p.1) dst p.2

theorem vopCore_rip (op : Vop) (sz : Sz) (dst vr : Reg) (y : BitVec sz.bits) (c : Core) :
    (vopCore op sz dst vr y c).rip = c.rip := by
  cases op <;> rfl

/-- BLSR/BLSMSK/BLSI on the source value. -/
def blsCore (op : BlsOp) (sz : Sz) (dst : Reg) (x : BitVec sz.bits) (c : Core) : Core :=
  setFlags (sz.write c dst (op.value x)) (op.flags x)

/-- `imul dst, src, imm` on the source value and the sign-extended immediate. -/
def imul3Core (sz : Sz) (dst : Reg) (y imm : BitVec sz.bits) (c : Core) : Core :=
  setFlags (sz.write c dst (y * imm)) (imulFlags y imm)

/-- One-operand IMUL: EDX:EAX (RDX:RAX) is the signed product of EAX (RAX) and
the source. CF = OF = the product does not fit in the low half; SF, ZF, AF, PF
undefined. -/
def imul1Core (sz : Sz) (y : BitVec sz.bits) (c : Core) : Core :=
  let x := sz.read c .rax
  let p := imulWide x y
  setFlags (sz.write (sz.write c .rax p.1) .rdx p.2) (mulFlags (imulWideOverflow x y))

/-- XADD: the destination gets the sum and the source the old destination. -/
def xaddCore (sz : Sz) (dst src : Reg) (c : Core) : Core :=
  let x := sz.read c dst
  let y := sz.read c src
  setFlags (sz.write (sz.write c src x) dst (x + y)) (addFlagsN x y)

/-- CMPXCHG: compare the accumulator with the destination (flags of CMP); if
equal the destination gets the source, otherwise the accumulator gets the
destination. -/
def cmpxchgCore (sz : Sz) (dst src : Reg) (c : Core) : Core :=
  let a := sz.read c .rax
  let x := sz.read c dst
  let c' := if a = x then sz.write c dst (sz.read c src) else sz.write c .rax x
  setFlags c' (subFlagsN a x)

/-- The bit offset of BT with a register base, or with an immediate. -/
def bitOffset (sz : Sz) (k : Nat) : Nat := k % sz.bits

/-- BT/BTS/BTR/BTC on a value: the selected bit and the new value. -/
def BitOp.apply {n : Nat} (op : BitOp) (x : BitVec n) (k : Nat) : BitVec n :=
  match op with
  | .bt => x
  | .bts => x ||| BitVec.ofNat n (2 ^ k)
  | .btr => x &&& ~~~(BitVec.ofNat n (2 ^ k))
  | .btc => x ^^^ BitVec.ofNat n (2 ^ k)

/-- BT flags: CF is the selected bit, ZF unchanged, OF, SF, AF, PF undefined. -/
def bitFlags (old : Flags) (b : Bool) : Flags :=
  { old with carry := some b, overflow := none, sign := none, adjust := none, parity := none }

/-- The masked SHLD/SHRD count. -/
def shdCount (sz : Sz) (count : ShdCount) (c : Core) : Nat :=
  match count with
  | .cl => (c.read .rcx).toNat % sz.bits
  | .imm n => n.toNat % sz.bits

/-- SHLD/SHRD by a nonzero count `k < n`: result and flags. CF is the last bit
shifted out of the destination, OF (for `k = 1`) a sign change, SF, ZF, PF
from the result, AF undefined. -/
def shdValue {n : Nat} (right : Bool) (x y : BitVec n) (k : Nat) : BitVec n :=
  if right then (x >>> k) ||| (y <<< (n - k)) else (x <<< k) ||| (y >>> (n - k))

def shdFlags {n : Nat} (right : Bool) (x y : BitVec n) (k : Nat) : Flags :=
  let r := shdValue right x y k
  ⟨some (if right then x.getLsbD (k - 1) else x.getLsbD (n - k)), some (parityN r), none,
    some (isZeroN r), some r.msb, if k = 1 then some (r.msb != x.msb) else none⟩

/-! ## Execution on the integer state -/

/-- Read-modify-write of an `r/m` destination with new flags. -/
def rmw (sz : Sz) (dst : RM) (c : Core) (memory : Memory) (next : Word)
    (f : BitVec sz.bits → BitVec sz.bits × Flags) : Out :=
  match readRM sz dst c memory next with
  | none => .dataFault
  | some x =>
    let r := f x
    Out.ofOption ((writeRM sz dst r.1 c memory next).map fun p => (setFlags p.1 r.2, p.2))

/-- ADC/SBB on an `r/m` destination with second operand `y`. -/
def carryRM (op : CarryOp) (sz : Sz) (dst : RM) (y : BitVec sz.bits) (c : Core) (memory : Memory)
    (next : Word) : Out :=
  match c.flags.carry with
  | none => .unmodeled
  | some cf => rmw sz dst c memory next fun x => (op.value x y cf, op.flags x y cf)

/-- Execute on the integer state; `next` is the address of the next
instruction. RIP is not changed. -/
def run (i : Instr) (next : Word) (c : Core) (memory : Memory) : Out :=
  match i with
  | .carry op sz dst src => carryRM op sz dst (sz.read c src) c memory next
  | .carryR op sz dst src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => carryRM op sz (.reg dst) y c memory next
  | .carryI op sz dst imm => carryRM op sz dst (imm.signExtend sz.bits) c memory next
  | .carryI8 op sz dst imm => carryRM op sz dst (imm.signExtend sz.bits) c memory next
  | .carryA op sz imm => carryRM op sz (.reg .rax) (imm.signExtend sz.bits) c memory next
  | .imulI sz dst src imm =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => .ok (imul3Core sz dst y (imm.signExtend sz.bits) c) memory
  | .imulI8 sz dst src imm =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => .ok (imul3Core sz dst y (imm.signExtend sz.bits) c) memory
  | .imul1 sz src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => .ok (imul1Core sz y c) memory
  | .testI sz dst imm =>
    match readRM sz dst c memory next with
    | none => .dataFault
    | some x => .ok (setFlags c (logicFlagsN (x &&& imm.signExtend sz.bits))) memory
  | .pushI imm =>
    let sp := c.read .rsp - 8
    Out.ofOption ((storeN memory sp 8 (imm.signExtend 64)).map fun m => (c.write .rsp sp, m))
  | .pushI8 imm =>
    let sp := c.read .rsp - 8
    Out.ofOption ((storeN memory sp 8 (imm.signExtend 64)).map fun m => (c.write .rsp sp, m))
  | .scan rev sz dst src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y =>
      if y = 0 then .unmodeled
      else
        let k := if rev then sz.bits - 1 - lzcntN y else tzcntN y
        .ok (setFlags (sz.write c dst (BitVec.ofNat sz.bits k))
          ⟨none, none, none, some false, none, none⟩) memory
  | .bit op sz dst src =>
    match dst with
    | .reg r =>
      let x := sz.read c r
      let k := bitOffset sz (sz.read c src).toNat
      let c' := if op = .bt then c else sz.write c r (op.apply x k)
      .ok (setFlags c' (bitFlags c.flags (x.getLsbD k))) memory
    | .mem m =>
      let o := (sz.read c src).toInt
      let addr := m.addr c next + BitVec.ofInt 64 ((o / sz.bits) * sz.bytes)
      let k := (o % sz.bits).toNat
      match loadN memory addr sz.bytes with
      | none => .unmodeled
      | some w =>
        let x : BitVec sz.bits := w.setWidth sz.bits
        let c' := setFlags c (bitFlags c.flags (x.getLsbD k))
        if op = .bt then .ok c' memory
        else
          match storeN memory addr sz.bytes ((op.apply x k).setWidth 64) with
          | none => .unmodeled
          | some memory' => .ok c' memory'
  | .bitI op sz dst imm =>
    match readRM sz dst c memory next with
    | none => .dataFault
    | some x =>
      let k := bitOffset sz imm.toNat
      let fl := bitFlags c.flags (x.getLsbD k)
      if op = .bt then .ok (setFlags c fl) memory
      else Out.ofOption ((writeRM sz dst (op.apply x k) c memory next).map fun p =>
        (setFlags p.1 fl, p.2))
  | .shd right sz dst src count =>
    let k := shdCount sz count c
    let y := sz.read c src
    if k = 0 then
      match dst with
      | .reg r => .ok (sz.write c r (sz.read c r)) memory
      | .mem _ => .unmodeled
    else rmw sz dst c memory next fun x => (shdValue right x y k, shdFlags right x y k)
  | .xadd sz dst src => .ok (xaddCore sz dst src c) memory
  | .cmpxchg sz dst src => .ok (cmpxchgCore sz dst src c) memory
  | .adx op sz dst src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y =>
      let x := sz.read c dst
      match op with
      | .adcx =>
        match c.flags.carry with
        | none => .unmodeled
        | some cf =>
          .ok (setFlags (sz.write c dst (adcValue x y cf))
            { c.flags with carry := some (adcCarry x y cf) }) memory
      | .adox =>
        match c.flags.overflow with
        | none => .unmodeled
        | some of =>
          .ok (setFlags (sz.write c dst (adcValue x y of))
            { c.flags with overflow := some (adcCarry x y of) }) memory
  | .movbeLoad sz dst src =>
    match readRM sz (.mem src) c memory next with
    | none => .dataFault
    | some v => .ok (sz.write c dst (byteSwap sz v)) memory
  | .movbeStore sz dst src =>
    Out.ofOption (writeRM sz (.mem dst) (byteSwap sz (sz.read c src)) c memory next)
  | .vop op sz dst v src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => .ok (vopCore op sz dst v y c) memory
  | .bls op sz dst src =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some x => .ok (blsCore op sz dst x c) memory
  | .rorx sz dst src imm =>
    match readRM sz src c memory next with
    | none => .dataFault
    | some y => .ok (sz.write c dst (y.rotateRight (imm.toNat % sz.bits))) memory

/-- Execute one instruction of the lane on the extended state, with the
consumed length. -/
def exec (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  match run i (s.rip + BitVec.ofNat 64 length) s.core memory with
  | .ok c m => .retired ((s.setCore c).advance length) m
  | .dataFault => .fault .dataFault
  | .unmodeled => .unmodeled

end Silmaril.X86.Features.IntExt
