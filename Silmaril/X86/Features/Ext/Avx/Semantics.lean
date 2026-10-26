module

public import Silmaril.X86.Features.Ext.Avx.Encoding
public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Float.Semantics

/-!
# Semantics of the `avx` lane

`exec` on the extended state (`Features.State`), written from the operation
sections of the Intel SDM Vol. 2 pages. A VEX-encoded destination register is
written with `State.writeXmmVex` (VEX.128: bits 511:128 zeroed) or
`State.writeYmmVex` (VEX.256: bits 511:256 zeroed); RIP advances by the
instruction length.

Values are computed on 256 bits: a VEX.128 source is its XMM register (or its
16-byte memory operand) zero-extended, and only bits 127:0 of the result are
written. Every operation that VEX.256 applies "in each 128-bit lane"
(`inLane`) therefore gives the VEX.128 result on the low lane.

## Operand roles

`Sem` names the roles of the form's fields (the `ops` column of
`scripts/x86-features/avx_ops.py`): ModRM.reg is the destination `V`,
VEX.vvvv the first source `H`, ModRM.rm the second source `W` (a vector
register or memory of `memBytes` bytes), and imm8 the immediate; `vmI` forms
(the shifts by an immediate) write VEX.vvvv; `is4` forms read a fourth
register from imm8[7:4]; `store` forms write ModRM.rm.

## Fidelity

Modelled exactly (and checked against the host, `Vectors/`): the integer
arithmetic, logic, comparison, saturation, multiply, average, sum of absolute
differences, sign, absolute value, pack, unpack, byte shuffle, horizontal
add/subtract, shift (by imm8, by an XMM count and per element), widening
moves, the bitwise floating-point forms (`vandps` …), shuffles, permutes,
blends, broadcasts, 128-bit inserts and extracts, the full-width moves and
stores, VZEROUPPER and VZEROALL.

Floating-point ADD/SUB/MUL/DIV/MIN/MAX/SQRT (packed and scalar) follow
`X86.Float` lane by lane (see below).

`unmodeled` (chaos): floating-point conversions, comparisons, rounding,
horizontal and add-subtract forms, and FMA,
F16C, VEX AES/PCLMUL/GFNI, gathers, masked moves, the scalar and partial
moves (MOVSS/MOVSD/MOVLPS/MOVHPS/MOVD/MOVQ, PINSR/PEXTR, INSERTPS/EXTRACTPS),
the mask extractions to general-purpose registers, PTEST/VTESTPS/VTESTPD
(flags), and PHMINPOSUW.

Memory operands: an access that is not permitted or not backed is
`Fault.dataFault`; a misaligned operand of an aligned form (VMOVDQA, VMOVAPS,
VMOVAPD, VMOVNT*) is #GP(0) (`Fault.generalProtection`) before the access.
Other VEX memory operands need no alignment.
-/

@[expose] public section

namespace Silmaril.X86.Features.Avx

open Silmaril.Process (Memory)
open Silmaril.X86 (Byte)

/-! ## Lanes -/

/-- Lane `i` of width `w`. -/
def lane {n : Nat} (w i : Nat) (v : BitVec n) : BitVec w := v.extractLsb' (i * w) w

/-- The `n`-bit value whose lane `i` of width `w` is `f i`. -/
def ofLanes (n w : Nat) (f : Nat → BitVec w) : BitVec n :=
  BitVec.ofNat n ((List.range (n / w)).foldr (fun i acc => acc + (f i).toNat * 2 ^ (i * w)) 0)

/-- Lane-wise unary operation. -/
def map1 {n : Nat} (w : Nat) (f : BitVec w → BitVec w) (a : BitVec n) : BitVec n :=
  ofLanes n w fun i => f (lane w i a)

/-- Lane-wise binary operation. -/
def map2 {n : Nat} (w : Nat) (f : BitVec w → BitVec w → BitVec w) (a b : BitVec n) : BitVec n :=
  ofLanes n w fun i => f (lane w i a) (lane w i b)

/-- A 128-bit operation applied to each 128-bit lane. -/
def inLane (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) : BitVec 256 :=
  f (a.extractLsb' 128 128) (b.extractLsb' 128 128) ++ f (a.extractLsb' 0 128) (b.extractLsb' 0 128)

/-- Signed saturation to `w` bits. -/
def ssat (w : Nat) (x : Int) : BitVec w :=
  if x > 2 ^ (w - 1) - 1 then BitVec.ofInt w (2 ^ (w - 1) - 1)
  else if x < -2 ^ (w - 1) then BitVec.ofInt w (-2 ^ (w - 1))
  else BitVec.ofInt w x

/-- Unsigned saturation to `w` bits. -/
def usat (w : Nat) (x : Int) : BitVec w :=
  if x < 0 then 0 else if x ≥ 2 ^ w then BitVec.allOnes w else BitVec.ofNat w x.toNat

/-- All ones or all zeros. -/
def mask (w : Nat) (b : Bool) : BitVec w := if b then BitVec.allOnes w else 0

/-- Interleave the low (`high = false`) or high halves of `a` and `b` in lanes of
width `w`: `a₀ b₀ a₁ b₁ …`. -/
def unpack (w : Nat) (high : Bool) (a b : BitVec 128) : BitVec 128 :=
  let base := if high then 64 / w else 0
  ofLanes 128 w fun i => lane w (base + i / 2) (if i % 2 = 0 then a else b)

/-- Shift kinds: logical right, arithmetic right, left. -/
inductive Shift where
  | srl | sra | sll
  deriving DecidableEq, Repr

/-- Shift one element by `c`; logical shifts by `c ≥ w` give 0, arithmetic
ones fill with the sign. -/
def Shift.lane {w : Nat} (k : Shift) (c : Nat) (a : BitVec w) : BitVec w :=
  match k with
  | .srl => if c ≥ w then 0 else a >>> c
  | .sra => a.sshiftRight (min c (w - 1))
  | .sll => if c ≥ w then 0 else a <<< c

/-- Absolute value (`0x80…` stays as it is). -/
def absLane {w : Nat} (a : BitVec w) : BitVec w := if a.msb then -a else a

/-! ## Integer operations (SDM Vol. 2, the operation sections) -/

/-- `op(src1, src2)` of the two-source integer forms, `none` for the others.
`w` is VEX.W (the element size of VPSRLVD/Q and VPSLLVD/Q). -/
def intOp? (op : Op) (w : Bool) : Option (BitVec 256 → BitVec 256 → BitVec 256) :=
  match op with
  | .paddb => some (map2 8 (· + ·))
  | .paddw => some (map2 16 (· + ·))
  | .paddd => some (map2 32 (· + ·))
  | .paddq => some (map2 64 (· + ·))
  | .psubb => some (map2 8 (· - ·))
  | .psubw => some (map2 16 (· - ·))
  | .psubd => some (map2 32 (· - ·))
  | .psubq => some (map2 64 (· - ·))
  | .paddsb => some (map2 8 fun a b => ssat 8 (a.toInt + b.toInt))
  | .paddsw => some (map2 16 fun a b => ssat 16 (a.toInt + b.toInt))
  | .paddusb => some (map2 8 fun a b => usat 8 (a.toNat + b.toNat))
  | .paddusw => some (map2 16 fun a b => usat 16 (a.toNat + b.toNat))
  | .psubsb => some (map2 8 fun a b => ssat 8 (a.toInt - b.toInt))
  | .psubsw => some (map2 16 fun a b => ssat 16 (a.toInt - b.toInt))
  | .psubusb => some (map2 8 fun a b => usat 8 ((a.toNat : Int) - b.toNat))
  | .psubusw => some (map2 16 fun a b => usat 16 ((a.toNat : Int) - b.toNat))
  | .pmullw => some (map2 16 (· * ·))
  | .pmulhw => some (map2 16 fun a b => BitVec.ofInt 16 ((a.toInt * b.toInt) / 2 ^ 16))
  | .pmulhuw => some (map2 16 fun a b => BitVec.ofNat 16 ((a.toNat * b.toNat) / 2 ^ 16))
  | .pmuludq => some (map2 64 fun a b => BitVec.ofNat 64 ((a.setWidth 32).toNat * (b.setWidth 32).toNat))
  | .pmuldq => some (map2 64 fun a b => BitVec.ofInt 64 ((a.setWidth 32).toInt * (b.setWidth 32).toInt))
  | .pmulld => some (map2 32 (· * ·))
  | .pmaddwd => some fun a b => ofLanes 256 32 fun i =>
      BitVec.ofInt 32 ((lane 16 (2 * i) a).toInt * (lane 16 (2 * i) b).toInt +
        (lane 16 (2 * i + 1) a).toInt * (lane 16 (2 * i + 1) b).toInt)
  | .pmaddubsw => some fun a b => ofLanes 256 16 fun i =>
      ssat 16 ((lane 8 (2 * i) a).toNat * (lane 8 (2 * i) b).toInt +
        (lane 8 (2 * i + 1) a).toNat * (lane 8 (2 * i + 1) b).toInt)
  | .pmulhrsw => some (map2 16 fun a b => BitVec.ofInt 16 (((a.toInt * b.toInt) / 2 ^ 14 + 1) / 2))
  | .pand | .andps | .andpd => some (· &&& ·)
  | .pandn | .andnps | .andnpd => some fun a b => ~~~a &&& b
  | .por | .orps | .orpd => some (· ||| ·)
  | .pxor | .xorps | .xorpd => some (· ^^^ ·)
  | .pcmpeqb => some (map2 8 fun a b => mask 8 (a == b))
  | .pcmpeqw => some (map2 16 fun a b => mask 16 (a == b))
  | .pcmpeqd => some (map2 32 fun a b => mask 32 (a == b))
  | .pcmpeqq => some (map2 64 fun a b => mask 64 (a == b))
  | .pcmpgtb => some (map2 8 fun a b => mask 8 (decide (a.toInt > b.toInt)))
  | .pcmpgtw => some (map2 16 fun a b => mask 16 (decide (a.toInt > b.toInt)))
  | .pcmpgtd => some (map2 32 fun a b => mask 32 (decide (a.toInt > b.toInt)))
  | .pcmpgtq => some (map2 64 fun a b => mask 64 (decide (a.toInt > b.toInt)))
  | .pminub => some (map2 8 fun a b => if a.toNat ≤ b.toNat then a else b)
  | .pminuw => some (map2 16 fun a b => if a.toNat ≤ b.toNat then a else b)
  | .pminud => some (map2 32 fun a b => if a.toNat ≤ b.toNat then a else b)
  | .pmaxub => some (map2 8 fun a b => if a.toNat ≥ b.toNat then a else b)
  | .pmaxuw => some (map2 16 fun a b => if a.toNat ≥ b.toNat then a else b)
  | .pmaxud => some (map2 32 fun a b => if a.toNat ≥ b.toNat then a else b)
  | .pminsb => some (map2 8 fun a b => if a.toInt ≤ b.toInt then a else b)
  | .pminsw => some (map2 16 fun a b => if a.toInt ≤ b.toInt then a else b)
  | .pminsd => some (map2 32 fun a b => if a.toInt ≤ b.toInt then a else b)
  | .pmaxsb => some (map2 8 fun a b => if a.toInt ≥ b.toInt then a else b)
  | .pmaxsw => some (map2 16 fun a b => if a.toInt ≥ b.toInt then a else b)
  | .pmaxsd => some (map2 32 fun a b => if a.toInt ≥ b.toInt then a else b)
  | .pavgb => some (map2 8 fun a b => BitVec.ofNat 8 ((a.toNat + b.toNat + 1) / 2))
  | .pavgw => some (map2 16 fun a b => BitVec.ofNat 16 ((a.toNat + b.toNat + 1) / 2))
  | .psadbw => some fun a b => ofLanes 256 64 fun j => BitVec.ofNat 64
      ((List.range 8).foldr (fun k acc => acc +
        (((lane 8 (8 * j + k) a).toNat : Int) - (lane 8 (8 * j + k) b).toNat).natAbs) 0)
  | .psignb => some (map2 8 fun a b => if b.toInt < 0 then -a else if b = 0 then 0 else a)
  | .psignw => some (map2 16 fun a b => if b.toInt < 0 then -a else if b = 0 then 0 else a)
  | .psignd => some (map2 32 fun a b => if b.toInt < 0 then -a else if b = 0 then 0 else a)
  | .packsswb => some (inLane fun a b => ofLanes 128 8 fun i =>
      ssat 8 (lane 16 (i % 8) (if i < 8 then a else b)).toInt)
  | .packuswb => some (inLane fun a b => ofLanes 128 8 fun i =>
      usat 8 (lane 16 (i % 8) (if i < 8 then a else b)).toInt)
  | .packssdw => some (inLane fun a b => ofLanes 128 16 fun i =>
      ssat 16 (lane 32 (i % 4) (if i < 4 then a else b)).toInt)
  | .packusdw => some (inLane fun a b => ofLanes 128 16 fun i =>
      usat 16 (lane 32 (i % 4) (if i < 4 then a else b)).toInt)
  | .punpcklbw => some (inLane (unpack 8 false))
  | .punpcklwd => some (inLane (unpack 16 false))
  | .punpckldq | .unpcklps => some (inLane (unpack 32 false))
  | .punpcklqdq | .unpcklpd => some (inLane (unpack 64 false))
  | .punpckhbw => some (inLane (unpack 8 true))
  | .punpckhwd => some (inLane (unpack 16 true))
  | .punpckhdq | .unpckhps => some (inLane (unpack 32 true))
  | .punpckhqdq | .unpckhpd => some (inLane (unpack 64 true))
  | .pshufb => some (inLane fun a b => ofLanes 128 8 fun i =>
      let c := lane 8 i b
      if c.getLsbD 7 then 0 else lane 8 (c.toNat % 16) a)
  | .phaddw => some (inLane fun a b => ofLanes 128 16 fun i =>
      let x := if i < 4 then a else b
      lane 16 (2 * (i % 4)) x + lane 16 (2 * (i % 4) + 1) x)
  | .phaddd => some (inLane fun a b => ofLanes 128 32 fun i =>
      let x := if i < 2 then a else b
      lane 32 (2 * (i % 2)) x + lane 32 (2 * (i % 2) + 1) x)
  | .phaddsw => some (inLane fun a b => ofLanes 128 16 fun i =>
      let x := if i < 4 then a else b
      ssat 16 ((lane 16 (2 * (i % 4)) x).toInt + (lane 16 (2 * (i % 4) + 1) x).toInt))
  | .phsubw => some (inLane fun a b => ofLanes 128 16 fun i =>
      let x := if i < 4 then a else b
      lane 16 (2 * (i % 4)) x - lane 16 (2 * (i % 4) + 1) x)
  | .phsubd => some (inLane fun a b => ofLanes 128 32 fun i =>
      let x := if i < 2 then a else b
      lane 32 (2 * (i % 2)) x - lane 32 (2 * (i % 2) + 1) x)
  | .phsubsw => some (inLane fun a b => ofLanes 128 16 fun i =>
      let x := if i < 4 then a else b
      ssat 16 ((lane 16 (2 * (i % 4)) x).toInt - (lane 16 (2 * (i % 4) + 1) x).toInt))
  | .psrlw => some fun a b => map1 16 (Shift.srl.lane (lane 64 0 b).toNat) a
  | .psrld => some fun a b => map1 32 (Shift.srl.lane (lane 64 0 b).toNat) a
  | .psrlq => some fun a b => map1 64 (Shift.srl.lane (lane 64 0 b).toNat) a
  | .psraw => some fun a b => map1 16 (Shift.sra.lane (lane 64 0 b).toNat) a
  | .psrad => some fun a b => map1 32 (Shift.sra.lane (lane 64 0 b).toNat) a
  | .psllw => some fun a b => map1 16 (Shift.sll.lane (lane 64 0 b).toNat) a
  | .pslld => some fun a b => map1 32 (Shift.sll.lane (lane 64 0 b).toNat) a
  | .psllq => some fun a b => map1 64 (Shift.sll.lane (lane 64 0 b).toNat) a
  | .psrlv => some fun a b =>
      if w then map2 64 (fun x c => Shift.srl.lane c.toNat x) a b
      else map2 32 (fun x c => Shift.srl.lane c.toNat x) a b
  | .psllv => some fun a b =>
      if w then map2 64 (fun x c => Shift.sll.lane c.toNat x) a b
      else map2 32 (fun x c => Shift.sll.lane c.toNat x) a b
  | .psrav => some (map2 32 fun x c => Shift.sra.lane c.toNat x)
  | .permd | .permps => some fun a b => ofLanes 256 32 fun i => lane 32 ((lane 32 i a).toNat % 8) b
  | .permilpsV => some (inLane fun a b => ofLanes 128 32 fun i => lane 32 ((lane 32 i b).toNat % 4) a)
  | .permilpdV => some (inLane fun a b => ofLanes 128 64 fun i =>
      lane 64 (if (lane 64 i b).getLsbD 1 then 1 else 0) a)
  | _ => none

/-- `op(src1, src2, imm8)` of the two-source forms with an immediate. -/
def intOpI? (op : Op) : Option (Byte → BitVec 256 → BitVec 256 → BitVec 256) :=
  match op with
  | .palignr => some fun imm => inLane fun a b =>
      let k := imm.toNat
      if k ≥ 32 then 0 else ((a ++ b) >>> (8 * k)).setWidth 128
  | .pblendw => some fun imm a b => ofLanes 256 16 fun i =>
      lane 16 i (if imm.getLsbD (i % 8) then b else a)
  | .pblendd => some fun imm a b => ofLanes 256 32 fun i =>
      lane 32 i (if imm.getLsbD i then b else a)
  | .blendps => some fun imm a b => ofLanes 256 32 fun i =>
      lane 32 i (if imm.getLsbD i then b else a)
  | .blendpd => some fun imm a b => ofLanes 256 64 fun i =>
      lane 64 i (if imm.getLsbD i then b else a)
  | .shufps => some fun imm => inLane fun a b => ofLanes 128 32 fun i =>
      lane 32 ((imm.toNat >>> (2 * i)) % 4) (if i < 2 then a else b)
  | .shufpd => some fun imm a b => ofLanes 256 64 fun i =>
      lane 64 (2 * (i / 2) + (if imm.getLsbD i then 1 else 0)) (if i % 2 = 0 then a else b)
  | .perm2i128 | .perm2f128 => some fun imm a b =>
      let sel (c : Nat) : BitVec 128 :=
        if (c >>> 3) % 2 = 1 then 0
        else match c % 4 with
          | 0 => a.extractLsb' 0 128
          | 1 => a.extractLsb' 128 128
          | 2 => b.extractLsb' 0 128
          | _ => b.extractLsb' 128 128
      sel (imm.toNat >>> 4) ++ sel imm.toNat
  | .inserti128 | .insertf128 => some fun imm a b =>
      if imm.getLsbD 0 then b.extractLsb' 0 128 ++ a.extractLsb' 0 128
      else a.extractLsb' 128 128 ++ b.extractLsb' 0 128
  | _ => none

/-- `op(src, imm8)` of the one-source forms (ModRM.reg ← f(ModRM.rm)); the
immediate is ignored by the forms without one. -/
def unOp? (op : Op) : Option (Byte → BitVec 256 → BitVec 256) :=
  match op with
  | .pabsb => some fun _ => map1 8 absLane
  | .pabsw => some fun _ => map1 16 absLane
  | .pabsd => some fun _ => map1 32 absLane
  | .pshufd | .permilpsI => some fun imm b =>
      inLane (fun x _ => ofLanes 128 32 fun i => lane 32 ((imm.toNat >>> (2 * i)) % 4) x) b b
  | .pshufhw => some fun imm b => inLane (fun x _ => ofLanes 128 16 fun i =>
      if i < 4 then lane 16 i x else lane 16 (4 + (imm.toNat >>> (2 * (i - 4))) % 4) x) b b
  | .pshuflw => some fun imm b => inLane (fun x _ => ofLanes 128 16 fun i =>
      if i < 4 then lane 16 ((imm.toNat >>> (2 * i)) % 4) x else lane 16 i x) b b
  | .permilpdI => some fun imm b => ofLanes 256 64 fun i =>
      lane 64 (2 * (i / 2) + (if imm.getLsbD i then 1 else 0)) b
  | .permq | .permpd => some fun imm b => ofLanes 256 64 fun i =>
      lane 64 ((imm.toNat >>> (2 * i)) % 4) b
  | .pmovsxbw => some fun _ b => ofLanes 256 16 fun i => (lane 8 i b).signExtend 16
  | .pmovsxbd => some fun _ b => ofLanes 256 32 fun i => (lane 8 i b).signExtend 32
  | .pmovsxbq => some fun _ b => ofLanes 256 64 fun i => (lane 8 i b).signExtend 64
  | .pmovsxwd => some fun _ b => ofLanes 256 32 fun i => (lane 16 i b).signExtend 32
  | .pmovsxwq => some fun _ b => ofLanes 256 64 fun i => (lane 16 i b).signExtend 64
  | .pmovsxdq => some fun _ b => ofLanes 256 64 fun i => (lane 32 i b).signExtend 64
  | .pmovzxbw => some fun _ b => ofLanes 256 16 fun i => (lane 8 i b).setWidth 16
  | .pmovzxbd => some fun _ b => ofLanes 256 32 fun i => (lane 8 i b).setWidth 32
  | .pmovzxbq => some fun _ b => ofLanes 256 64 fun i => (lane 8 i b).setWidth 64
  | .pmovzxwd => some fun _ b => ofLanes 256 32 fun i => (lane 16 i b).setWidth 32
  | .pmovzxwq => some fun _ b => ofLanes 256 64 fun i => (lane 16 i b).setWidth 64
  | .pmovzxdq => some fun _ b => ofLanes 256 64 fun i => (lane 32 i b).setWidth 64
  | .movdqa | .movdqu | .movaps | .movapd | .movups | .movupd | .movntdqa | .lddqu =>
      some fun _ b => b
  | .movsldup => some fun _ b => ofLanes 256 32 fun i => lane 32 (2 * (i / 2)) b
  | .movshdup => some fun _ b => ofLanes 256 32 fun i => lane 32 (2 * (i / 2) + 1) b
  | .movddup => some fun _ b => ofLanes 256 64 fun i => lane 64 (2 * (i / 2)) b
  | .pbroadcastb => some fun _ b => ofLanes 256 8 fun _ => lane 8 0 b
  | .pbroadcastw => some fun _ b => ofLanes 256 16 fun _ => lane 16 0 b
  | .pbroadcastd | .broadcastss => some fun _ b => ofLanes 256 32 fun _ => lane 32 0 b
  | .pbroadcastq | .broadcastsd => some fun _ b => ofLanes 256 64 fun _ => lane 64 0 b
  | .broadcastf128 | .broadcasti128 => some fun _ b => b.extractLsb' 0 128 ++ b.extractLsb' 0 128
  | _ => none

/-- The shifts by an immediate: VEX.vvvv ← f(ModRM.rm, imm8). -/
def shiftImm? (op : Op) : Option (Byte → BitVec 256 → BitVec 256) :=
  match op with
  | .psrlwI => some fun imm => map1 16 (Shift.srl.lane imm.toNat)
  | .psrawI => some fun imm => map1 16 (Shift.sra.lane imm.toNat)
  | .psllwI => some fun imm => map1 16 (Shift.sll.lane imm.toNat)
  | .psrldI => some fun imm => map1 32 (Shift.srl.lane imm.toNat)
  | .psradI => some fun imm => map1 32 (Shift.sra.lane imm.toNat)
  | .pslldI => some fun imm => map1 32 (Shift.sll.lane imm.toNat)
  | .psrlqI => some fun imm => map1 64 (Shift.srl.lane imm.toNat)
  | .psllqI => some fun imm => map1 64 (Shift.sll.lane imm.toNat)
  | .psrldq => some fun imm b => inLane (fun x _ =>
      if imm.toNat ≥ 16 then 0 else x >>> (8 * imm.toNat)) b b
  | .pslldq => some fun imm b => inLane (fun x _ =>
      if imm.toNat ≥ 16 then 0 else x <<< (8 * imm.toNat)) b b
  | _ => none

/-- The variable blends: `op(src1, src2, mask)` with the mask register in
imm8[7:4]; an element of `src2` is taken where the mask element's top bit is
set. -/
def blendV? (op : Op) : Option (BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256) :=
  match op with
  | .pblendvb => some fun a b m => ofLanes 256 8 fun i => if (lane 8 i m).msb then lane 8 i b else lane 8 i a
  | .blendvps => some fun a b m => ofLanes 256 32 fun i =>
      if (lane 32 i m).msb then lane 32 i b else lane 32 i a
  | .blendvpd => some fun a b m => ofLanes 256 64 fun i =>
      if (lane 64 i m).msb then lane 64 i b else lane 64 i a
  | _ => none

/-- The full-width stores: ModRM.rm ← ModRM.reg (`extract`: the 128-bit lane
imm8[0] of the YMM register). -/
inductive StoreKind where
  | full
  | extract
  deriving DecidableEq, Repr

def store? (op : Op) : Option StoreKind :=
  match op with
  | .movdqaSt | .movdquSt | .movapsSt | .movapdSt | .movupsSt | .movupdSt
  | .movntdq | .movntps | .movntpd => some .full
  | .extracti128 | .extractf128 => some .extract
  | _ => none

/-- Forms whose memory operand must be aligned to its size (#GP(0) otherwise). -/
def aligned (op : Op) : Bool :=
  match op with
  | .movdqa | .movdqaSt | .movaps | .movapsSt | .movapd | .movapdSt
  | .movntdq | .movntps | .movntpd | .movntdqa => true
  | _ => false

/-- The size in bytes of the ModRM.rm memory operand (SDM operand columns:
`Wx` 16, `Wh` half, `Wq4` quarter, `Wq8` eighth of the vector length, `Wd` 4,
`Wq` 8, `Wb` 1, `Ww` 2; the vector length otherwise). -/
def memBytes (op : Op) (l : Bool) : Nat :=
  let v := if l then 32 else 16
  match op with
  | .psrlw | .psrld | .psrlq | .psraw | .psrad | .psllw | .pslld | .psllq
  | .inserti128 | .insertf128 | .broadcastf128 | .broadcasti128
  | .extracti128 | .extractf128 => 16
  | .pmovsxbw | .pmovsxwd | .pmovsxdq | .pmovzxbw | .pmovzxwd | .pmovzxdq => v / 2
  | .pmovsxbd | .pmovsxwq | .pmovzxbd | .pmovzxwq => v / 4
  | .pmovsxbq | .pmovzxbq => v / 8
  | .pbroadcastb => 1
  | .pbroadcastw => 2
  | .pbroadcastd | .broadcastss => 4
  | .pbroadcastq | .broadcastsd => 8
  | .movddup => if l then 32 else 8
  | .addss | .subss | .mulss | .divss | .minss | .maxss | .sqrtss => 4
  | .addsd | .subsd | .mulsd | .divsd | .minsd | .maxsd | .sqrtsd => 8
  | _ => v

/-! ## Floating-point arithmetic

ADD/SUB/MUL/DIV/MIN/MAX/SQRT PS/PD (VEX.128 and VEX.256) and SS/SD apply
`X86.Float`'s scalar operations of the current MXCSR configuration
(`Float.Scalar.binary`, `minMax`, `sqrt`) to every lane, with each lane's
exception conditions; the conditions of all lanes are OR-ed and handled by
`Float.signal` (SDM Vol. 1, §11.5.3): an unmasked exception is #XM with
nothing written, otherwise MXCSR records the flags. The scalar forms (VEX.LIG)
keep bits 127:32 (127:64) of the first source and zero bits 511:128. -/

/-- The operation of a floating-point arithmetic form. -/
inductive FpKind where
  | arith (op : Float.ArithOp)
  | sqrt
  deriving DecidableEq, Repr

/-- The floating-point arithmetic forms: precision, operation, scalar. -/
def fpOp? (op : Op) : Option (Float.Precision × FpKind × Bool) :=
  match op with
  | .addps => some (.single, .arith .add, false)
  | .addpd => some (.double, .arith .add, false)
  | .addss => some (.single, .arith .add, true)
  | .addsd => some (.double, .arith .add, true)
  | .subps => some (.single, .arith .sub, false)
  | .subpd => some (.double, .arith .sub, false)
  | .subss => some (.single, .arith .sub, true)
  | .subsd => some (.double, .arith .sub, true)
  | .mulps => some (.single, .arith .mul, false)
  | .mulpd => some (.double, .arith .mul, false)
  | .mulss => some (.single, .arith .mul, true)
  | .mulsd => some (.double, .arith .mul, true)
  | .divps => some (.single, .arith .div, false)
  | .divpd => some (.double, .arith .div, false)
  | .divss => some (.single, .arith .div, true)
  | .divsd => some (.double, .arith .div, true)
  | .minps => some (.single, .arith .min, false)
  | .minpd => some (.double, .arith .min, false)
  | .minss => some (.single, .arith .min, true)
  | .minsd => some (.double, .arith .min, true)
  | .maxps => some (.single, .arith .max, false)
  | .maxpd => some (.double, .arith .max, false)
  | .maxss => some (.single, .arith .max, true)
  | .maxsd => some (.double, .arith .max, true)
  | .sqrtps => some (.single, .sqrt, false)
  | .sqrtpd => some (.double, .sqrt, false)
  | .sqrtss => some (.single, .sqrt, true)
  | .sqrtsd => some (.double, .sqrt, true)
  | _ => none

/-- Lane `i` of a precision. -/
def flane (p : Float.Precision) (i : Nat) (v : BitVec 256) : Numeric.Float.Bits p.fmt :=
  Float.lane p ((v >>> (i * p.width)).setWidth 128)

/-- OR the conditions of several lanes. -/
def combine (ds : List Float.Detected) : Float.Detected :=
  ds.foldl (fun a d => { pre := a.pre.union d.pre, post := a.post.union d.post }) {}

/-- One lane: `op(x, y)`, or `sqrt(y)`, with its conditions. -/
def fpLane (m : Float.MXCSR) (p : Float.Precision) (k : FpKind) (x y : Numeric.Float.Bits p.fmt) :
    Numeric.Float.Bits p.fmt × Float.Detected :=
  match k with
  | .arith op =>
    match op.kind with
    | .inl a => ((Float.Scalar.binary m p a x y).value, Float.Scalar.binaryDetected m p a x y)
    | .inr isMax =>
      ((Float.Scalar.minMax m p isMax x y).value, Float.Scalar.minMaxDetected m p isMax x y)
  | .sqrt => ((Float.Scalar.sqrt m p y).value, Float.Scalar.sqrtDetected m p y)

/-- The result and conditions of a floating-point arithmetic form on sources
`a` (VEX.vvvv) and `b` (ModRM.rm). -/
def fpEval (m : Float.MXCSR) (p : Float.Precision) (k : FpKind) (scalar l : Bool)
    (a b : BitVec 256) : BitVec 256 × Float.Detected :=
  let f (i : Nat) := fpLane m p k (flane p i a) (flane p i b)
  if scalar then
    (((a >>> p.width) <<< p.width) ||| BitVec.ofNat 256 (f 0).1.toNat, (f 0).2)
  else
    let n := (if l then 256 else 128) / p.width
    (ofLanes 256 p.width (fun i => if i < n then BitVec.ofNat p.width (f i).1.toNat else 0),
      combine ((List.range n).map fun i => (f i).2))

/-! ## Memory and registers -/

/-- The value of little-endian bytes. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The `n` little-endian bytes of `v` modulo `2^(8n)`. -/
def natLe (n v : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (v / 2 ^ (8 * i))

/-- Load `k` bytes, zero-extended to 256 bits. -/
def load (memory : Memory) (address k : Nat) : Option (BitVec 256) :=
  (memory.readBytes address k).map fun bytes => BitVec.ofNat 256 (leNat bytes)

/-- Store the low `k` bytes of `v`. -/
def storeBytes (memory : Memory) (address k : Nat) (v : BitVec 256) : Option Memory :=
  memory.writeBytes address (natLe k v.toNat)

/-- The vector register of a four-bit register number. -/
def vreg (n : BitVec 4) : VReg := ⟨n.toNat, by have := n.isLt; omega⟩

/-- Write a VEX destination: VEX.128 zeroes bits 511:128, VEX.256 bits 511:256. -/
def writeV (s : State) (l : Bool) (n : BitVec 4) (v : BitVec 256) : State :=
  if l then s.writeYmmVex (vreg n) v else s.writeXmmVex (vreg n) (v.setWidth 128)

/-- The effective address of a memory operand. -/
def addr (s : State) (m : Ext.Mem) (next : X86.Word) : Nat := (m.addr s.core next).toNat

/-- Read the ModRM.rm source: a YMM register, or `k` bytes of memory
zero-extended; an aligned form checks the alignment to `k` first. -/
def readSrc (s : State) (memory : Memory) (next : X86.Word) (rm : Opnd) (k : Nat)
    (align : Bool) : Except Fault (BitVec 256) :=
  match rm with
  | .reg n => .ok (s.ymm (vreg n))
  | .mem m =>
    let a := addr s m next
    if align && a % k != 0 then .error .generalProtection
    else match load memory a k with
      | some v => .ok v
      | none => .error .dataFault

/-! ## Execution -/

/-- The value a store form writes: the register, or its 128-bit lane imm8[0]. -/
def storeValue (kind : StoreKind) (l : Bool) (imm : Byte) (v : BitVec 256) : BitVec 256 :=
  match kind with
  | .full => if l then v else (v.setWidth 128).setWidth 256
  | .extract => (if imm.getLsbD 0 then v.extractLsb' 128 128 else v.setWidth 128).setWidth 256

/-- VZEROUPPER: bits 511:128 of ZMM0–ZMM15 zeroed (64-bit mode); ZMM16–31 kept. -/
def zeroUpper (s : State) : State :=
  (List.finRange 16).foldl (fun t (j : Fin 16) =>
    t.writeZmm (j.castLE (by decide)) (((t.zmm (j.castLE (by decide))).setWidth 128).setWidth 512)) s

/-- VZEROALL: ZMM0–ZMM15 zeroed; ZMM16–31 kept. -/
def zeroAll (s : State) : State :=
  (List.finRange 16).foldl (fun t (j : Fin 16) => t.writeZmm (j.castLE (by decide)) 0) s

/-- Retire with a register result. -/
def retireV (s : State) (memory : Memory) (length : Nat) (l : Bool) (n : BitVec 4)
    (r : Except Fault (BitVec 256)) : Result :=
  match r with
  | .ok v => .retired ((writeV s l n v).advance length) memory
  | .error f => .fault f

/-- The zeroing forms. -/
def zero? (op : Op) : Option (State → State) :=
  match op with
  | .zeroupper => some zeroUpper
  | .zeroall => some zeroAll
  | _ => none

/-- Execute one instruction of the lane. -/
def exec (i : Syntax) (length : Nat) (s : State) (memory : Memory) : Result :=
  let x := i.1
  let op := x.op
  let next := s.rip + BitVec.ofNat 64 length
  let src := readSrc s memory next x.rm (memBytes op x.l) (aligned op)
  let a := s.ymm (vreg x.vvvv)
  match intOp? op x.w with
  | some f => retireV s memory length x.l x.reg (src.map (f a))
  | none =>
  match intOpI? op with
  | some f => retireV s memory length x.l x.reg (src.map (f x.imm a))
  | none =>
  match unOp? op with
  | some f => retireV s memory length x.l x.reg (src.map (f x.imm))
  | none =>
  match shiftImm? op with
  | some f => retireV s memory length x.l x.vvvv (src.map (f x.imm))
  | none =>
  match blendV? op with
  | some f => retireV s memory length x.l x.reg
      (src.map fun b => f a b (s.ymm (vreg (x.imm.extractLsb' 4 4))))
  | none =>
  match fpOp? op with
  | some (p, kind, scalar) =>
    match src with
    | .error f => .fault f
    | .ok b =>
      let r := fpEval s.mxcsr p kind scalar x.l a b
      match Float.signal s.mxcsr r.2 with
      | .error m => .fault (.simdException m)
      | .ok m => .retired (((writeV s (!scalar && x.l) x.reg r.1).setMxcsr m).advance length) memory
  | none =>
  match store? op with
  | some kind =>
    let v := storeValue kind x.l x.imm (s.ymm (vreg x.reg))
    let l := kind == .full && x.l
    let k := if l then 32 else 16
    match x.rm with
    | .reg n => .retired ((writeV s l n v).advance length) memory
    | .mem m =>
      let ad := addr s m next
      if aligned op && ad % k != 0 then .fault .generalProtection
      else match storeBytes memory ad k v with
        | some memory' => .retired (s.advance length) memory'
        | none => .fault .dataFault
  | none =>
  match zero? op with
  | some f => .retired ((f s).advance length) memory
  | none => .unmodeled

end Silmaril.X86.Features.Avx
