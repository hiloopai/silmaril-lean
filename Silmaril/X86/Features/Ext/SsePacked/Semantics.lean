module

public import Silmaril.X86.Features.Ext.SsePacked.Encoding
public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Float.Semantics

/-!
# Semantics of the SSE/SSE2 packed lane

`Instr.exec` on the extended state `Features.State`, written from the Intel SDM
Vol. 2 operation sections. Every destination write is a legacy-SSE write
(`State.writeXmmLegacy`: bits 511:128 kept). RIP advances by the instruction
length.

## Floating point

Packed floating-point instructions apply `X86.Float`'s scalar operations
(`Float.Scalar.binary`, `minMax`, `sqrt`, `cmp`, `ofInt`, `toInt`, `convert`,
which are the operations of `MXCSR.profile`) to every lane, with the lane's
exception conditions (`Float.Detected`). The conditions of all lanes are OR-ed
and handled by `Float.signal`, which follows SDM Vol. 1, §11.5.3 (masked,
unmasked, and combinations; pre-computation before post-computation). On #XM
nothing is written and the fault carries the MXCSR the handler observes.

## Fidelity

Exact (and checked against hardware, `Vectors/`): everything except the
following.

* RCPPS, RSQRTPS, RCPSS, RSQRTSS return `unmodeled`. The SDM bounds their
  relative error by `1.5 × 2⁻¹²` but does not determine the result, which
  differs between processor generations.
* MASKMOVDQU is exact when the whole 16-byte span at RDI is writable. If a
  selected byte is not writable it is a data fault. Otherwise (only unselected
  bytes unwritable, where the SDM leaves faulting implementation-specific) it
  is `unmodeled`. Its non-temporal hint is ignored; the 67 address-size
  prefix (EDI) is not decoded.
* MOVNTPS/MOVNTPD/MOVNTDQ are ordinary aligned stores: the non-temporal hint
  and the weak ordering are invisible to a single thread. The fences and the
  prefetches retire without effect for the same reason (prefetches never
  fault).
* Memory operands: a misaligned 16-byte operand of an aligned form raises
  #GP(0) before the access (`Fault.generalProtection`); an access that is not
  permitted or not backed is `Fault.dataFault`. CR0.AM alignment checking,
  AMD's MXCSR.MM and canonical-address checks are not modelled.
-/

@[expose] public section

namespace Silmaril.X86.Features.SsePacked

open Silmaril.Process (Memory)
open Silmaril.X86 (XReg Mem Reg Byte)
open Silmaril.X86.Float (Precision CmpPred LogicOp IntWidth ArithOp Detected MXCSR)

/-! ## Bytes and lanes -/

/-- The value of little-endian bytes. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The `n` little-endian bytes of `v` modulo `2^(8n)`. -/
def natLe (n v : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (v / 2 ^ (8 * i))

@[simp] theorem length_natLe (n v : Nat) : (natLe n v).length = n := by simp [natLe]

/-- Load a `w`-bit value (`w` a multiple of 8). -/
def loadW (w : Nat) (memory : Memory) (address : Nat) : Option (BitVec w) :=
  (memory.readBytes address (w / 8)).map fun bytes => BitVec.ofNat w (leNat bytes)

/-- Store a `w`-bit value. -/
def storeW (w : Nat) (memory : Memory) (address : Nat) (v : BitVec w) : Option Memory :=
  memory.writeBytes address (natLe (w / 8) v.toNat)

/-- Lane `i` of width `w`. -/
def lane (w i : Nat) (v : BitVec 128) : BitVec w := v.extractLsb' (i * w) w

/-- The 128-bit value whose lane `i` of width `w` is `f i mod 2^w`. -/
def ofLanes (w : Nat) (f : Nat → Nat) : BitVec 128 :=
  BitVec.ofNat 128 ((List.range (128 / w)).foldr (fun i acc => acc + f i % 2 ^ w * 2 ^ (i * w)) 0)

/-- Lane-wise binary operation. -/
def map2 (w : Nat) (f : BitVec w → BitVec w → BitVec w) (a b : BitVec 128) : BitVec 128 :=
  ofLanes w fun i => (f (lane w i a) (lane w i b)).toNat

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
width `w`: `a₀ b₀ a₁ b₁ …` (PUNPCKL*, UNPCKLPS/PD and the high forms). -/
def unpack (w : Nat) (high : Bool) (a b : BitVec 128) : BitVec 128 :=
  let base := if high then 64 / w else 0
  ofLanes w fun i => (lane w (base + i / 2) (if i % 2 = 0 then a else b)).toNat

/-- Shift right logical, arithmetic or left, by `c`, saturating the count. -/
def shiftLane (w : Nat) (kind : Fin 3) (c : Nat) (a : BitVec w) : BitVec w :=
  match kind with
  | 0 => if c ≥ w then 0 else a >>> c
  | 1 => a.sshiftRight (min c (w - 1))
  | 2 => if c ≥ w then 0 else a <<< c

/-! ## Integer operations -/

/-- The value of a packed-integer operation, `op(destination, source)` (SDM
Vol. 2, the operation section of each page). -/
def PIntOp.eval (op : PIntOp) (d s : BitVec 128) : BitVec 128 :=
  let cnt := (s.extractLsb' 0 64).toNat
  match op with
  | .paddb => map2 8 (· + ·) d s
  | .paddw => map2 16 (· + ·) d s
  | .paddd => map2 32 (· + ·) d s
  | .paddq => map2 64 (· + ·) d s
  | .psubb => map2 8 (· - ·) d s
  | .psubw => map2 16 (· - ·) d s
  | .psubd => map2 32 (· - ·) d s
  | .psubq => map2 64 (· - ·) d s
  | .paddsb => map2 8 (fun a b => ssat 8 (a.toInt + b.toInt)) d s
  | .paddsw => map2 16 (fun a b => ssat 16 (a.toInt + b.toInt)) d s
  | .paddusb => map2 8 (fun a b => usat 8 (a.toNat + b.toNat)) d s
  | .paddusw => map2 16 (fun a b => usat 16 (a.toNat + b.toNat)) d s
  | .psubsb => map2 8 (fun a b => ssat 8 (a.toInt - b.toInt)) d s
  | .psubsw => map2 16 (fun a b => ssat 16 (a.toInt - b.toInt)) d s
  | .psubusb => map2 8 (fun a b => usat 8 ((a.toNat : Int) - b.toNat)) d s
  | .psubusw => map2 16 (fun a b => usat 16 ((a.toNat : Int) - b.toNat)) d s
  | .pmullw => map2 16 (· * ·) d s
  | .pmulhw => map2 16 (fun a b => (a.signExtend 32 * b.signExtend 32).extractLsb' 16 16) d s
  | .pmulhuw => map2 16 (fun a b => (a.zeroExtend 32 * b.zeroExtend 32).extractLsb' 16 16) d s
  | .pmuludq => map2 64 (fun a b => (a.setWidth 32).zeroExtend 64 * (b.setWidth 32).zeroExtend 64) d s
  | .pmaddwd => map2 32 (fun a b =>
      (a.extractLsb' 0 16).signExtend 32 * (b.extractLsb' 0 16).signExtend 32 +
        (a.extractLsb' 16 16).signExtend 32 * (b.extractLsb' 16 16).signExtend 32) d s
  | .psadbw => map2 64 (fun a b => BitVec.ofNat 64 ((List.range 8).foldr (fun j acc =>
      acc + (((a.extractLsb' (8 * j) 8).toNat : Int) - (b.extractLsb' (8 * j) 8).toNat).natAbs) 0)) d s
  | .pavgb => map2 8 (fun a b => BitVec.ofNat 8 ((a.toNat + b.toNat + 1) / 2)) d s
  | .pavgw => map2 16 (fun a b => BitVec.ofNat 16 ((a.toNat + b.toNat + 1) / 2)) d s
  | .pminub => map2 8 (fun a b => if a.ult b then a else b) d s
  | .pmaxub => map2 8 (fun a b => if b.ult a then a else b) d s
  | .pminsw => map2 16 (fun a b => if a.slt b then a else b) d s
  | .pmaxsw => map2 16 (fun a b => if b.slt a then a else b) d s
  | .pcmpeqb => map2 8 (fun a b => mask 8 (a == b)) d s
  | .pcmpeqw => map2 16 (fun a b => mask 16 (a == b)) d s
  | .pcmpeqd => map2 32 (fun a b => mask 32 (a == b)) d s
  | .pcmpgtb => map2 8 (fun a b => mask 8 (b.slt a)) d s
  | .pcmpgtw => map2 16 (fun a b => mask 16 (b.slt a)) d s
  | .pcmpgtd => map2 32 (fun a b => mask 32 (b.slt a)) d s
  | .pand => d &&& s
  | .pandn => ~~~d &&& s
  | .por => d ||| s
  | .pxor => d ^^^ s
  | .punpcklbw => unpack 8 false d s
  | .punpcklwd => unpack 16 false d s
  | .punpckldq => unpack 32 false d s
  | .punpcklqdq => unpack 64 false d s
  | .punpckhbw => unpack 8 true d s
  | .punpckhwd => unpack 16 true d s
  | .punpckhdq => unpack 32 true d s
  | .punpckhqdq => unpack 64 true d s
  | .packsswb => ofLanes 8 fun i =>
      (ssat 8 (lane 16 (i % 8) (if i < 8 then d else s)).toInt).toNat
  | .packssdw => ofLanes 16 fun i =>
      (ssat 16 (lane 32 (i % 4) (if i < 4 then d else s)).toInt).toNat
  | .packuswb => ofLanes 8 fun i =>
      (usat 8 (lane 16 (i % 8) (if i < 8 then d else s)).toInt).toNat
  | .psrlw => ofLanes 16 fun i => (shiftLane 16 0 cnt (lane 16 i d)).toNat
  | .psrld => ofLanes 32 fun i => (shiftLane 32 0 cnt (lane 32 i d)).toNat
  | .psrlq => ofLanes 64 fun i => (shiftLane 64 0 cnt (lane 64 i d)).toNat
  | .psraw => ofLanes 16 fun i => (shiftLane 16 1 cnt (lane 16 i d)).toNat
  | .psrad => ofLanes 32 fun i => (shiftLane 32 1 cnt (lane 32 i d)).toNat
  | .psllw => ofLanes 16 fun i => (shiftLane 16 2 cnt (lane 16 i d)).toNat
  | .pslld => ofLanes 32 fun i => (shiftLane 32 2 cnt (lane 32 i d)).toNat
  | .psllq => ofLanes 64 fun i => (shiftLane 64 2 cnt (lane 64 i d)).toNat

/-- The value of a shift by an immediate. -/
def PShiftOp.eval (op : PShiftOp) (imm : Byte) (d : BitVec 128) : BitVec 128 :=
  let c := imm.toNat
  match op with
  | .psrlw => ofLanes 16 fun i => (shiftLane 16 0 c (lane 16 i d)).toNat
  | .psraw => ofLanes 16 fun i => (shiftLane 16 1 c (lane 16 i d)).toNat
  | .psllw => ofLanes 16 fun i => (shiftLane 16 2 c (lane 16 i d)).toNat
  | .psrld => ofLanes 32 fun i => (shiftLane 32 0 c (lane 32 i d)).toNat
  | .psrad => ofLanes 32 fun i => (shiftLane 32 1 c (lane 32 i d)).toNat
  | .pslld => ofLanes 32 fun i => (shiftLane 32 2 c (lane 32 i d)).toNat
  | .psrlq => ofLanes 64 fun i => (shiftLane 64 0 c (lane 64 i d)).toNat
  | .psllq => ofLanes 64 fun i => (shiftLane 64 2 c (lane 64 i d)).toNat
  | .psrldq => if c > 15 then 0 else d >>> (8 * c)
  | .pslldq => if c > 15 then 0 else d <<< (8 * c)

/-- The two-bit field `k` of an immediate. -/
def sel2 (imm : Byte) (k : Nat) : Nat := (imm.toNat >>> (2 * k)) % 4

/-- PSHUFD/PSHUFHW/PSHUFLW of the source. -/
def ShufKind.eval (k : ShufKind) (imm : Byte) (s : BitVec 128) : BitVec 128 :=
  match k with
  | .d => ofLanes 32 fun i => (lane 32 (sel2 imm i) s).toNat
  | .hw => ofLanes 16 fun i => if i < 4 then (lane 16 i s).toNat else (lane 16 (4 + sel2 imm (i - 4)) s).toNat
  | .lw => ofLanes 16 fun i => if i < 4 then (lane 16 (sel2 imm i) s).toNat else (lane 16 i s).toNat

/-- SHUFPS/SHUFPD: the low half from the destination, the high half from the source. -/
def shufpEval (p : Precision) (imm : Byte) (d s : BitVec 128) : BitVec 128 :=
  match p with
  | .single => ofLanes 32 fun i => (lane 32 (sel2 imm i) (if i < 2 then d else s)).toNat
  | .double => ofLanes 64 fun i => (lane 64 ((imm.toNat >>> i) % 2) (if i = 0 then d else s)).toNat

/-- The sign bits of the lanes of width `w`, as a mask. -/
def signMask (w : Nat) (v : BitVec 128) : Nat :=
  (List.range (128 / w)).foldr (fun i acc => acc + (if v.getLsbD (i * w + w - 1) then 2 ^ i else 0)) 0

def MskKind.width : MskKind → Nat
  | .ps => 32 | .pd => 64 | .b => 8

/-! ## Operands -/

/-- The effective address. A RIP-relative address is relative to the next
instruction, at `rip + length`. -/
def Addr.ea (a : Addr) (length : Nat) (s : State) : Nat :=
  match a with
  | .mem m => (m.effectiveAddress s.core.read).toNat
  | .rip d => (s.rip + BitVec.ofNat 64 length + d.signExtend 64).toNat

/-- Read `w` bits at an address, with optional 16-byte alignment. -/
def readMem (w : Nat) (aligned : Bool) (memory : Memory) (address : Nat) : Except Fault (BitVec w) :=
  if aligned && address % 16 != 0 then .error .generalProtection
  else
    match loadW w memory address with
    | some v => .ok v
    | none => .error .dataFault

/-- An `xmm/m128` source (`aligned` for the forms that require it). -/
def readSrc (aligned : Bool) (length : Nat) (s : State) (memory : Memory) :
    Src → Except Fault (BitVec 128)
  | .reg r => .ok (s.xmm r.toV)
  | .mem a => readMem 128 aligned memory (a.ea length s)

/-- An `xmm/m64` source: the low 64 bits of a register, or eight bytes. -/
def readSrc64 (length : Nat) (s : State) (memory : Memory) : Src → Except Fault (BitVec 64)
  | .reg r => .ok ((s.xmm r.toV).extractLsb' 0 64)
  | .mem a => readMem 64 false memory (a.ea length s)

/-- An `xmm/m32` source. -/
def readSrc32 (length : Nat) (s : State) (memory : Memory) : Src → Except Fault (BitVec 32)
  | .reg r => .ok ((s.xmm r.toV).extractLsb' 0 32)
  | .mem a => readMem 32 false memory (a.ea length s)

/-- Write `w` bits, with optional alignment. -/
def writeMem (w : Nat) (aligned : Bool) (memory : Memory) (address : Nat) (v : BitVec w) :
    Except Fault Memory :=
  if aligned && address % 16 != 0 then .error .generalProtection
  else
    match storeW w memory address v with
    | some m => .ok m
    | none => .error .dataFault

/-- Continue with a read value or report its fault. -/
def andThen {α : Type} (e : Except Fault α) (k : α → Result) : Result :=
  match e with
  | .ok v => k v
  | .error f => .fault f

/-- Write XMM `dst` (legacy SSE) and advance. -/
def retireX (s : State) (length : Nat) (memory : Memory) (dst : XReg) (v : BitVec 128) : Result :=
  .retired ((s.writeXmmLegacy dst.toV v).advance length) memory

/-- Write a 32-bit result to a general-purpose register (zero-extended to 64). -/
def State.writeGpr32 (s : State) (r : Reg) (v : BitVec 32) : State :=
  s.setCore (s.core.write r (v.setWidth 64))

/-! ## Packed floating point -/

/-- The lane count of a precision. -/
def Precision.lanes : Precision → Nat
  | .single => 4 | .double => 2

/-- Lane `i` of a precision. -/
def flane (p : Precision) (i : Nat) (v : BitVec 128) : Numeric.Float.Bits p.fmt :=
  Float.lane p (v >>> (i * p.width))

/-- OR the conditions of several lanes. -/
def combine (ds : List Detected) : Detected :=
  ds.foldl (fun a d => { pre := a.pre.union d.pre, post := a.post.union d.post }) {}

/-- Commit `write` with the recorded MXCSR, or raise #XM (`Float.signal`). -/
def fpFinish (s : State) (length : Nat) (memory : Memory) (d : Detected) (write : State → State) :
    Result :=
  match Float.signal s.mxcsr d with
  | .error m => .fault (.simdException m)
  | .ok m => .retired (((write s).setMxcsr m).advance length) memory

/-- A lane-wise floating-point operation with lane outcomes `out` producing
`n` lanes of width `w`, the others zero: the value and the combined conditions. -/
def lanesOf {α : Type} (n w : Nat) (val : α → Nat) (out : Nat → α) : BitVec 128 :=
  ofLanes w fun i => if i < n then val (out i) else 0

/-- ADD/SUB/MUL/DIV/MIN/MAX PS/PD on lane values. -/
def arithLane (m : MXCSR) (p : Precision) (op : ArithOp) (x y : Numeric.Float.Bits p.fmt) :
    Numeric.Float.Bits p.fmt × Detected :=
  match op.kind with
  | .inl a => ((Float.Scalar.binary m p a x y).value, Float.Scalar.binaryDetected m p a x y)
  | .inr isMax => ((Float.Scalar.minMax m p isMax x y).value, Float.Scalar.minMaxDetected m p isMax x y)

/-- The result and conditions of a packed operation from lane results. -/
def packLanes (p : Precision) (f : Nat → Numeric.Float.Bits p.fmt × Detected) :
    BitVec 128 × Detected :=
  (ofLanes p.width fun i => (f i).1.toNat, combine ((List.range (Precision.lanes p)).map fun i => (f i).2))

/-- A conversion: lane outcomes `f i` for `i < n`, results of width `w`. -/
def cvtLanes (n w : Nat) (f : Nat → Nat × Detected) : BitVec 128 × Detected :=
  (ofLanes w fun i => if i < n then (f i).1 else 0, combine ((List.range n).map fun i => (f i).2))

/-- The packed conversions on a source (the low 64 bits for CVTPS2PD and
CVTDQ2PD). -/
def CvtKind.eval (k : CvtKind) (m : MXCSR) (b : BitVec 128) : BitVec 128 × Detected :=
  match k with
  | .dq2ps => cvtLanes 4 32 fun i =>
      ((Float.Scalar.ofInt m .single .w32 (lane 32 i b)).value.toNat,
        Float.Scalar.ofIntDetected m .single .w32 (lane 32 i b))
  | .ps2dq => cvtLanes 4 32 fun i =>
      ((Float.Scalar.toInt m .single .w32 m.rounding (flane .single i b)).value.toNat,
        Float.Scalar.toIntDetected m .single .w32 m.rounding (flane .single i b))
  | .tps2dq => cvtLanes 4 32 fun i =>
      ((Float.Scalar.toInt m .single .w32 .towardZero (flane .single i b)).value.toNat,
        Float.Scalar.toIntDetected m .single .w32 .towardZero (flane .single i b))
  | .ps2pd => cvtLanes 2 64 fun i =>
      ((Float.Scalar.convert m .single (flane .single i b)).value.toNat,
        Float.Scalar.convertDetected m .single (flane .single i b))
  | .pd2ps => cvtLanes 2 32 fun i =>
      ((Float.Scalar.convert m .double (flane .double i b)).value.toNat,
        Float.Scalar.convertDetected m .double (flane .double i b))
  | .dq2pd => cvtLanes 2 64 fun i =>
      ((Float.Scalar.ofInt m .double .w32 (lane 32 i b)).value.toNat,
        Float.Scalar.ofIntDetected m .double .w32 (lane 32 i b))
  | .pd2dq => cvtLanes 2 32 fun i =>
      ((Float.Scalar.toInt m .double .w32 m.rounding (flane .double i b)).value.toNat,
        Float.Scalar.toIntDetected m .double .w32 m.rounding (flane .double i b))
  | .tpd2dq => cvtLanes 2 32 fun i =>
      ((Float.Scalar.toInt m .double .w32 .towardZero (flane .double i b)).value.toNat,
        Float.Scalar.toIntDetected m .double .w32 .towardZero (flane .double i b))

/-- Whether a conversion reads only 64 bits (CVTPS2PD, CVTDQ2PD; no alignment). -/
def CvtKind.half : CvtKind → Bool
  | .ps2pd | .dq2pd => true
  | _ => false

/-! ## Moves -/

/-- The 16-byte-aligned moves. -/
def MovKind.aligned : MovKind → Bool
  | .aps | .apd | .dqa => true
  | _ => false

/-- MASKMOVDQU's byte stores, one at a time. -/
def maskStores (memory : Memory) (address : Nat) (src msk : BitVec 128) : Nat → Option Memory
  | 0 => some memory
  | j + 1 =>
    (maskStores memory address src msk j).bind fun m =>
      if msk.getLsbD (8 * j + 7) then m.writeBytes (address + j) [src.extractLsb' (8 * j) 8]
      else some m

/-! ## Execution -/

/-- Execute one instruction of length `length`. -/
def Instr.exec (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  match i with
  | .load k dst a =>
    andThen (readMem 128 k.aligned memory (a.ea length s)) (retireX s length memory dst)
  | .store k a src =>
    andThen (writeMem 128 k.aligned memory (a.ea length s) (s.xmm src.toV))
      (.retired (s.advance length))
  | .movReg _ dst src => retireX s length memory dst (s.xmm src.toV)
  | .storeNT _ a src =>
    andThen (writeMem 128 true memory (a.ea length s) (s.xmm src.toV)) (.retired (s.advance length))
  | .maskmovdqu src msk =>
    let address := (s.core.read .rdi).toNat
    if memory.checkSpan .write address 16 then
      match maskStores memory address (s.xmm src.toV) (s.xmm msk.toV) 16 with
      | some m => .retired (s.advance length) m
      | none => .unmodeled
    else if (List.range 16).all fun j =>
        !(s.xmm msk.toV).getLsbD (8 * j + 7) || memory.checkSpan .write (address + j) 1 then
      .unmodeled
    else .fault .dataFault
  | .movqLoad dst src =>
    andThen (readSrc64 length s memory src) fun v => retireX s length memory dst (v.setWidth 128)
  | .movqStore a src =>
    andThen (writeMem 64 false memory (a.ea length s) ((s.xmm src.toV).extractLsb' 0 64))
      (.retired (s.advance length))
  | .movdLoad .w32 dst a =>
    andThen (readMem 32 false memory (a.ea length s)) fun v =>
      retireX s length memory dst (v.setWidth 128)
  | .movdLoad .w64 dst a =>
    andThen (readMem 64 false memory (a.ea length s)) fun v =>
      retireX s length memory dst (v.setWidth 128)
  | .movdStore .w32 a src =>
    andThen (writeMem 32 false memory (a.ea length s) ((s.xmm src.toV).extractLsb' 0 32))
      (.retired (s.advance length))
  | .movdStore .w64 a src =>
    andThen (writeMem 64 false memory (a.ea length s) ((s.xmm src.toV).extractLsb' 0 64))
      (.retired (s.advance length))
  | .movHalfLoad high _ dst a =>
    andThen (readMem 64 false memory (a.ea length s)) fun v =>
      let d := s.xmm dst.toV
      retireX s length memory dst
        (if high then v ++ d.extractLsb' 0 64 else d.extractLsb' 64 64 ++ v)
  | .movHalfStore high _ a src =>
    andThen (writeMem 64 false memory (a.ea length s)
        ((s.xmm src.toV).extractLsb' (if high then 64 else 0) 64))
      (.retired (s.advance length))
  | .movhlps dst src =>
    retireX s length memory dst
      ((s.xmm dst.toV).extractLsb' 64 64 ++ (s.xmm src.toV).extractLsb' 64 64)
  | .movlhps dst src =>
    retireX s length memory dst
      ((s.xmm src.toV).extractLsb' 0 64 ++ (s.xmm dst.toV).extractLsb' 0 64)
  | .movmsk k dst src =>
    .retired ((State.writeGpr32 s dst (BitVec.ofNat 32 (signMask k.width (s.xmm src.toV)))).advance length)
      memory
  | .pinsrw dst src imm =>
    let word : Except Fault (BitVec 16) :=
      match src with
      | .reg r => .ok ((s.core.read r).extractLsb' 0 16)
      | .mem a => readMem 16 false memory (a.ea length s)
    andThen word fun v =>
      let sel := imm.toNat % 8
      retireX s length memory dst
        (ofLanes 16 fun j => if j = sel then v.toNat else (lane 16 j (s.xmm dst.toV)).toNat)
  | .pextrw dst src imm =>
    .retired ((State.writeGpr32 s dst ((lane 16 (imm.toNat % 8) (s.xmm src.toV)).setWidth 32)).advance
      length) memory
  | .pint op dst src =>
    andThen (readSrc true length s memory src) fun v =>
      retireX s length memory dst (op.eval (s.xmm dst.toV) v)
  | .pshiftImm op dst imm => retireX s length memory dst (op.eval imm (s.xmm dst.toV))
  | .pshuf k dst src imm =>
    andThen (readSrc true length s memory src) fun v => retireX s length memory dst (k.eval imm v)
  | .arithp op p dst src =>
    andThen (readSrc true length s memory src) fun v =>
      let r := packLanes p fun i => arithLane s.mxcsr p op (flane p i (s.xmm dst.toV)) (flane p i v)
      fpFinish s length memory r.2 fun t => t.writeXmmLegacy dst.toV r.1
  | .sqrtp p dst src =>
    andThen (readSrc true length s memory src) fun v =>
      let r := packLanes p fun i =>
        ((Float.Scalar.sqrt s.mxcsr p (flane p i v)).value,
          Float.Scalar.sqrtDetected s.mxcsr p (flane p i v))
      fpFinish s length memory r.2 fun t => t.writeXmmLegacy dst.toV r.1
  | .cmpp p pred dst src =>
    andThen (readSrc true length s memory src) fun v =>
      let r := packLanes p fun i =>
        (Float.cmpMask p (Float.Scalar.cmp s.mxcsr p pred (flane p i (s.xmm dst.toV)) (flane p i v)).value,
          Float.Scalar.cmpDetected s.mxcsr p pred (flane p i (s.xmm dst.toV)) (flane p i v))
      fpFinish s length memory r.2 fun t => t.writeXmmLegacy dst.toV r.1
  | .logicRip op _ dst d =>
    andThen (readMem 128 true memory ((Addr.rip d).ea length s)) fun v =>
      retireX s length memory dst (op.eval (s.xmm dst.toV) v)
  | .unpckp high p dst src =>
    andThen (readSrc true length s memory src) fun v =>
      retireX s length memory dst (unpack p.width high (s.xmm dst.toV) v)
  | .shufp p dst src imm =>
    andThen (readSrc true length s memory src) fun v =>
      retireX s length memory dst (shufpEval p imm (s.xmm dst.toV) v)
  | .cvtp k dst src =>
    let source : Except Fault (BitVec 128) :=
      if k.half then (readSrc64 length s memory src).map (·.setWidth 128)
      else readSrc true length s memory src
    andThen source fun v =>
      let r := k.eval s.mxcsr v
      fpFinish s length memory r.2 fun t => t.writeXmmLegacy dst.toV r.1
  | .approx .. => .unmodeled
  | .fence _ => .retired (s.advance length) memory
  | .prefetch .. => .retired (s.advance length) memory

end Silmaril.X86.Features.SsePacked
