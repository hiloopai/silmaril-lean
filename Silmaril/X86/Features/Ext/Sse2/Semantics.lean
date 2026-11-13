module

public import Silmaril.X86.Features.Ext.Sse2.Syntax
public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Float.Semantics

/-!
# Semantics of the SSE/SSE2 integer and move lane

`exec` on the extended state `Features.State`, written from the Operation
sections of the SDM Vol. 2 instruction pages. Every XMM write is a legacy-SSE
write (`State.writeXmmLegacy`): bits 511:128 of the register are kept.

* No instruction of the lane reads or writes RFLAGS, MXCSR or the x87 state,
  and none raises a SIMD floating-point exception; there are no undefined
  flags, so the flag-oracle convention is not needed.
* Memory operands: a 128-bit operand of MOVDQA/MOVAPS/MOVAPD and of every
  `xmm/m128` source of a packed integer operation or PSHUFD must be 16-byte
  aligned, else #GP(0) (`Fault.generalProtection`), checked before the access
  as in `X86.Float.readPacked`; MOVDQU/MOVUPS/MOVUPD and the 16/32/64-bit
  accesses have no alignment requirement. An access that is not permitted or
  not backed is `Fault.dataFault`. Canonical-address and segment checks and
  alignment checking with CR0.AM/EFLAGS.AC are not modelled.
* Shift counts: PSRL/PSLL by a count above the lane width minus one give zero,
  PSRA gives the sign fill (count clamped to the width); the count operand is
  all 64 bits of the source (PSxx by XMM) or the imm8. PSRLDQ/PSLLDQ by more
  than 15 bytes give zero.
* PINSRW/PEXTRW use imm8[2:0]; PSHUFD uses all of imm8.
* PMOVMSKB and PEXTRW write a 32-bit register: bits 63:32 are zeroed.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse2

open Silmaril.X86
open Silmaril.X86.Float (XRM GRM IntWidth le32 le64 ofLe32? ofLe64? ofLe128?)
open Silmaril.Process (Memory)

/-! ## Lanes -/

/-- Lane `i` of width `w` of a 128-bit value. -/
def lane (w i : Nat) (v : BitVec 128) : BitVec w := v.extractLsb' (w * i) w

/-- The 128-bit value whose lane `i` of width `w` is `g i`, for `i < n`. -/
def ofLanes (w n : Nat) (g : Nat → BitVec w) : BitVec 128 :=
  (List.range n).foldr (fun i acc => acc ||| ((g i).setWidth 128 <<< (w * i))) 0

/-- Apply `f` lane by lane. -/
def lanewise (w : Nat) (f : BitVec w → BitVec w → BitVec w) (a b : BitVec 128) : BitVec 128 :=
  ofLanes w (128 / w) fun i => f (lane w i a) (lane w i b)

def Lane.width : Lane → Nat
  | .b => 8 | .w => 16 | .d => 32 | .q => 64

def CmpLane.width : CmpLane → Nat
  | .b => 8 | .w => 16 | .d => 32

def Logic.eval : Logic → BitVec 128 → BitVec 128 → BitVec 128
  | .and, a, b => a &&& b
  | .andn, a, b => ~~~a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- PUNPCKL (`hi = false`) or PUNPCKH: interleave the low (high) halves of the
destination and the source, the destination's lanes first. -/
def unpack (w : Nat) (hi : Bool) (a b : BitVec 128) : BitVec 128 :=
  let half := 64 / w
  let base := if hi then half else 0
  ofLanes w (2 * half) fun j => if j % 2 = 0 then lane w (base + j / 2) a else lane w (base + j / 2) b

/-- The shift operation of a shift kind, by a count already read. -/
inductive ShiftDir where
  | srl | sra | sll

def ShiftKind.dir : ShiftKind → ShiftDir
  | .srlw | .srld | .srlq => .srl
  | .sraw | .srad => .sra
  | .sllw | .slld | .sllq => .sll

def ShiftKind.width : ShiftKind → Nat
  | .srlw | .sraw | .sllw => 16
  | .srld | .srad | .slld => 32
  | .srlq | .sllq => 64

/-- Shift each lane of `v` by `count` (SDM PSRLW/PSRAW/PSLLW Operation): the
count is clamped to the lane width, which gives zero for the logical shifts
and the sign fill for the arithmetic one. -/
def shiftLanes (k : ShiftKind) (count : Nat) (v : BitVec 128) : BitVec 128 :=
  let w := k.width
  let c := min count w
  ofLanes w (128 / w) fun i =>
    match k.dir with
    | .srl => lane w i v >>> c
    | .sra => (lane w i v).sshiftRight c
    | .sll => lane w i v <<< c

/-- PSRLDQ/PSLLDQ: shift the whole register by `imm` bytes (zero above 15). -/
def shiftBytes (left : Bool) (imm : Byte) (v : BitVec 128) : BitVec 128 :=
  let c := 8 * min imm.toNat 16
  if left then v <<< c else v >>> c

/-- PSHUFD: doubleword `i` of the result is doubleword `imm[2i+1:2i]` of the source. -/
def pshufd (imm : Byte) (v : BitVec 128) : BitVec 128 :=
  ofLanes 32 4 fun i => lane 32 (imm.extractLsb' (2 * i) 2).toNat v

/-- PMOVMSKB: bit `i` is the most significant bit of byte `i`. -/
def movmsk (v : BitVec 128) : BitVec 16 :=
  BitVec.ofNat 16 ((List.range 16).foldr
    (fun i acc => acc + if v.getLsbD (8 * i + 7) then 2 ^ i else 0) 0)

/-- PINSRW: replace word `imm[2:0]`. -/
def insertWord (imm : Byte) (x : BitVec 16) (v : BitVec 128) : BitVec 128 :=
  let sel := (imm.extractLsb' 0 3).toNat
  ofLanes 16 8 fun j => if j = sel then x else lane 16 j v

/-- PEXTRW: word `imm[2:0]`. -/
def extractWord (imm : Byte) (v : BitVec 128) : BitVec 16 :=
  lane 16 (imm.extractLsb' 0 3).toNat v

/-- The `xmm, xmm/m128` operations on the destination and source values. -/
def BinOp.eval : BinOp → BitVec 128 → BitVec 128 → BitVec 128
  | .logic op, a, b => op.eval a b
  | .add l, a, b => lanewise l.width (· + ·) a b
  | .sub l, a, b => lanewise l.width (· - ·) a b
  | .cmpeq l, a, b => lanewise l.width (fun x y => if x = y then -1 else 0) a b
  | .unpackLo l, a, b => unpack l.width false a b
  | .unpackHi l, a, b => unpack l.width true a b
  | .shift k, a, b => shiftLanes k (b.extractLsb' 0 64).toNat a

/-! ## Memory -/

/-- The little-endian bytes of a 128-bit value. -/
def le128 (v : BitVec 128) : List Byte := le64 (v.extractLsb' 0 64) ++ le64 (v.extractLsb' 64 64)

/-- The value of exactly two little-endian bytes. -/
def ofLe16? : List Byte → Option (BitVec 16)
  | [b0, b1] => some (b1 ++ b0)
  | _ => none

/-- The effective address of a memory operand. -/
def addr (m : Mem) (s : State) : Nat := (m.effectiveAddress s.core.read).toNat

/-- A 128-bit load; `aligned` requires a 16-byte aligned address (#GP(0)). -/
def load128 (aligned : Bool) (s : State) (memory : Memory) (m : Mem) : Except Fault (BitVec 128) :=
  if aligned && addr m s % 16 != 0 then .error .generalProtection
  else
    match (memory.readBytes (addr m s) 16).bind ofLe128? with
    | some v => .ok v
    | none => .error .dataFault

/-- An `xmm/m128` source of a packed operation (aligned). -/
def readSrc (s : State) (memory : Memory) : XRM → Except Fault (BitVec 128)
  | .reg r => .ok (s.xmm r.toV)
  | .mem m => load128 true s memory m

/-- Write `bytes` at a memory operand. -/
def store (s : State) (memory : Memory) (m : Mem) (bytes : List Byte) (length : Nat) : Result :=
  match memory.writeBytes (addr m s) bytes with
  | some after => .retired (s.advance length) after
  | none => .fault .dataFault

/-- A 128-bit store; `aligned` requires a 16-byte aligned address (#GP(0)). -/
def store128 (aligned : Bool) (s : State) (memory : Memory) (m : Mem) (v : BitVec 128)
    (length : Nat) : Result :=
  if aligned && addr m s % 16 != 0 then .fault .generalProtection
  else store s memory m (le128 v) length

/-- Retire after writing XMM `dst` (legacy SSE: bits 511:128 kept). -/
def retireXmm (s : State) (memory : Memory) (dst : XReg) (v : BitVec 128) (length : Nat) :
    Result :=
  .retired ((s.writeXmmLegacy dst.toV v).advance length) memory

/-- Retire with a computed source value, or fault. -/
def withSrc (r : Except Fault (BitVec 128)) (k : BitVec 128 → Result) : Result :=
  match r with
  | .ok v => k v
  | .error f => .fault f

/-- A 32-bit general-purpose register write: bits 63:32 are zeroed. -/
def writeGpr32 (s : State) (r : Reg) (v : BitVec 32) : State :=
  s.setCore (s.core.write r (v.setWidth 64))

/-! ## Execution -/

/-- Execute one instruction of the lane on the extended state. -/
def exec (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  match i with
  | .movLoad k dst m => withSrc (load128 k.aligned s memory m) fun v => retireXmm s memory dst v length
  | .movStore k m src => store128 k.aligned s memory m (s.xmm src.toV) length
  | .movRR _ dst src => Result.pure (fun s => s.writeXmmLegacy dst.toV (s.xmm src.toV)) length s memory
  | .movRRStore _ dst src =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV (s.xmm src.toV)) length s memory
  | .movdLoad .w32 dst m =>
    match (memory.readBytes (addr m s) 4).bind ofLe32? with
    | some v => retireXmm s memory dst (v.setWidth 128) length
    | none => .fault .dataFault
  | .movdLoad .w64 dst m =>
    match (memory.readBytes (addr m s) 8).bind ofLe64? with
    | some v => retireXmm s memory dst (v.setWidth 128) length
    | none => .fault .dataFault
  | .movdStore .w32 m src => store s memory m (le32 ((s.xmm src.toV).extractLsb' 0 32)) length
  | .movdStore .w64 m src => store s memory m (le64 ((s.xmm src.toV).extractLsb' 0 64)) length
  | .movqLoad dst (.reg src) =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV (((s.xmm src.toV).extractLsb' 0 64).setWidth 128))
      length s memory
  | .movqLoad dst (.mem m) =>
    match (memory.readBytes (addr m s) 8).bind ofLe64? with
    | some v => retireXmm s memory dst (v.setWidth 128) length
    | none => .fault .dataFault
  | .movqStore (.reg dst) src =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV (((s.xmm src.toV).extractLsb' 0 64).setWidth 128))
      length s memory
  | .movqStore (.mem m) src => store s memory m (le64 ((s.xmm src.toV).extractLsb' 0 64)) length
  | .binop op dst src =>
    withSrc (readSrc s memory src) fun v => retireXmm s memory dst (op.eval (s.xmm dst.toV) v) length
  | .shiftImm k dst imm =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV (shiftLanes k imm.toNat (s.xmm dst.toV)))
      length s memory
  | .shiftBytes left dst imm =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV (Sse2.shiftBytes left imm (s.xmm dst.toV)))
      length s memory
  | .pshufd dst src imm =>
    withSrc (readSrc s memory src) fun v => retireXmm s memory dst (Sse2.pshufd imm v) length
  | .pmovmskb dst src =>
    Result.pure (fun s => writeGpr32 s dst ((movmsk (s.xmm src.toV)).setWidth 32)) length s memory
  | .pinsrw dst (.reg r) imm =>
    Result.pure (fun s => s.writeXmmLegacy dst.toV
      (insertWord imm ((s.core.read r).setWidth 16) (s.xmm dst.toV))) length s memory
  | .pinsrw dst (.mem m) imm =>
    match (memory.readBytes (addr m s) 2).bind ofLe16? with
    | some x => retireXmm s memory dst (insertWord imm x (s.xmm dst.toV)) length
    | none => .fault .dataFault
  | .pextrw dst src imm =>
    Result.pure (fun s => writeGpr32 s dst ((extractWord imm (s.xmm src.toV)).setWidth 32))
      length s memory

end Silmaril.X86.Features.Sse2
