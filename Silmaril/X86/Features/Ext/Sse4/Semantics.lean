module

public import Silmaril.X86.Features.Ext.Sse4.Encoding
public import Silmaril.X86.Features.Ext.SsePacked.Semantics
public import Silmaril.X86.Ext.Semantics
public import Silmaril.Crypto.CRC32C

/-!
# Semantics of the SSE3/SSSE3/SSE4.1/SSE4.2 lane

`exec` on the extended state `Features.State`, written from the Operation
sections of the Intel SDM Vol. 2 instruction pages. Every XMM destination is a
legacy-SSE write (`State.writeXmmLegacy`: bits 511:128 are kept). RIP advances
by the instruction length. The lane helpers (`lane`, `ofLanes`, `ssat`, `usat`,
`readMem`, `writeMem`) are `SsePacked`'s.

## Fidelity

These forms are exact:

* the SSE3 moves MOVDDUP, MOVSLDUP, MOVSHDUP and LDDQU;
* every SSSE3 form (PSHUFB, PHADD/PHSUB and their saturating variants,
  PMADDUBSW, PMULHRSW, PSIGN, PABS, PALIGNR);
* the SSE4.1 integer, blend and move forms: PBLENDVB, BLENDVPS/PD (mask in
  XMM0), BLENDPS/PD, PBLENDW, PTEST (ZF and CF, with AF, OF, PF and SF
  cleared), PMOVSX/PMOVZX, PMULDQ, PMULLD, PCMPEQQ, PACKUSDW, PMIN/PMAX,
  PHMINPOSUW, MPSADBW, INSERTPS, MOVNTDQA, PEXTR*/EXTRACTPS and PINSR*;
* SSE4.2 PCMPGTQ and CRC32, which is `Crypto.crc32cUpdateByte` over the
  source bytes in memory order.

The floating-point forms (ADDSUBPS/PD, HADDPS/PD, HSUBPS/PD, ROUNDPS/PD,
DPPS/DPPD) and the string compares (PCMPESTRI/M, PCMPISTRI/M) are
`unmodeled`. So are the register forms of LDDQU and MOVNTDQA, whose operand
must be memory.

Memory operands follow the legacy-SSE rule that a 16-byte operand is 16-byte
aligned (a misaligned one is #GP(0)), with LDDQU as the exception. The narrower
operands (the `m64`/`m32`/`m16` sources of PMOVSX/PMOVZX, MOVDDUP and INSERTPS,
the scalar sources and destinations of PINSR/PEXTR, and CRC32) have no
alignment requirement. A RIP-relative operand is relative to the next
instruction.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse4

open Silmaril.X86 (XReg Reg Byte Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Features.SsePacked (lane ofLanes ssat usat mask readMem writeMem andThen)

/-! ## Operands -/

/-- The address of the next instruction. -/
def nextRip (s : State) (length : Nat) : Word := s.rip + BitVec.ofNat 64 length

/-- The effective address of a memory operand. -/
def ea (m : Ext.Mem) (s : State) (length : Nat) : Nat := (m.addr s.core (nextRip s length)).toNat

/-- The low `w` bits of an `xmm/m` source (`w` ≤ 128), aligned when asked. -/
def readSrc (w : Nat) (aligned : Bool) (length : Nat) (s : State) (memory : Memory) :
    Src → Except Fault (BitVec w)
  | .reg r => .ok ((s.xmm r.toV).setWidth w)
  | .mem m => readMem w aligned memory (ea m s length)

/-- The low `w` bits of an `r/m` source. -/
def readRM (w : Nat) (length : Nat) (s : State) (memory : Memory) :
    Ext.RM → Except Fault (BitVec w)
  | .reg r => .ok ((s.core.read r).setWidth w)
  | .mem m => readMem w false memory (ea m s length)

/-- Write `v` (`w` ≤ 64 bits) to an `r/m` destination: a register is written
whole, zero-extended. -/
def writeRM (w : Nat) (length : Nat) (s : State) (memory : Memory) (dst : Ext.RM)
    (v : BitVec w) : Result :=
  match dst with
  | .reg r => .retired ((s.setCore (s.core.write r (v.setWidth 64))).advance length) memory
  | .mem m => andThen (writeMem w false memory (ea m s length) v) (.retired (s.advance length))

def retire (s : State) (length : Nat) (memory : Memory) (dst : XReg) (v : BitVec 128) : Result :=
  .retired ((s.writeXmmLegacy dst.toV v).advance length) memory

/-! ## Lane operations -/

/-- `ofLanes` with `BitVec` lanes. -/
def build (w : Nat) (f : Nat → BitVec w) : BitVec 128 := ofLanes w fun i => (f i).toNat

/-- Horizontal pairs: lanes of the low half from `d`, of the high half from `s`. -/
def horiz (w : Nat) (f : BitVec w → BitVec w → BitVec w) (d s : BitVec 128) : BitVec 128 :=
  let half := 64 / w
  build w fun i =>
    let v := if i < half then d else s
    let j := i % half
    f (lane w (2 * j) v) (lane w (2 * j + 1) v)

def lanes2 (w : Nat) (f : BitVec w → BitVec w → BitVec w) (d s : BitVec 128) : BitVec 128 :=
  build w fun i => f (lane w i d) (lane w i s)

def psign (w : Nat) (d s : BitVec 128) : BitVec 128 :=
  lanes2 w (fun a b => if b.slt 0 then -a else if b = 0 then 0 else a) d s

def pabs (w : Nat) (s : BitVec 128) : BitVec 128 :=
  build w fun i => let b := lane w i s; if b.slt 0 then -b else b

def pshufb (d s : BitVec 128) : BitVec 128 :=
  build 8 fun i =>
    let c := lane 8 i s
    if c.getLsbD 7 then 0 else lane 8 (c.toNat % 16) d

/-- Select lanes of `s` where the sign bit of the `mask` lane is set. -/
def blendv (w : Nat) (msk d s : BitVec 128) : BitVec 128 :=
  build w fun i => if (lane w i msk).getLsbD (w - 1) then lane w i s else lane w i d

/-- Select lanes of `s` where bit `i` of `imm` is set. -/
def blendImm (w : Nat) (imm : Byte) (d s : BitVec 128) : BitVec 128 :=
  build w fun i => if imm.getLsbD i then lane w i s else lane w i d

/-- PMOVSX (`signed`) or PMOVZX from lanes of `from` bits to lanes of `to` bits. -/
def pmovx (signed : Bool) (fromW toW : Nat) (s : BitVec 128) : BitVec 128 :=
  build toW fun i =>
    let x := lane fromW i s
    if signed then x.signExtend toW else x.setWidth toW

def pmaddubsw (d s : BitVec 128) : BitVec 128 :=
  build 16 fun i =>
    ssat 16 ((lane 8 (2 * i) d).toNat * (lane 8 (2 * i) s).toInt +
      (lane 8 (2 * i + 1) d).toNat * (lane 8 (2 * i + 1) s).toInt)

def pmulhrsw (d s : BitVec 128) : BitVec 128 :=
  lanes2 16 (fun a b => BitVec.ofInt 16 (((a.toInt * b.toInt) / 2 ^ 14 + 1) / 2)) d s

def phminposuw (s : BitVec 128) : BitVec 128 :=
  let ws := (List.range 8).map fun i => (lane 16 i s).toNat
  let m := ws.foldl min (2 ^ 16)
  let idx := (ws.findIdx? (· = m)).getD 0
  BitVec.ofNat 128 (m + idx * 2 ^ 16)

/-- MPSADBW: eight sums of absolute differences of four unsigned bytes. -/
def mpsadbw (imm : Byte) (d s : BitVec 128) : BitVec 128 :=
  let o1 := if imm.getLsbD 2 then 4 else 0
  let o2 := 4 * (imm.toNat % 4)
  build 16 fun i => BitVec.ofNat 16 ((List.range 4).foldl (fun acc k =>
    acc + (((lane 8 (o1 + i + k) d).toNat : Int) - (lane 8 (o2 + k) s).toNat).natAbs) 0)

/-- INSERTPS with the selected source element `e`. -/
def insertps (imm : Byte) (e : BitVec 32) (d : BitVec 128) : BitVec 128 :=
  let cd := (imm.toNat >>> 4) % 4
  build 32 fun i =>
    if imm.getLsbD i then 0 else if i = cd then e else lane 32 i d

/-! ## Two-operand forms -/

/-- The source width of a two-operand form (bits read from memory or from the
low end of the source register) and whether a memory source must be aligned. -/
def Op2.srcWidth : Op2 → Nat
  | .pmovsxbw | .pmovzxbw | .pmovsxwd | .pmovzxwd | .pmovsxdq | .pmovzxdq | .movddup => 64
  | .pmovsxbd | .pmovzxbd | .pmovsxwq | .pmovzxwq => 32
  | .pmovsxbq | .pmovzxbq => 16
  | _ => 128

def Op2.aligned : Op2 → Bool
  | .lddqu => false
  | op => op.srcWidth == 128

/-- The value of a two-operand form on XMM0 (the implicit mask), the destination
and the source (zero-extended to 128 bits), or `none` outside the model. -/
def Op2.eval (op : Op2) (x0 d s : BitVec 128) : Option (BitVec 128) :=
  match op with
  | .movddup => some (build 64 fun _ => lane 64 0 s)
  | .movsldup => some (build 32 fun i => lane 32 (i - i % 2) s)
  | .movshdup => some (build 32 fun i => lane 32 (i - i % 2 + 1) s)
  | .lddqu | .movntdqa => some s
  | .pshufb => some (Sse4.pshufb d s)
  | .phaddw => some (horiz 16 (· + ·) d s)
  | .phaddd => some (horiz 32 (· + ·) d s)
  | .phaddsw => some (horiz 16 (fun a b => ssat 16 (a.toInt + b.toInt)) d s)
  | .phsubw => some (horiz 16 (· - ·) d s)
  | .phsubd => some (horiz 32 (· - ·) d s)
  | .phsubsw => some (horiz 16 (fun a b => ssat 16 (a.toInt - b.toInt)) d s)
  | .pmaddubsw => some (Sse4.pmaddubsw d s)
  | .pmulhrsw => some (Sse4.pmulhrsw d s)
  | .psignb => some (psign 8 d s)
  | .psignw => some (psign 16 d s)
  | .psignd => some (psign 32 d s)
  | .pabsb => some (pabs 8 s)
  | .pabsw => some (pabs 16 s)
  | .pabsd => some (pabs 32 s)
  | .pblendvb => some (blendv 8 x0 d s)
  | .blendvps => some (blendv 32 x0 d s)
  | .blendvpd => some (blendv 64 x0 d s)
  | .pmovsxbw => some (pmovx true 8 16 s)
  | .pmovsxbd => some (pmovx true 8 32 s)
  | .pmovsxbq => some (pmovx true 8 64 s)
  | .pmovsxwd => some (pmovx true 16 32 s)
  | .pmovsxwq => some (pmovx true 16 64 s)
  | .pmovsxdq => some (pmovx true 32 64 s)
  | .pmovzxbw => some (pmovx false 8 16 s)
  | .pmovzxbd => some (pmovx false 8 32 s)
  | .pmovzxbq => some (pmovx false 8 64 s)
  | .pmovzxwd => some (pmovx false 16 32 s)
  | .pmovzxwq => some (pmovx false 16 64 s)
  | .pmovzxdq => some (pmovx false 32 64 s)
  | .pmuldq => some (build 64 fun i =>
      BitVec.ofInt 64 ((lane 32 (2 * i) d).toInt * (lane 32 (2 * i) s).toInt))
  | .pcmpeqq => some (lanes2 64 (fun a b => mask 64 (a == b)) d s)
  | .packusdw => some (build 16 fun i =>
      usat 16 (lane 32 (i % 4) (if i < 4 then d else s)).toInt)
  | .pminsb => some (lanes2 8 (fun a b => if a.slt b then a else b) d s)
  | .pminsd => some (lanes2 32 (fun a b => if a.slt b then a else b) d s)
  | .pminuw => some (lanes2 16 (fun a b => if a.ult b then a else b) d s)
  | .pminud => some (lanes2 32 (fun a b => if a.ult b then a else b) d s)
  | .pmaxsb => some (lanes2 8 (fun a b => if b.slt a then a else b) d s)
  | .pmaxsd => some (lanes2 32 (fun a b => if b.slt a then a else b) d s)
  | .pmaxuw => some (lanes2 16 (fun a b => if b.ult a then a else b) d s)
  | .pmaxud => some (lanes2 32 (fun a b => if b.ult a then a else b) d s)
  | .pmulld => some (lanes2 32 (· * ·) d s)
  | .phminposuw => some (Sse4.phminposuw s)
  | .pcmpgtq => some (lanes2 64 (fun a b => mask 64 (b.slt a)) d s)
  | .addsubpd | .addsubps | .haddpd | .haddps | .hsubpd | .hsubps | .ptest => none

/-- The forms whose operand must be memory. -/
def Op2.memOnly : Op2 → Bool
  | .lddqu | .movntdqa => true
  | _ => false

/-- PTEST: ZF from `d AND s`, CF from `(NOT d) AND s`; AF, OF, PF, SF cleared. -/
def ptestFlags (d s : BitVec 128) : X86.Flags :=
  { carry := some ((~~~d &&& s) == 0), parity := some false, adjust := some false,
    zero := some ((d &&& s) == 0), sign := some false, overflow := some false }

/-! ## Immediate forms -/

def OpI.eval (op : OpI) (imm : Byte) (d s : BitVec 128) : Option (BitVec 128) :=
  match op with
  | .palignr =>
    some (if imm.toNat ≥ 32 then 0 else ((d ++ s) >>> (8 * imm.toNat)).setWidth 128)
  | .blendps => some (blendImm 32 imm d s)
  | .blendpd => some (blendImm 64 imm d s)
  | .pblendw => some (blendImm 16 imm d s)
  | .mpsadbw => some (Sse4.mpsadbw imm d s)
  | .insertps => some (Sse4.insertps imm (lane 32 ((imm.toNat >>> 6) % 4) s) d)
  | .roundps | .roundpd | .dpps | .dppd
  | .pcmpestrm | .pcmpestri | .pcmpistrm | .pcmpistri | .pcmpestrm64 | .pcmpestri64 => none

/-! ## Extraction, insertion and CRC32 -/

def ExtrOp.width : ExtrOp → Nat
  | .pextrb => 8 | .pextrw => 16 | .pextrd | .extractps => 32 | .pextrq => 64

def InsOp.width : InsOp → Nat
  | .pinsrb => 8 | .pinsrd => 32 | .pinsrq => 64

/-- The CRC32C update of `crc` by the `k` low bytes of `v`, least significant first. -/
def crcBytes (crc : BitVec 32) (v : BitVec 64) (k : Nat) : BitVec 32 :=
  let r := ((List.range k).map fun j => (v.extractLsb' (8 * j) 8).toNat.toUInt8).foldl
    Crypto.crc32cUpdateByte (crc.toNat.toUInt32)
  BitVec.ofNat 32 r.toNat

def CrcSz.bytes : CrcSz → Nat
  | .b | .bq => 1 | .d => 4 | .q => 8

/-! ## Execution -/

def exec (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  match i with
  | .rr .ptest dst src =>
    andThen (readSrc 128 true length s memory src) fun v =>
      .retired ((s.setCore { s.core with flags := ptestFlags (s.xmm dst.toV) v }).advance length)
        memory
  | .rr op dst src =>
    match op.memOnly, src with
    | true, .reg _ => .unmodeled
    | _, _ =>
      andThen (readSrc op.srcWidth op.aligned length s memory src) fun v =>
        match op.eval (s.xmm XReg.xmm0.toV) (s.xmm dst.toV) (v.setWidth 128) with
        | some r => retire s length memory dst r
        | none => .unmodeled
  | .ri .insertps dst (.mem m) imm =>
    andThen (readMem 32 false memory (ea m s length)) fun e =>
      retire s length memory dst (insertps imm e (s.xmm dst.toV))
  | .ri op dst src imm =>
    andThen (readSrc 128 true length s memory src) fun v =>
      match op.eval imm (s.xmm dst.toV) v with
      | some r => retire s length memory dst r
      | none => .unmodeled
  | .extr op dst src imm =>
    let w := op.width
    writeRM w length s memory dst (lane w (imm.toNat % (128 / w)) (s.xmm src.toV))
  | .ins op dst src imm =>
    let w := op.width
    andThen (readRM w length s memory src) fun v =>
      let sel := imm.toNat % (128 / w)
      retire s length memory dst (build w fun j => if j = sel then v else lane w j (s.xmm dst.toV))
  | .crc32 sz dst src =>
    andThen (readRM (8 * sz.bytes) length s memory src) fun v =>
      let r := crcBytes ((s.core.read dst).setWidth 32) (v.setWidth 64) sz.bytes
      .retired ((s.setCore (s.core.write dst (r.setWidth 64))).advance length) memory

end Silmaril.X86.Features.Sse4
