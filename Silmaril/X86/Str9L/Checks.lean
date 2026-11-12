module

public import Silmaril.X86.Str9L.Defs
public import Silmaril.X86.Features.Ext.Avx.Check
public import Silmaril.X86.Features.Checks

/-!
# Checkers for the lane vectors on the tower

Both run one **`Str9L.step host lanes`** on a tower state built from a lane vector, with the
code at `0x1000` (executable): the decoder chain of `Str9X` must claim or reject the bytes,
and the step (a lower layer's, or a lane's through `view`/`back`) must give the processor's
result.

* `checkAvxLine`: a vector of the `avx` lane (`scripts/x86-features/gen_avx_vectors.py`, the
  format of `Features.Avx.checkLine`): YMM `j` holds the vector's input or `Avx.pattern j`,
  RSI addresses the 64-byte buffer at `Avx.bufBase`, MXCSR is the vector's. The step must
  retire with every YMM register, the buffer and MXCSR as on the processor, RIP past the
  instruction. Forms `Str9V` decodes (`vpxor`, `vpcmpeqb`, `vpminub`, `vmovdqu`, …) are run
  by `Str9V`, so these vectors are also its difftest.
* `checkRoundLine`: a `roundss`/`roundsd xmm0, xmm1, imm8` vector
  (`scripts/x86-features/gen_vectors.py`): XMM0 and MXCSR as on the processor, the upper
  half of YMM0 kept.

`host` is `v3` with AES and PCLMULQDQ, the features of the processor that produced the
vectors (an i7-8700) that the lanes read.
-/

@[expose] public section

namespace Silmaril.X86.Str9L.Checks

open Silmaril.X86 (Byte Word State XReg)
open Silmaril.Process (Memory)
open Silmaril.X86.Features (FeatureSet)

/-- The feature set of the vectors' processor, as far as the lanes read it. -/
def host : FeatureSet := v3 ∪ FeatureSet.ofList [.aes, .pclmulqdq]

/-- A tower state: core `c`, the code at `0x1000`, one more read-write region, YMM registers
`ymm`, MXCSR `mx`; DF clear, x87 after FNINIT. -/
def stateOf (c : State) (code : List Byte) (data : Silmaril.Process.Region) (bytes : List Byte)
    (ymm : XReg → BitVec 256) (mx : Nat) : LState :=
  let memory : Memory := ⟨[⟨0x1000, code.length, ⟨true, false, true⟩⟩, data],
    Memory.install (Memory.install ∅ 0x1000 code) data.base bytes⟩
  ⟨⟨⟨⟨⟨⟨⟨c, memory⟩, fun r => (ymm r).extractLsb' 0 128⟩, fun _ => 0, true⟩,
      fun r => (ymm r).extractLsb' 128 128⟩, false⟩, Silmaril.X86.Features.X87.reset⟩,
    ⟨BitVec.ofNat 32 mx⟩⟩

/-- YMM `r` of a tower state. -/
def ymmOf (s : LState) (r : XReg) : BitVec 256 := s.hi r ++ s.xmm r

/-- **One `avx` vector through `Str9L.step`.** -/
def checkAvxVec (code : List Nat) (ins : List (Nat × Nat)) (memIn : Nat) (outs : List (Nat × Nat))
    (memOut mxIn mxOut : Nat) : Bool :=
  let bytes : List Byte := code.map (BitVec.ofNat 8)
  let input : XReg → BitVec 256 := fun r => match ins.lookup r.toBitVec.toNat with
    | some v => BitVec.ofNat 256 v
    | none => Silmaril.X86.Features.Avx.pattern r.toBitVec.toNat
  let c := Silmaril.X86.Features.vcore.write .rsi (BitVec.ofNat 64 Silmaril.X86.Features.Avx.bufBase)
  let s := stateOf c bytes Silmaril.X86.Features.Avx.bufRegion
    (Silmaril.X86.Features.Avx.natLe 64 memIn) input mxIn
  match step host lanes s with
  | none => false
  | some t =>
    (List.range 16).all (fun j =>
      let r : XReg := XReg.ofBitVec (BitVec.ofNat 4 j)
      ymmOf t r == match outs.lookup j with
        | some v => BitVec.ofNat 256 v
        | none => input r) &&
    t.memory.readBytes Silmaril.X86.Features.Avx.bufBase 64 ==
      some (Silmaril.X86.Features.Avx.natLe 64 memOut) &&
    t.core.rip.toNat == 0x1000 + bytes.length && t.mxcsr.bits == BitVec.ofNat 32 mxOut

/-- An `avx` vector line (the format of `Features.Avx.checkLine`). -/
def checkAvxLine : List Nat → Bool
  | len :: rest =>
    let code := rest.take len
    match rest.drop len with
    | nin :: rest =>
      match Silmaril.X86.Features.Avx.pairs nin rest with
      | some (ins, memIn :: nout :: rest) =>
        match Silmaril.X86.Features.Avx.pairs nout rest with
        | some (outs, [memOut, mxIn, mxOut]) =>
          code.length == len && checkAvxVec code ins memIn outs memOut mxIn mxOut
        | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- The upper half of YMM0 in the `roundss`/`roundsd` vectors (kept by the legacy form). -/
def roundHi : BitVec 128 := 0xDEAD_BEEF_0123_4567_89AB_CDEF_FEDC_BA98#128

/-- **One `roundss`/`roundsd xmm0, xmm1, imm8` vector through `Str9L.step`.** -/
def checkRound (dbl : Bool) (imm mx x lo hi rlo rhi mo : Nat) : Bool :=
  let bytes : List Byte := [0x66, 0x0F, 0x3A, if dbl then 0x0B else 0x0A, 0xC1, BitVec.ofNat 8 imm]
  let ymm : XReg → BitVec 256 := fun r =>
    if r = .xmm0 then roundHi ++ (BitVec.ofNat 64 hi ++ BitVec.ofNat 64 lo)
    else if r = .xmm1 then BitVec.ofNat 256 (0x0123456789abcdef * 2 ^ 64 + x) else 0
  let s := stateOf Silmaril.X86.Features.vcore bytes ⟨0x20000, 0, ⟨true, true, false⟩⟩ [] ymm mx
  match step host lanes s with
  | none => false
  | some t =>
    t.xmm .xmm0 == (BitVec.ofNat 64 rhi ++ BitVec.ofNat 64 rlo) && t.hi .xmm0 == roundHi &&
      t.mxcsr.bits == BitVec.ofNat 32 mo && t.core.rip.toNat == 0x1000 + 6

/-- A `roundss`/`roundsd` vector line (the format of `Features.checkRoundLine`). -/
def checkRoundLine : List Nat → Bool
  | [d, imm, mx, x, lo, hi, rlo, rhi, mo] => checkRound (d == 1) imm mx x lo hi rlo rhi mo
  | _ => false

end Silmaril.X86.Str9L.Checks
