module

public import Silmaril.X86.Str9L.Defs
public import Silmaril.X86.Features.Ext.Avx.Check
public import Silmaril.X86.Features.Checks
public import Silmaril.X86.Features.Ext.Sse2.Checks
public import Silmaril.X86.Features.Ext.IntMerged.Check

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
* `checkFormLine`: a vector of the SSE/SSE2 (`gen_sse2_vectors.py`), packed SSE
  (`gen_sse_packed_vectors.py`) or SSE3/SSSE3/SSE4 (`gen_sse4_vectors.py`) lane, with the
  form's encoding as the code. Forms `Sse9` and `Str9G` decode (`pxor`, `pcmpeqb`, `pminub`,
  `pmovmskb`, `pshufd`, `movdqu`, …) are run by them.
* `checkIntLine`: a vector of the integer lanes (`gen_int_vectors.py`): BMI1/BMI2, ADX,
  MOVBE, ADC/SBB, the 16-bit ALU, SHLD/SHRD, BTx, PUSH imm, `repz ret`; forms the tower's
  integer layers decode are run by them.
* `checkRoundLine`: a `roundss`/`roundsd xmm0, xmm1, imm8` vector
  (`scripts/x86-features/gen_vectors.py`): XMM0 and MXCSR as on the processor, the upper
  half of YMM0 kept.

`host` is `v3` with AES, PCLMULQDQ, ADX, RDRAND and RDSEED, the features of the processor
that produced the vectors (an i7-8700) that the lanes read.
-/

@[expose] public section

namespace Silmaril.X86.Str9L.Checks

open Silmaril.X86 (Byte Word State XReg)
open Silmaril.Process (Memory)
open Silmaril.X86.Features (FeatureSet)

/-- The feature set of the vectors' processor, as far as the lanes read it. -/
def host : FeatureSet := v3 ∪ FeatureSet.ofList [.aes, .pclmulqdq, .adx, .rdrand, .rdseed]

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

/-- **One vector of the SSE/SSE2, packed SSE or SSE3/SSSE3/SSE4 lane through `Str9L.step`**:
the form's encoding at `0x1000`, YMM0 = `a`, YMM1 = `b`, RAX, RDI at `off` in the 32-byte
buffer at `0x10000` (the format of `Sse2.Checks.checkVector`). YMM0 must be the processor's
`ra` (a legacy form keeps bits 255:128), YMM1, RDI kept, RAX and the buffer as on the
processor, RIP past the encoding. -/
def checkForm (code : List Byte) (a b rax off mem ra rax' mem' : Nat) : Bool :=
  let base := Silmaril.X86.Features.Sse2.Checks.vbase
  let c : State :=
    { regs := fun r => if r = .rax then BitVec.ofNat 64 rax
        else if r = .rdi then BitVec.ofNat 64 (base + off) else 0
      rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }
  let ymm : XReg → BitVec 256 := fun r =>
    if r = .xmm0 then BitVec.ofNat 256 a else if r = .xmm1 then BitVec.ofNat 256 b else 0
  let s := stateOf c code Silmaril.X86.Features.Sse2.Checks.vregion
    (Silmaril.X86.Features.Sse2.Checks.bytesOf mem 32) ymm 0x1F80
  match step host lanes s with
  | none => false
  | some t =>
    ymmOf t .xmm0 == BitVec.ofNat 256 ra && ymmOf t .xmm1 == BitVec.ofNat 256 b &&
      t.core.read .rax == BitVec.ofNat 64 rax' && t.core.read .rdi == BitVec.ofNat 64 (base + off) &&
      t.core.rip.toNat == 0x1000 + code.length &&
      t.memory.readBytes base 32 == some (Silmaril.X86.Features.Sse2.Checks.bytesOf mem' 32)

/-- A line `case ymm0 ymm1 rax offset buffer ymm0' rax' buffer'` of a lane whose case `n`
is encoded as `enc n`. -/
def checkFormLine (enc : Nat → List Byte) : List Nat → Bool
  | [n, a, b, rax, off, mem, ra, rax', mem'] => checkForm (enc n) a b rax off mem ra rax' mem'
  | _ => false

/-- **One vector of the integer lanes through `Str9L.step`** (the format of
`IntMerged.check`): the sixteen registers and RFLAGS, the 64-byte data area at
`IntMerged.dataBase`, the sixteen bytes around RSP, the code at `0x1000`. The step must
retire with the processor's registers, defined flags, data words and pushed word, RIP past
the code; a vector the merged lane leaves `unmodeled` may also have no step. -/
def checkIntLine (row : List Nat) : Bool :=
  match row with
  | _ :: len :: code :: rest =>
    let regs := rest.take 16
    let rflags := rest.getD 16 0
    let data := (rest.drop 17).take 8
    let rsp := regs.getD 4 0
    let bytes := Silmaril.X86.Features.IntMerged.codeBytes len code
    let c : State :=
      { regs := fun r => BitVec.ofNat 64
          (regs.getD (Silmaril.X86.Features.IntMerged.regList.idxOf r) 0)
        rip := 0x1000, flags := Silmaril.X86.Features.IntMerged.flagsOf rflags }
    let m := Silmaril.X86.Features.IntMerged.initMemory data rsp
    let memory : Memory := ⟨⟨0x1000, bytes.length, ⟨true, false, true⟩⟩ :: m.regions,
      Memory.install m.bytes 0x1000 bytes⟩
    let s : LState := ⟨⟨⟨⟨⟨⟨⟨c, memory⟩, fun _ => 0⟩, fun _ => 0, true⟩, fun _ => 0⟩, false⟩,
      Silmaril.X86.Features.X87.reset⟩, Silmaril.X86.Float.MXCSR.reset⟩
    match step host lanes s with
    | some t =>
      Silmaril.X86.Features.IntMerged.agrees len rsp (view t) t.memory ((rest.drop 25).take 16)
        (rest.getD 41 0) ((rest.drop 42).take 8) (rest.getD 50 0)
    | none =>
      Silmaril.X86.Features.IntMerged.check Silmaril.X86.Features.IntMerged.intMerged row ==
        .unmodeled
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
