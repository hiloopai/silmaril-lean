module

public import Silmaril.X86.Str9L.Checks
public import Silmaril.X86.Features.Ext.Avx.Vectors
public import Silmaril.X86.Features.Vectors.Round
public import Silmaril.X86.Features.Ext.Sse2.Vectors
public import Silmaril.X86.Features.Ext.Sse4.Vectors
public import Silmaril.X86.Features.Ext.SseMerged.PackedVectors
public import Silmaril.X86.Features.Ext.IntMerged.Vectors
public import Silmaril.X86.Features.Cpuid.Models
public meta import Silmaril.X86.Str9L.Checks
public meta import Silmaril.X86.Features.Ext.Avx.Vectors
public meta import Silmaril.X86.Features.Vectors.Round
public meta import Silmaril.X86.Features.Ext.Sse2.Vectors
public meta import Silmaril.X86.Features.Ext.Sse4.Vectors
public meta import Silmaril.X86.Features.Ext.SseMerged.PackedVectors
public meta import Silmaril.X86.Features.Ext.IntMerged.Vectors
public meta import Silmaril.X86.Features.Cpuid.Models

/-! The `avx` lane's native vectors (`Features.Avx.Vectors`, 3,627 vectors from
`scripts/x86-features/gen_avx_vectors.py`) and the `roundss`/`roundsd` vectors
(`Features.Vectors.Round`, 7,168 from `scripts/x86-features/gen_vectors.py`), each run through
one `Str9L.step Checks.host lanes` (`Str9L.Checks`). The VEX forms `Str9V` decodes are run by
`Str9V`, the others by the `avx` lane; `roundss`/`roundsd` by `floatExt`. The SSE/SSE2
(3,876), packed SSE (2,148) and SSE3/SSSE3/SSE4 (3,036) lanes' native vectors likewise, with
each case's encoding as the code (`checkFormLine`), and the integer lanes' 1,800
(`checkIntLine`). -/

namespace Silmaril.X86.Str9L.Vectors

open Silmaril.X86.Features (hexFields)
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v0).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v1).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v2).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v3).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v4).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v5).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v6).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v7).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v8).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v9).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v10).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v11).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v12).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v13).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v14).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v15).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v16).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v17).all Checks.checkAvxLine
#guard (hexFields Silmaril.X86.Features.Avx.Vectors.v18).all Checks.checkAvxLine

#guard (hexFields Silmaril.X86.Features.Vectors.Round.vectors).all Checks.checkRoundLine

#guard (hexFields Silmaril.X86.Features.Sse2.Vectors.vectors).all
  (Checks.checkFormLine fun n => Silmaril.X86.Features.Sse2.encode
    (Silmaril.X86.Features.Sse2.Vectors.form n))

#guard (hexFields Silmaril.X86.Features.SseMerged.PackedVectors.vectors).all
  (Checks.checkFormLine fun n => Silmaril.X86.Features.SsePacked.encode
    (Silmaril.X86.Features.SseMerged.PackedVectors.form n))

#guard (hexFields Silmaril.X86.Features.Sse4.Vectors.vectors).all
  (Checks.checkFormLine fun n => Silmaril.X86.Features.Sse4.encode
    (Silmaril.X86.Features.Sse4.Vectors.form n))

#guard (hexFields Silmaril.X86.Features.IntMerged.vectors).all Checks.checkIntLine

/-! ## The census forms

Each instruction the demand census found outside the tower in zlib, gzip and glibc's
`sse2`/`ssse3`/`sse4_2` string variants is now read by a layer or a lane: `pshuflw`,
`psubd`, `paddq`, `pcmpgtd`, `pcmpeqd`, `paddd`, `movhlps`, `pinsrw`, `psubw`, `paddw`,
`punpckhwd`, `psubusw`, `pandn`, `paddb`, `pcmpgtb`, `movntps`, `palignr`, `pcmpistri`,
`pshufb`, `pminud`, `cvtsi2sd`, `mulsd`, `divsd`, `andn`, `blsr`. -/

/-- Some layer of `Str9X` claims the bytes, or a lane decodes them. -/
def readsAt (bytes : List Silmaril.X86.Byte) : Bool :=
  let s := Checks.stateOf Silmaril.X86.Features.vcore bytes Silmaril.X86.Features.Avx.bufRegion []
    (fun _ => 0) 0x1F80
  lowerClaims s.x || (Silmaril.X86.Features.extDecode lanes bytes).isSome

#guard [[0xF2, 0x0F, 0x70, 0xC1, 0x1B], [0x66, 0x0F, 0xFA, 0xC1], [0x66, 0x0F, 0xD4, 0xC1],
  [0x66, 0x0F, 0x66, 0xC1], [0x66, 0x0F, 0x76, 0xC1], [0x66, 0x0F, 0xFE, 0xC1], [0x0F, 0x12, 0xC1],
  [0x66, 0x0F, 0xC4, 0xC1, 0x02], [0x66, 0x0F, 0xF9, 0xC1], [0x66, 0x0F, 0xFD, 0xC1],
  [0x66, 0x0F, 0x69, 0xC1], [0x66, 0x0F, 0xD9, 0xC1], [0x66, 0x0F, 0xDF, 0xC1],
  [0x66, 0x0F, 0xFC, 0xC1], [0x66, 0x0F, 0x64, 0xC1], [0x0F, 0x2B, 0x07],
  [0x66, 0x0F, 0x3A, 0x0F, 0xC1, 0x05], [0x66, 0x0F, 0x3A, 0x63, 0xC1, 0x1A],
  [0x66, 0x0F, 0x38, 0x00, 0xC1], [0x66, 0x0F, 0x38, 0x3B, 0xC1], [0xF2, 0x48, 0x0F, 0x2A, 0xC0],
  [0xF2, 0x0F, 0x59, 0xC1], [0xF2, 0x0F, 0x5E, 0xC1], [0xC4, 0xE2, 0x78, 0xF2, 0xC1],
  [0xC4, 0xE2, 0x78, 0xF3, 0xC9]].all readsAt

-- `andn` and `blsr` (VEX-encoded BMI1) are the integer lane's, not the `avx` lane's.
#guard [[0xC4, 0xE2, 0x78, 0xF2, 0xC1], [0xC4, 0xE2, 0x78, 0xF3, 0xC9]].all fun bs =>
  (Silmaril.X86.Features.extDecode lanes bs).map (·.1.name) ==
    some Silmaril.X86.Features.IntMerged.intMerged.name

/-! ## CPUID and XGETBV on the tower

On each of the thirteen dumped processor models (`Features.Profile.models`: the native i7-8700 and
twelve qemu models), `cpuid` (`0F A2`) through `Str9L.stepOf p` writes the profile's answer
for leaves 0, 1 and 7 to EAX, EBX, ECX and EDX, and `xgetbv` (`0F 01 D0`, ECX = 0) writes
XCR0 to EDX:EAX where OSXSAVE is set and has no step where it is not. -/

/-- One `stepOf p` of `code` with RAX = `eax`, RCX = `ecx`. -/
def runSys (p : Silmaril.X86.Features.Profile) (code : List Silmaril.X86.Byte) (eax ecx : Nat) :
    Option LState :=
  let c : Silmaril.X86.State :=
    { Silmaril.X86.Features.vcore with
      regs := fun r => if r = .rax then BitVec.ofNat 64 eax else if r = .rcx then BitVec.ofNat 64 ecx
        else 0 }
  stepOf p (Checks.stateOf c code Silmaril.X86.Features.Avx.bufRegion [] (fun _ => 0) 0x1F80)

def cpuidOk (p : Silmaril.X86.Features.Profile) (leaf : Nat) : Bool :=
  match runSys p [0x0F, 0xA2] leaf 0 with
  | some t =>
    let r := p.cpuid (BitVec.ofNat 32 leaf) 0
    t.core.read .rax == r.eax.setWidth 64 && t.core.read .rbx == r.ebx.setWidth 64 &&
      t.core.read .rcx == r.ecx.setWidth 64 && t.core.read .rdx == r.edx.setWidth 64 &&
      t.core.rip.toNat == 0x1002
  | none => false

def xgetbvOk (p : Silmaril.X86.Features.Profile) : Bool :=
  match runSys p [0x0F, 0x01, 0xD0] 0 0, p.osxsave with
  | some t, true =>
    t.core.read .rax == (p.xcr0.setWidth 32).setWidth 64 &&
      t.core.read .rdx == (p.xcr0 >>> 32).setWidth 64 && t.core.rip.toNat == 0x1003
  | none, false => true
  | _, _ => false

#guard Silmaril.X86.Features.Profile.models.length == 13

#guard Silmaril.X86.Features.Profile.models.all fun p => [0, 1, 7].all (cpuidOk p) && xgetbvOk p

end Silmaril.X86.Str9L.Vectors
