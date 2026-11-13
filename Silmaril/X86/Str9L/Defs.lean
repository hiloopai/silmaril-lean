module

public import Silmaril.X86.Str9X.Defs
public import Silmaril.X86.Features.Embed
public import Silmaril.X86.Features.Ext.Avx.Extension
public import Silmaril.X86.Features.Ext.SseMerged.Extension
public import Silmaril.X86.Features.Ext.Sse4.Extension
public import Silmaril.X86.Features.Ext.IntMerged.Extension
public import Silmaril.X86.Features.Cpuid.Extension

/-!
# `Str9L`: `Str9X` with MXCSR and the lanes of the feature-parametric machine

The tower decodes only the SSE and AVX forms its layers list by hand (`Sse9`, `Str9G`,
`Str9V`). silmaril's feature-parametric machine has whole families as `Extension` lanes:
`floatExt` (`X86.Float`: scalar SSE/SSE2/SSE4.1 arithmetic, conversions, comparisons, `roundss`/
`roundsd`, MXCSR, `ldmxcsr`/`stmxcsr`; what glibc's `printf`/`strtod` paths, gzip and coreutils
`sort`, `df`, `ls`, `du`, `sleep`, `od` reach) and `Avx.ext` (998 VEX.128/256 forms, integer
and floating point). `Str9L` runs any list of lanes **at the end of `Str9X`'s fetch chain**,
on a processor with feature set `F`, unchanged: with `lanes`, also the SSE/SSE2 integer
forms of zlib and glibc's `sse2` string variants, SSSE3/SSE4.2 (`palignr`, `pshufb`,
`pcmpistri`) and BMI/ADX.

**State.** `LState` is a `Str9X.XState` (`x`) and MXCSR (`mxcsr`).

**The lane view.** `view s` is the feature-parametric state of `s`: the core, `zmm i` =
`hi i ++ xmm i` (zero-extended) for the sixteen registers the tower has and zero for
ZMM16–31, zero opmasks, MXCSR and the x87 state. `back s t m` takes a lane result `t` back:
the core, each `xmm r` (bits 127:0 of `t`'s ZMM `r`), each `hi r` (bits 255:128), MXCSR, the
x87 state and the memory `m`; the ghost state (`tsc`, `cetOff`) and DF are kept. The tower
has no state above bit 255, no ZMM16–31 and no opmasks: `view`/`back` are exact for lanes
that use only YMM0–15, i.e. for every lane on a processor without AVX-512 (`F` with no
AVX-512 feature, such as `v3`): an EVEX form then has the step `featureUD`, which is no step
here.

**Step.** Where `Str9X` claims the bytes (`lowerClaims`: `Str9D`'s chain or an x87 form)
`step` is `Str9X.step` with MXCSR kept, so every `Str9X` step is a step (`Thms.step_of_str9x`,
`Thms.extendsStr9X`). Elsewhere it decodes the fetch window with the lanes in list order
(`Features.extDecode`, as `Features.step` does), requires execute permission on the consumed
bytes, and runs `Features.extStep F` (the missing-feature check, then the lane's `exec`) on
`view s`; only a retirement is a step (faults, `featureUD` and `unmodeled` are not).

`F` is a parameter. `v3` is the x86-64-v3 psABI level (the processors `Str9V`'s forms
assume): x87, SSE through SSE4.2, POPCNT, LZCNT, BMI1, BMI2, MOVBE, AVX, AVX2, FMA, F16C.
-/

@[expose] public section

namespace Silmaril.X86.Str9L

open Silmaril.X86 (Reg Word State Byte XReg fetchWindow maxInstrLength)
open Silmaril.X86.Features (Extension FeatureSet Feature VReg)
open Silmaril.Process (Memory)

/-! ## State -/

/-- **The state**: a `Str9X` state and MXCSR. -/
structure LState where
  x : Str9X.XState
  mxcsr : Silmaril.X86.Float.MXCSR

/-- The core. -/
abbrev LState.core (s : LState) : State := s.x.core

/-- The memory. -/
abbrev LState.memory (s : LState) : Memory := s.x.memory

/-- XMM `r` (bits 127:0 of YMM `r`). -/
abbrev LState.xmm (s : LState) (r : XReg) : BitVec 128 := s.x.d.v.g.x.xmm r

/-- Bits 255:128 of YMM `r`. -/
abbrev LState.hi (s : LState) (r : XReg) : BitVec 128 := s.x.d.v.hi r

/-- The SSE register of a vector register number below 16. -/
def xregOf (i : VReg) : XReg := XReg.ofBitVec (BitVec.ofNat 4 i.val)

/-- **The lane view**: core, YMM0–15 zero-extended, ZMM16–31 and opmasks zero, MXCSR, x87. -/
def view (s : LState) : Silmaril.X86.Features.State :=
  ⟨s.core,
    fun i => if i.val < 16 then ((s.hi (xregOf i) ++ s.xmm (xregOf i) : BitVec 256).setWidth 512)
      else 0,
    fun _ => 0, s.mxcsr, s.x.fpu⟩

/-- **Back from a lane result**: core, XMM and upper YMM halves of registers 0–15, MXCSR,
x87 and memory; the ghost state and DF kept. -/
def back (s : LState) (t : Silmaril.X86.Features.State) (m : Memory) : LState :=
  ⟨⟨⟨⟨{ s.x.d.v.g with x := ⟨⟨t.core, m⟩, fun r => t.xmm r.toV⟩ },
      fun r => (t.ymm r.toV).extractLsb' 128 128⟩, s.x.d.df⟩, t.x87⟩, t.mxcsr⟩

/-! ## Profiles -/

/-- The x86-64-v3 psABI level. -/
def v3 : FeatureSet :=
  FeatureSet.ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt, .lzcnt, .bmi1,
    .bmi2, .movbe, .avx, .avx2, .fma, .f16c]

/-- The lanes: the legacy-encoded SSE/SSE2 profile `sseExts` (scalar SSE `floatExt`, the
SSE/SSE2 integer and move lane `sse2Ext`, the rest of the packed SSE/SSE2 lane), SSE3/SSSE3/
SSE4.1/SSE4.2 (`sse4Ext`), the integer extensions (`IntMerged.intMerged`: BMI1, BMI2, ADX,
MOVBE and the base forms `X86.Ext` lacks) and AVX/AVX2 (`Avx.ext`). -/
def lanes : List Extension :=
  Silmaril.X86.Features.sseExts ++
    [Silmaril.X86.Features.sse4Ext, Silmaril.X86.Features.IntMerged.intMerged,
      Silmaril.X86.Features.Avx.ext]

/-- The lanes of a processor profile `p`: `lanes` and CPUID/XGETBV answered by `p`
(`Features.sysExt p`; ld.so's `init_cpu_features` reads both). -/
def lanesWith (p : Silmaril.X86.Features.Profile) : List Extension :=
  lanes ++ [Silmaril.X86.Features.sysExt p]

/-! ## Step -/

/-- Some decoder of `Str9X` claims the bytes at RIP. -/
def lowerClaims (x : Str9X.XState) : Bool :=
  Str9X.lowerClaims x.d || (Str9X.fetchFpu x.memory x.core.rip.toNat).isSome

/-- Run a decoded lane form of `n` bytes on `F`: only a retirement is a step. -/
def execLane (F : FeatureSet) (e : Extension) (i : e.Syntax) (n : Nat) (s : LState) :
    Option LState :=
  match Silmaril.X86.Features.extStep F e i n ⟨view s, s.memory⟩ with
  | .retired m => some (back s m.state m.memory)
  | _ => none

/-- **One step** on a processor with features `F` and lanes `exts`: `Str9X.step` with MXCSR
kept where `Str9X` claims the bytes; otherwise the first lane that decodes the fetch window. -/
def step (F : FeatureSet) (exts : List Extension) (s : LState) : Option LState :=
  if lowerClaims s.x then (Str9X.step s.x).map fun x => ⟨x, s.mxcsr⟩
  else
    match Silmaril.X86.Features.extDecode exts
        (fetchWindow s.memory maxInstrLength s.core.rip.toNat) with
    | some ⟨e, i, n⟩ =>
      if s.memory.Permitted .execute s.core.rip.toNat n then execLane F e i n s else none
    | none => none

/-- The machine of a processor profile: its features, `lanesWith p`. -/
abbrev stepOf (p : Silmaril.X86.Features.Profile) (s : LState) : Option LState :=
  step p.features (lanesWith p) s

end Silmaril.X86.Str9L
