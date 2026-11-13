module

public import Silmaril.X86.Float.Instr
public import Silmaril.X86.Features.Feature

/-!
# Syntax of the legacy-encoded SSE/SSE2 packed and integer SIMD instructions

The instruction lane `SsePacked` covers the 128-bit packed instructions of SSE
and SSE2 in their legacy (non-VEX) encodings, written from the Intel SDM Vol. 2
instruction pages. It extends `X86.Float` (scalar SSE/SSE2/SSE4.1) and does not
repeat it: the forms `X86.Float` decodes (MOVAPS/MOVAPD register moves,
ANDPS/ANDNPS/ORPS/XORPS and the PD forms with a register or base-register memory
operand, MOVD/MOVQ between XMM and a general-purpose register) are left to
`floatExt`, and the extension is disjoint from it (`Extension.lean`).

## Operands

`Addr` is a memory operand: the base-register form `X86.Mem` of `X86.Float`, or
RIP-relative `[rip + disp32]` (SDM Vol. 2A, §2.2.1.6), which `X86.Float` cannot
represent and which libcrypto uses for its constant tables. `Src` is an
`xmm/m` operand. Register operands are XMM0–XMM15 (`XReg`).

## The instructions

| Constructor | Instructions | Opcode | Feature |
| --- | --- | --- | --- |
| `load`, `store` | MOVAPS/MOVUPS (SSE), MOVAPD/MOVUPD/MOVDQA/MOVDQU (SSE2) memory forms | `0F 28/29`, `0F 10/11`, `66 0F 28/29`, `66 0F 10/11`, `66 0F 6F/7F`, `F3 0F 6F/7F` | SSE / SSE2 |
| `movReg` | MOVUPS/MOVUPD/MOVDQA/MOVDQU register moves | `0F 10`, `66 0F 10`, `66 0F 6F`, `F3 0F 6F` | SSE / SSE2 |
| `storeNT` | MOVNTPS, MOVNTPD, MOVNTDQ | `0F 2B`, `66 0F 2B`, `66 0F E7` | SSE / SSE2 |
| `maskmovdqu` | MASKMOVDQU | `66 0F F7` | SSE2 |
| `movqLoad`, `movqStore` | MOVQ xmm, xmm/m64; MOVQ m64, xmm | `F3 0F 7E`, `66 0F D6` | SSE2 |
| `movdLoad`, `movdStore` | MOVD/MOVQ xmm, m32/m64 and m32/m64, xmm | `66 [W] 0F 6E/7E` (memory) | SSE2 |
| `movHalfLoad`, `movHalfStore` | MOVLPS/MOVHPS (SSE), MOVLPD/MOVHPD (SSE2) | `[66] 0F 12/13/16/17` (memory) | SSE / SSE2 |
| `movhlps`, `movlhps` | MOVHLPS, MOVLHPS | `0F 12`, `0F 16` (register) | SSE |
| `movmsk` | MOVMSKPS (SSE), MOVMSKPD, PMOVMSKB (SSE2) | `0F 50`, `66 0F 50`, `66 0F D7` | SSE / SSE2 |
| `pinsrw`, `pextrw` | PINSRW, PEXTRW | `66 0F C4`, `66 0F C5` | SSE2 |
| `pint` | 56 packed-integer operations (`PIntOp`) | `66 0F xx` | SSE2 |
| `pshiftImm` | PSRLW/D/Q, PSRAW/D, PSLLW/D/Q, PSRLDQ, PSLLDQ by imm8 | `66 0F 71/72/73 /n ib` | SSE2 |
| `pshuf` | PSHUFD, PSHUFHW, PSHUFLW | `66/F3/F2 0F 70` | SSE2 |
| `arithp` | ADD/SUB/MUL/DIV/MIN/MAX PS/PD | `[66] 0F 58-5F` | SSE / SSE2 |
| `sqrtp` | SQRTPS, SQRTPD | `[66] 0F 51` | SSE / SSE2 |
| `cmpp` | CMPPS, CMPPD (predicates 0–7) | `[66] 0F C2 ib` | SSE / SSE2 |
| `logicRip` | ANDPS/ANDNPS/ORPS/XORPS and PD, RIP-relative source | `[66] 0F 54-57` | SSE / SSE2 |
| `unpckp` | UNPCKLPS/UNPCKHPS (SSE), UNPCKLPD/UNPCKHPD (SSE2) | `[66] 0F 14/15` | SSE / SSE2 |
| `shufp` | SHUFPS (SSE), SHUFPD (SSE2) | `[66] 0F C6 ib` | SSE / SSE2 |
| `cvtp` | CVTDQ2PS, CVTPS2DQ, CVTTPS2DQ, CVTPS2PD, CVTPD2PS, CVTDQ2PD, CVTPD2DQ, CVTTPD2DQ | `0F 5B`, `66 0F 5B`, `F3 0F 5B`, `0F 5A`, `66 0F 5A`, `F3 0F E6`, `F2 0F E6`, `66 0F E6` | SSE2 |
| `approx` | RCPPS, RSQRTPS, RCPSS, RSQRTSS | `0F 53`, `0F 52`, `F3 0F 53`, `F3 0F 52` | SSE |
| `fence` | LFENCE, MFENCE (SSE2), SFENCE (SSE) | `0F AE E8/F0/F8` | SSE / SSE2 |
| `prefetch` | PREFETCHNTA/T0/T1/T2 | `0F 18 /0`, `/1`, `/2`, `/3` | SSE |

The feature column is the CPUID flag of each SDM page. Every one of them is in
the x86-64 baseline (`FeatureSet.baseline64`), but the requirements are still
recorded so that feature transport and `featureUD` apply uniformly.
-/

@[expose] public section

namespace Silmaril.X86.Features.SsePacked

open Silmaril.X86 (XReg Mem Reg Byte)
open Silmaril.X86.Float (Precision CmpPred LogicOp IntWidth ArithOp)

/-! ## Operands -/

/-- A memory operand: a base-register form or `[rip + disp32]`. -/
inductive Addr where
  | mem (m : Mem)
  | rip (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- An `xmm/m` operand. -/
inductive Src where
  | reg (r : XReg)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-- An `r32/m16` operand (PINSRW). -/
inductive GSrc where
  | reg (r : Reg)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-! ## Operation tables -/

/-- The 128-bit moves with a load and a store opcode. -/
inductive MovKind where
  | aps | apd | ups | upd | dqa | dqu
  deriving DecidableEq, Repr

/-- The register-to-register moves outside `X86.Float` (which owns MOVAPS and
MOVAPD between registers). -/
inductive RegMov where
  | ups | upd | dqa | dqu
  deriving DecidableEq, Repr

def RegMov.toMovKind : RegMov → MovKind
  | .ups => .ups | .upd => .upd | .dqa => .dqa | .dqu => .dqu

/-- The non-temporal stores. -/
inductive NTKind where
  | ps | pd | dq
  deriving DecidableEq, Repr

/-- MOVMSKPS, MOVMSKPD, PMOVMSKB. -/
inductive MskKind where
  | ps | pd | b
  deriving DecidableEq, Repr

/-- The packed-integer two-operand instructions `66 0F xx /r` (SDM Vol. 2,
one page each). `destination ← op(destination, source)`. -/
inductive PIntOp where
  | paddb | paddw | paddd | paddq | psubb | psubw | psubd | psubq
  | paddsb | paddsw | paddusb | paddusw | psubsb | psubsw | psubusb | psubusw
  | pmullw | pmulhw | pmulhuw | pmuludq | pmaddwd | psadbw
  | pavgb | pavgw | pminub | pmaxub | pminsw | pmaxsw
  | pcmpeqb | pcmpeqw | pcmpeqd | pcmpgtb | pcmpgtw | pcmpgtd
  | pand | pandn | por | pxor
  | punpcklbw | punpcklwd | punpckldq | punpcklqdq
  | punpckhbw | punpckhwd | punpckhdq | punpckhqdq
  | packsswb | packssdw | packuswb
  | psrlw | psrld | psrlq | psraw | psrad | psllw | pslld | psllq
  deriving DecidableEq, Repr

/-- The shifts by an immediate, `66 0F 71/72/73 /n ib`. -/
inductive PShiftOp where
  | psrlw | psraw | psllw | psrld | psrad | pslld | psrlq | psrldq | psllq | pslldq
  deriving DecidableEq, Repr

/-- PSHUFD (`66`), PSHUFHW (`F3`), PSHUFLW (`F2`). -/
inductive ShufKind where
  | d | hw | lw
  deriving DecidableEq, Repr

/-- The packed conversions. -/
inductive CvtKind where
  /-- CVTDQ2PS: four int32 to four binary32. -/
  | dq2ps
  /-- CVTPS2DQ: four binary32 to int32, rounding by MXCSR.RC. -/
  | ps2dq
  /-- CVTTPS2DQ: the same, truncating. -/
  | tps2dq
  /-- CVTPS2PD: the low two binary32 to two binary64 (source m64). -/
  | ps2pd
  /-- CVTPD2PS: two binary64 to binary32 in the low half, high half zeroed. -/
  | pd2ps
  /-- CVTDQ2PD: the low two int32 to binary64 (source m64). -/
  | dq2pd
  /-- CVTPD2DQ: two binary64 to int32 in the low half, rounding by MXCSR.RC. -/
  | pd2dq
  /-- CVTTPD2DQ: the same, truncating. -/
  | tpd2dq
  deriving DecidableEq, Repr

/-- The approximate reciprocals, whose results the SDM bounds but does not
determine. -/
inductive ApproxKind where
  | rcpps | rsqrtps | rcpss | rsqrtss
  deriving DecidableEq, Repr

inductive FenceKind where
  | lfence | mfence | sfence
  deriving DecidableEq, Repr

/-- The PREFETCHh hint, in `/digit` order: NTA, T0, T1, T2. -/
inductive PrefetchHint where
  | nta | t0 | t1 | t2
  deriving DecidableEq, Repr

/-! ## Instructions -/

/-- The legacy-encoded SSE/SSE2 packed instructions of this lane. The
destination is the first operand, as in Intel syntax. -/
inductive Instr where
  /-- MOVAPS/MOVAPD/MOVUPS/MOVUPD/MOVDQA/MOVDQU `xmm, m128`. -/
  | load (k : MovKind) (dst : XReg) (src : Addr)
  /-- The same moves `m128, xmm`. -/
  | store (k : MovKind) (dst : Addr) (src : XReg)
  /-- MOVUPS/MOVUPD/MOVDQA/MOVDQU `xmm, xmm`. -/
  | movReg (k : RegMov) (dst src : XReg)
  /-- MOVNTPS/MOVNTPD/MOVNTDQ `m128, xmm`. -/
  | storeNT (k : NTKind) (dst : Addr) (src : XReg)
  /-- MASKMOVDQU `src, mask`: the bytes of `src` whose mask byte has bit 7 set
  are stored to `[rdi]`. -/
  | maskmovdqu (src mask : XReg)
  /-- MOVQ `xmm, xmm/m64` (`F3 0F 7E`): bits 127:64 zeroed. -/
  | movqLoad (dst : XReg) (src : Src)
  /-- MOVQ `m64, xmm` (`66 0F D6`). -/
  | movqStore (dst : Addr) (src : XReg)
  /-- MOVD `xmm, m32` / MOVQ `xmm, m64` (`66 [REX.W] 0F 6E`, memory). -/
  | movdLoad (w : IntWidth) (dst : XReg) (src : Addr)
  /-- MOVD `m32, xmm` / MOVQ `m64, xmm` (`66 [REX.W] 0F 7E`, memory). -/
  | movdStore (w : IntWidth) (dst : Addr) (src : XReg)
  /-- MOVLPS/MOVLPD (`high = false`) or MOVHPS/MOVHPD (`high = true`)
  `xmm, m64`; `pd` selects the `66` form. -/
  | movHalfLoad (high pd : Bool) (dst : XReg) (src : Addr)
  /-- The same `m64, xmm`. -/
  | movHalfStore (high pd : Bool) (dst : Addr) (src : XReg)
  /-- MOVHLPS `dst, src`: bits 63:0 of `dst` ← bits 127:64 of `src`. -/
  | movhlps (dst src : XReg)
  /-- MOVLHPS `dst, src`: bits 127:64 of `dst` ← bits 63:0 of `src`. -/
  | movlhps (dst src : XReg)
  /-- MOVMSKPS/MOVMSKPD/PMOVMSKB `r32, xmm`. -/
  | movmsk (k : MskKind) (dst : Reg) (src : XReg)
  /-- PINSRW `xmm, r32/m16, imm8`. -/
  | pinsrw (dst : XReg) (src : GSrc) (imm : Byte)
  /-- PEXTRW `r32, xmm, imm8`. -/
  | pextrw (dst : Reg) (src : XReg) (imm : Byte)
  /-- A packed-integer operation `xmm, xmm/m128`. -/
  | pint (op : PIntOp) (dst : XReg) (src : Src)
  /-- A shift of `dst` by `imm8`. -/
  | pshiftImm (op : PShiftOp) (dst : XReg) (imm : Byte)
  /-- PSHUFD/PSHUFHW/PSHUFLW `xmm, xmm/m128, imm8`. -/
  | pshuf (k : ShufKind) (dst : XReg) (src : Src) (imm : Byte)
  /-- ADD/SUB/MUL/DIV/MIN/MAX PS/PD `xmm, xmm/m128`. -/
  | arithp (op : ArithOp) (p : Precision) (dst : XReg) (src : Src)
  /-- SQRTPS/SQRTPD `xmm, xmm/m128`. -/
  | sqrtp (p : Precision) (dst : XReg) (src : Src)
  /-- CMPPS/CMPPD `xmm, xmm/m128, imm8` with predicate 0–7. -/
  | cmpp (p : Precision) (pred : CmpPred) (dst : XReg) (src : Src)
  /-- ANDPS/ANDNPS/ORPS/XORPS (or PD) `xmm, [rip + disp32]`. -/
  | logicRip (op : LogicOp) (p : Precision) (dst : XReg) (disp : BitVec 32)
  /-- UNPCKLPS/UNPCKLPD (`high = false`), UNPCKHPS/UNPCKHPD (`high = true`). -/
  | unpckp (high : Bool) (p : Precision) (dst : XReg) (src : Src)
  /-- SHUFPS/SHUFPD `xmm, xmm/m128, imm8`. -/
  | shufp (p : Precision) (dst : XReg) (src : Src) (imm : Byte)
  /-- A packed conversion `xmm, xmm/m128` (`xmm/m64` for CVTPS2PD, CVTDQ2PD). -/
  | cvtp (k : CvtKind) (dst : XReg) (src : Src)
  /-- RCPPS/RSQRTPS `xmm, xmm/m128`, RCPSS/RSQRTSS `xmm, xmm/m32`. -/
  | approx (k : ApproxKind) (dst : XReg) (src : Src)
  /-- LFENCE, MFENCE, SFENCE. -/
  | fence (k : FenceKind)
  /-- PREFETCHh `m8`. -/
  | prefetch (h : PrefetchHint) (a : Addr)
  deriving DecidableEq, Repr

/-! ## Required features -/

/-- SSE for the PS forms, SSE2 for the PD forms. -/
def precisionFeature : Precision → Feature
  | .single => .sse
  | .double => .sse2

def MovKind.feature : MovKind → Feature
  | .aps | .ups => .sse
  | _ => .sse2

/-- The CPUID features of each instruction's SDM page (CPUID column). -/
def Instr.requires : Instr → List Feature
  | .load k .. | .store k .. => [k.feature]
  | .movReg k .. => [k.toMovKind.feature]
  | .storeNT .ps .. => [.sse]
  | .storeNT _ .. => [.sse2]
  | .maskmovdqu .. | .movqLoad .. | .movqStore .. | .movdLoad .. | .movdStore .. => [.sse2]
  | .movHalfLoad _ pd .. | .movHalfStore _ pd .. => [if pd then .sse2 else .sse]
  | .movhlps .. | .movlhps .. => [.sse]
  | .movmsk .ps .. => [.sse]
  | .movmsk _ .. => [.sse2]
  | .pinsrw .. | .pextrw .. | .pint .. | .pshiftImm .. | .pshuf .. | .cvtp .. => [.sse2]
  | .arithp _ p .. | .sqrtp p .. | .cmpp p .. | .logicRip _ p .. | .unpckp _ p ..
  | .shufp p .. => [precisionFeature p]
  | .approx .. => [.sse]
  | .fence .sfence => [.sse]
  | .fence _ => [.sse2]
  | .prefetch .. => [.sse]

end Silmaril.X86.Features.SsePacked
