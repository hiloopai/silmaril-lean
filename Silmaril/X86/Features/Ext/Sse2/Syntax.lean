module

public import Silmaril.X86.Float.Instr
public import Silmaril.X86.Encoding
public import Silmaril.X86.Features.Feature

/-!
# Syntax of the legacy SSE/SSE2 integer and move instructions

The instructions of the SSE2 lane of the feature-parametric machine
(`Features.Machine`), written from the instruction pages of the Intel SDM,
Volume 2. All are legacy (non-VEX) encodings in the `0F` opcode map with the
mandatory prefix none, `66` or `F3`, and operate on XMM0–XMM15.

| Constructor | Mnemonics | Feature |
| --- | --- | --- |
| `movLoad`, `movStore`, `movRR`, `movRRStore` | MOVDQA, MOVDQU, MOVAPS, MOVUPS, MOVAPD, MOVUPD | SSE (PS) / SSE2 |
| `movdLoad`, `movdStore` | MOVD/MOVQ between XMM and m32/m64 (`66 [REX.W] 0F 6E/7E`) | SSE2 |
| `movqLoad`, `movqStore` | MOVQ `xmm, xmm/m64` (`F3 0F 7E`), MOVQ `xmm/m64, xmm` (`66 0F D6`) | SSE2 |
| `binop` | PAND/PANDN/POR/PXOR, PADD{B,W,D,Q}, PSUB{B,W,D,Q}, PCMPEQ{B,W,D}, PUNPCK{L,H}{BW,WD,DQ,QDQ}, PSRL/PSRA/PSLL by XMM | SSE2 |
| `shiftImm` | PSRL{W,D,Q}, PSRA{W,D}, PSLL{W,D,Q} by imm8 | SSE2 |
| `shiftBytes` | PSRLDQ, PSLLDQ | SSE2 |
| `pshufd` | PSHUFD | SSE2 |
| `pmovmskb` | PMOVMSKB `r32, xmm` | SSE2 |
| `pinsrw`, `pextrw` | PINSRW `xmm, r32/m16, imm8`, PEXTRW `r32, xmm, imm8` | SSE2 |

## Opcode space

The lane owns exactly these encodings; it is disjoint from the integer decoder
`Ext.decode` and from `X86.Float`'s scalar SSE decoder (`floatExt`). In
particular the register forms of MOVAPS/MOVAPD `0F 28` and of MOVD/MOVQ
`66 0F 6E/7E` with a general-purpose register belong to `floatExt`
(`Float.Instr.movap`, `movToX`, `movFromX`) and are not repeated here: this
lane has their memory forms only. MOVQ with a general-purpose register and
PMOVMSKB/PEXTRW with REX.W are not in the subset (their canonical forms have
REX.W clear).
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse2

open Silmaril.X86
open Silmaril.X86.Float (XRM GRM IntWidth)

/-- A full-width (128-bit) register move family: the mnemonic selects the
prefix, the alignment requirement and the CPUID feature. -/
inductive MovKind where
  /-- MOVDQA (`66 0F 6F/7F`), aligned. -/
  | dqa
  /-- MOVDQU (`F3 0F 6F/7F`). -/
  | dqu
  /-- MOVAPS (`0F 28/29`), aligned, SSE. -/
  | aps
  /-- MOVUPS (`0F 10/11`), SSE. -/
  | ups
  /-- MOVAPD (`66 0F 28/29`), aligned. -/
  | apd
  /-- MOVUPD (`66 0F 10/11`). -/
  | upd
  deriving DecidableEq, Repr

/-- The families whose load opcode has a register form in this lane (MOVAPS
and MOVAPD `0F 28` register forms belong to `floatExt`). -/
inductive RRKind where
  | dqa | dqu | ups | upd
  deriving DecidableEq, Repr

def RRKind.toMovKind : RRKind → MovKind
  | .dqa => .dqa | .dqu => .dqu | .ups => .ups | .upd => .upd

/-- The lane width of a packed integer operation. -/
inductive Lane where
  | b | w | d | q
  deriving DecidableEq, Repr

/-- PCMPEQ lane widths in SSE2 (PCMPEQQ is SSE4.1). -/
inductive CmpLane where
  | b | w | d
  deriving DecidableEq, Repr

/-- The bitwise operations. `andn` computes `(not dst) and src`. -/
inductive Logic where
  | and | andn | or | xor
  deriving DecidableEq, Repr

/-- The SSE2 shifts: logical right, arithmetic right and left, in the lane
widths that exist (there is no byte shift and no PSRAQ before AVX-512). -/
inductive ShiftKind where
  | srlw | srld | srlq | sraw | srad | sllw | slld | sllq
  deriving DecidableEq, Repr

/-- The two-operand `xmm, xmm/m128` operations (all `66 0F xx /r`). -/
inductive BinOp where
  | logic (op : Logic)
  | add (l : Lane)
  | sub (l : Lane)
  | cmpeq (l : CmpLane)
  | unpackLo (l : Lane)
  | unpackHi (l : Lane)
  /-- Shift each lane of the destination by the count in bits 63:0 of the source. -/
  | shift (k : ShiftKind)
  deriving DecidableEq, Repr

/-- SSE/SSE2 integer and move instructions. The destination is the first
operand, as in Intel syntax. -/
inductive Instr where
  /-- `MOVxxx xmm, m128` (load opcode `6F`/`28`/`10`). -/
  | movLoad (k : MovKind) (dst : XReg) (src : Mem)
  /-- `MOVxxx m128, xmm` (store opcode `7F`/`29`/`11`). -/
  | movStore (k : MovKind) (dst : Mem) (src : XReg)
  /-- `MOVxxx xmm, xmm` through the load opcode (ModRM `reg` is the destination). -/
  | movRR (k : RRKind) (dst src : XReg)
  /-- `MOVxxx xmm, xmm` through the store opcode (ModRM `r/m` is the destination). -/
  | movRRStore (k : MovKind) (dst src : XReg)
  /-- `MOVD xmm, m32` / `MOVQ xmm, m64` (`66 [REX.W] 0F 6E`): zero-extending load. -/
  | movdLoad (w : IntWidth) (dst : XReg) (src : Mem)
  /-- `MOVD m32, xmm` / `MOVQ m64, xmm` (`66 [REX.W] 0F 7E`). -/
  | movdStore (w : IntWidth) (dst : Mem) (src : XReg)
  /-- `MOVQ xmm, xmm/m64` (`F3 0F 7E`): bits 127:64 of the destination are zeroed. -/
  | movqLoad (dst : XReg) (src : XRM)
  /-- `MOVQ xmm/m64, xmm` (`66 0F D6`); a register destination has bits 127:64 zeroed. -/
  | movqStore (dst : XRM) (src : XReg)
  /-- `op xmm, xmm/m128`. -/
  | binop (op : BinOp) (dst : XReg) (src : XRM)
  /-- `PSRLW/.../PSLLQ xmm, imm8` (`66 0F 71/72/73 /digit ib`). -/
  | shiftImm (k : ShiftKind) (dst : XReg) (imm : Byte)
  /-- `PSRLDQ xmm, imm8` (`left = false`, `66 0F 73 /3`) or `PSLLDQ` (`/7`). -/
  | shiftBytes (left : Bool) (dst : XReg) (imm : Byte)
  /-- `PSHUFD xmm, xmm/m128, imm8` (`66 0F 70`). -/
  | pshufd (dst : XReg) (src : XRM) (imm : Byte)
  /-- `PMOVMSKB r32, xmm` (`66 0F D7`). -/
  | pmovmskb (dst : Reg) (src : XReg)
  /-- `PINSRW xmm, r32/m16, imm8` (`66 0F C4`). -/
  | pinsrw (dst : XReg) (src : GRM) (imm : Byte)
  /-- `PEXTRW r32, xmm, imm8` (`66 0F C5`). -/
  | pextrw (dst : Reg) (src : XReg) (imm : Byte)
  deriving DecidableEq, Repr

/-- MOVAPS and MOVUPS are SSE; every other form is SSE2. -/
def MovKind.isSse : MovKind → Bool
  | .aps | .ups => true
  | _ => false

/-- The aligned families (a misaligned memory operand is #GP(0)). -/
def MovKind.aligned : MovKind → Bool
  | .dqa | .aps | .apd => true
  | _ => false

/-- The CPUID features on each instruction's SDM page. -/
def Instr.requires : Instr → List Feature
  | .movLoad k .. | .movStore k .. | .movRRStore k .. => if k.isSse then [.sse] else [.sse2]
  | .movRR k .. => if k.toMovKind.isSse then [.sse] else [.sse2]
  | _ => [.sse2]

end Silmaril.X86.Features.Sse2
