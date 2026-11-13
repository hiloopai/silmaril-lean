module

public import Silmaril.X86.Ext.Syntax
public import Silmaril.X86.Float.Instr
public import Silmaril.X86.Features.Feature

/-!
# Syntax of the SSE3, SSSE3, SSE4.1 and SSE4.2 lane

The legacy-SSE (non-VEX) XMM forms of SSE3, SSSE3, SSE4.1 and SSE4.2, written
from the Intel SDM Vol. 2 instruction pages. Every form has a mandatory `66`,
`F2` or `F3` prefix and lives in the `0F`, `0F 38` or `0F 3A` opcode map. The
instructions fall into five shapes:

* `rr op dst src`: `op xmm, xmm/m` without an immediate (`Op2`);
* `ri op dst src imm`: `op xmm, xmm/m, imm8` (`OpI`);
* `extr op dst src imm`: PEXTRB/W/D/Q and EXTRACTPS, `r/m, xmm, imm8`;
* `ins op dst src imm`: PINSRB/D/Q, `xmm, r/m, imm8`;
* `crc32 sz dst src`: CRC32 `r32/r64, r/m8/r/m32/r/m64`.

Memory operands are the integer machine's `Ext.Mem`: a base register, no base,
RIP-relative or `fs:` with no base. MMX forms (the SSSE3 instructions without
the `66` prefix), the 16-bit CRC32 source (`66 F2 0F 38 F1`), and AH/CH/DH/BH as
the byte source of CRC32 are not part of the syntax; their bytes are not
decoded. ROUNDSS/ROUNDSD (`66 0F 3A 0A/0B`) belong to `X86.Float` (`floatExt`)
and are not repeated here.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse4

open Silmaril.X86 (XReg Reg Byte)

/-- An `xmm/m` source operand. -/
inductive Src where
  | reg (r : XReg)
  | mem (m : Ext.Mem)
  deriving DecidableEq, Repr

/-- The instructions of shape `op xmm, xmm/m` (no immediate). The CPUID feature
is `Op2.feature`. -/
inductive Op2 where
  -- SSE3
  | addsubpd | addsubps | haddpd | haddps | hsubpd | hsubps
  | movddup | movshdup | movsldup | lddqu
  -- SSSE3
  | pshufb | phaddw | phaddd | phaddsw | pmaddubsw | phsubw | phsubd | phsubsw
  | psignb | psignw | psignd | pmulhrsw | pabsb | pabsw | pabsd
  -- SSE4.1
  | pblendvb | blendvps | blendvpd | ptest
  | pmovsxbw | pmovsxbd | pmovsxbq | pmovsxwd | pmovsxwq | pmovsxdq
  | pmuldq | pcmpeqq | movntdqa | packusdw
  | pmovzxbw | pmovzxbd | pmovzxbq | pmovzxwd | pmovzxwq | pmovzxdq
  | pminsb | pminsd | pminuw | pminud | pmaxsb | pmaxsd | pmaxuw | pmaxud
  | pmulld | phminposuw
  -- SSE4.2
  | pcmpgtq
  deriving DecidableEq, Repr

/-- The instructions of shape `op xmm, xmm/m, imm8`. `pcmpestrm64` and
`pcmpestri64` are the REX.W forms, whose explicit lengths are RAX and RDX. -/
inductive OpI where
  -- SSSE3
  | palignr
  -- SSE4.1
  | roundps | roundpd | blendps | blendpd | pblendw | insertps | dpps | dppd | mpsadbw
  -- SSE4.2
  | pcmpestrm | pcmpestri | pcmpistrm | pcmpistri | pcmpestrm64 | pcmpestri64
  deriving DecidableEq, Repr

/-- PEXTRB, PEXTRW (the `0F 3A 15` form), PEXTRD, PEXTRQ and EXTRACTPS. -/
inductive ExtrOp where
  | pextrb | pextrw | pextrd | pextrq | extractps
  deriving DecidableEq, Repr

/-- PINSRB, PINSRD and PINSRQ. -/
inductive InsOp where
  | pinsrb | pinsrd | pinsrq
  deriving DecidableEq, Repr

/-- The CRC32 forms: `r32, r/m8` (`b`), `r64, r/m8` (`bq`), `r32, r/m32` (`d`)
and `r64, r/m64` (`q`). -/
inductive CrcSz where
  | b | bq | d | q
  deriving DecidableEq, Repr

/-- An instruction of the lane. The destination is the first operand, as in
Intel syntax. -/
inductive Instr where
  | rr (op : Op2) (dst : XReg) (src : Src)
  | ri (op : OpI) (dst : XReg) (src : Src) (imm : Byte)
  | extr (op : ExtrOp) (dst : Ext.RM) (src : XReg) (imm : Byte)
  | ins (op : InsOp) (dst : XReg) (src : Ext.RM) (imm : Byte)
  | crc32 (sz : CrcSz) (dst : Reg) (src : Ext.RM)
  deriving DecidableEq, Repr

/-! ## Features (SDM Vol. 2, the CPUID feature flag column) -/

/-- SSE3 for the first ten, SSSE3 for PSHUFB to PABSD, SSE4.2 for PCMPGTQ and
SSE4.1 for the rest. -/
def Op2.feature : Op2 → Feature
  | .addsubpd | .addsubps | .haddpd | .haddps | .hsubpd | .hsubps
  | .movddup | .movshdup | .movsldup | .lddqu => .sse3
  | .pshufb | .phaddw | .phaddd | .phaddsw | .pmaddubsw | .phsubw | .phsubd | .phsubsw
  | .psignb | .psignw | .psignd | .pmulhrsw | .pabsb | .pabsw | .pabsd => .ssse3
  | .pcmpgtq => .sse42
  | _ => .sse41

def OpI.feature : OpI → Feature
  | .palignr => .ssse3
  | .pcmpestrm | .pcmpestri | .pcmpistrm | .pcmpistri | .pcmpestrm64 | .pcmpestri64 => .sse42
  | _ => .sse41

/-- The CPUID features of an instruction. -/
def Instr.requires : Instr → List Feature
  | .rr op .. => [op.feature]
  | .ri op .. => [op.feature]
  | .extr .. | .ins .. => [.sse41]
  | .crc32 .. => [.sse42]

end Silmaril.X86.Features.Sse4
