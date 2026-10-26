module

public import Silmaril.X86.Basic

/-!
# Syntax of scalar SSE/SSE2/SSE4.1 floating-point instructions on x86-64

This file gives the abstract syntax of a scalar floating-point subset of x86-64
in 64-bit mode, written from the instruction pages of the Intel 64 and IA-32
Architectures Software Developer's Manual (SDM), Volume 2 (Chapters 3 and 4). It
is a specification from documents, not a correspondence with hardware or with
any reference model. Semantics are not defined here.

Two parts are independent of floating point and are placed in the
`Silmaril.X86` namespace for reuse by later integer or vector memory forms:

* `XReg`, the sixteen XMM registers addressable without EVEX (SDM Vol. 1,
  §10.2.2, and Vol. 2A, §2.2.1.2 for the REX extension to XMM8-XMM15);
* `Mem`, a memory operand `[base + index * scale + disp32]` (SDM Vol. 2A,
  §2.1.5, Tables 2-2 and 2-3, and §2.2.1.2, Table 2-5). RIP-relative operands
  (§2.2.1.6) and the base-less SIB form (`mod = 00`, SIB base `101`) are not
  representable. RSP cannot be an index (SIB index `100` with REX.X = 0 means
  "no index"), so the index register has type `IndexReg`.

The instructions in `Silmaril.X86.Float.Instr` are:

| Constructor | Mnemonics | Required feature |
| --- | --- | --- |
| `movs`, `load`, `store` | MOVSS / MOVSD (register, load, store) | SSE / SSE2 |
| `movToX`, `movFromX` | MOVD / MOVQ between XMM and a GPR | SSE2 |
| `movap` | MOVAPS / MOVAPD register form | SSE / SSE2 |
| `arith` | ADD, SUB, MUL, DIV, MIN, MAX (SS / SD) | SSE / SSE2 |
| `sqrt` | SQRTSS / SQRTSD | SSE / SSE2 |
| `cvtFromInt` | CVTSI2SS / CVTSI2SD | SSE / SSE2 |
| `cvtToIntTrunc`, `cvtToInt` | CVTTSS2SI / CVTTSD2SI, CVTSS2SI / CVTSD2SI | SSE / SSE2 |
| `cvtPrec` | CVTSS2SD / CVTSD2SS | SSE2 |
| `ucomi`, `comi` | UCOMISS / UCOMISD, COMISS / COMISD | SSE / SSE2 |
| `logic` | ANDPS/PD, ANDNPS/PD, ORPS/PD, XORPS/PD | SSE / SSE2 |
| `round` | ROUNDSS / ROUNDSD | SSE4.1 |
| `cmp` | CMPSS / CMPSD with predicates 0-7 | SSE / SSE2 |
| `ldmxcsr`, `stmxcsr` | LDMXCSR / STMXCSR | SSE |

The feature column is the CPUID flag named on each instruction page; SSE4.1 is
the only one that is not part of the x86-64 baseline. VEX/EVEX (AVX) forms,
packed arithmetic, x87 and MMX are out of scope.
-/

@[expose] public section

namespace Silmaril.X86

/-! ## XMM registers -/

/-- The sixteen XMM registers of 64-bit mode (without EVEX), in hardware-number
order. Only their encoding numbers are used here; their 128-bit contents belong
to a later semantics. -/
inductive XReg where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr

namespace XReg

/-- The four-bit register number (REX extension bit followed by the three-bit
ModRM field). -/
def toBitVec : XReg → BitVec 4
  | xmm0 => 0 | xmm1 => 1 | xmm2 => 2 | xmm3 => 3
  | xmm4 => 4 | xmm5 => 5 | xmm6 => 6 | xmm7 => 7
  | xmm8 => 8 | xmm9 => 9 | xmm10 => 10 | xmm11 => 11
  | xmm12 => 12 | xmm13 => 13 | xmm14 => 14 | xmm15 => 15

def ofBitVec (b : BitVec 4) : XReg :=
  match b.toNat with
  | 0 => xmm0 | 1 => xmm1 | 2 => xmm2 | 3 => xmm3
  | 4 => xmm4 | 5 => xmm5 | 6 => xmm6 | 7 => xmm7
  | 8 => xmm8 | 9 => xmm9 | 10 => xmm10 | 11 => xmm11
  | 12 => xmm12 | 13 => xmm13 | 14 => xmm14 | _ => xmm15

@[simp] theorem ofBitVec_toBitVec (r : XReg) : ofBitVec r.toBitVec = r := by
  cases r <;> rfl

@[simp] theorem toBitVec_ofBitVec (b : BitVec 4) : (ofBitVec b).toBitVec = b := by
  revert b
  decide

theorem toBitVec_injective : Function.Injective toBitVec := by
  intro r q h
  simpa using congrArg ofBitVec h

end XReg

/-! ## Memory operands -/

/-- The SIB scale factor. -/
inductive Scale where
  | s1 | s2 | s4 | s8
  deriving DecidableEq, Repr

namespace Scale

/-- The two-bit SIB `scale` field. -/
def toBitVec : Scale → BitVec 2
  | s1 => 0 | s2 => 1 | s4 => 2 | s8 => 3

def ofBitVec (b : BitVec 2) : Scale :=
  match b.toNat with
  | 0 => s1 | 1 => s2 | 2 => s4 | _ => s8

/-- The multiplier applied to the index register. -/
def factor : Scale → Nat
  | s1 => 1 | s2 => 2 | s4 => 4 | s8 => 8

@[simp] theorem ofBitVec_toBitVec (s : Scale) : ofBitVec s.toBitVec = s := by
  cases s <;> rfl

@[simp] theorem toBitVec_ofBitVec (b : BitVec 2) : (ofBitVec b).toBitVec = b := by
  revert b
  decide

end Scale

/-- A general-purpose register usable as a SIB index. RSP is excluded: the SIB
index field `100` with REX.X = 0 encodes "no index" (SDM Vol. 2A, Table 2-3 and
Table 2-5). R12 (`100` with REX.X = 1) is a valid index. -/
abbrev IndexReg := {r : Reg // r ≠ .rsp}

/-- A memory operand `[base + index * scale + disp]` with a signed 32-bit
displacement. The encoder chooses the shortest displacement form. -/
structure Mem where
  base : Reg
  index : Option (IndexReg × Scale) := none
  disp : BitVec 32 := 0
  deriving DecidableEq, Repr

/-- The 64-bit effective address, computed modulo 2^64 from the given register
values: base plus scaled index plus the sign-extended displacement (SDM Vol. 1,
§3.7.5). Canonical-address checks and segmentation are not modeled. -/
def Mem.effectiveAddress (m : Mem) (read : Reg → Word) : Word :=
  let scaled := match m.index with
    | some (i, s) => read i.1 * BitVec.ofNat 64 s.factor
    | none => 0
  read m.base + scaled + m.disp.signExtend 64

/-! ## Floating-point instruction syntax -/

namespace Float

/-- Scalar format: the SS (binary32) or SD (binary64) form; for the packed
logical instructions, the PS or PD form. -/
inductive Precision where
  | single | double
  deriving DecidableEq, Repr

/-- The general-purpose operand size of a conversion or MOVD/MOVQ; `w64` is
selected by REX.W. -/
inductive IntWidth where
  | w32 | w64
  deriving DecidableEq, Repr

/-- An `xmm/m` operand. -/
inductive XRM where
  | reg (r : XReg)
  | mem (m : Mem)
  deriving DecidableEq, Repr

/-- An `r/m32` or `r/m64` operand. -/
inductive GRM where
  | reg (r : Reg)
  | mem (m : Mem)
  deriving DecidableEq, Repr

/-- The scalar binary arithmetic operations with the SS/SD opcode pattern. -/
inductive ArithOp where
  | add | sub | mul | div | min | max
  deriving DecidableEq, Repr

/-- The bitwise packed operations used for absolute value, negation and
copy-sign. `andn` computes `(not dst) and src`. -/
inductive LogicOp where
  | and | andn | or | xor
  deriving DecidableEq, Repr

/-- The eight CMPSS/CMPSD predicates of the legacy (non-VEX) encoding, in
immediate order 0-7 (SDM Vol. 2A, CMPPD, Table 3-1). -/
inductive CmpPred where
  | eq | lt | le | unord | neq | nlt | nle | ord
  deriving DecidableEq, Repr

namespace CmpPred

def toBitVec : CmpPred → BitVec 3
  | eq => 0 | lt => 1 | le => 2 | unord => 3 | neq => 4 | nlt => 5 | nle => 6 | ord => 7

def ofBitVec (b : BitVec 3) : CmpPred :=
  match b.toNat with
  | 0 => eq | 1 => lt | 2 => le | 3 => unord | 4 => neq | 5 => nlt | 6 => nle | _ => ord

@[simp] theorem ofBitVec_toBitVec (p : CmpPred) : ofBitVec p.toBitVec = p := by
  cases p <;> rfl

@[simp] theorem toBitVec_ofBitVec (b : BitVec 3) : (ofBitVec b).toBitVec = b := by
  revert b
  decide

end CmpPred

/-- The ROUNDSS/ROUNDSD immediate, bits 3:0 (SDM Vol. 2B, ROUNDPD, Figure
"Bit Control Fields of Immediate Byte for ROUNDxx Instruction"): `rc` is
imm8[1:0], the rounding control used when `useMxcsr` (imm8[2], "RS") is false;
`suppressInexact` is imm8[3] ("P"), which suppresses the precision exception.
Bits 7:4 are reserved and are zero in this syntax. -/
structure RoundImm where
  rc : BitVec 2
  useMxcsr : Bool
  suppressInexact : Bool
  deriving DecidableEq, Repr

/-- A CPUID feature an instruction requires. `sse` is CPUID.01H:EDX[25],
`sse2` is CPUID.01H:EDX[26] and `sse41` is CPUID.01H:ECX[19]. SSE and SSE2 are
architecturally present in every processor supporting 64-bit mode. -/
inductive Feature where
  | sse | sse2 | sse41
  deriving DecidableEq, Repr

/-- Scalar SSE/SSE2/SSE4.1 instructions. Register operands are XMM registers
unless their type is `Reg`. The destination is the first operand, as in Intel
syntax. -/
inductive Instr where
  /-- `MOVSS/MOVSD dst, src` (register form; upper destination bits kept). -/
  | movs (p : Precision) (dst src : XReg)
  /-- `MOVSS/MOVSD dst, m32/m64` (load; upper destination bits zeroed). -/
  | load (p : Precision) (dst : XReg) (src : Mem)
  /-- `MOVSS/MOVSD m32/m64, src`. -/
  | store (p : Precision) (dst : Mem) (src : XReg)
  /-- `MOVD xmm, r32` / `MOVQ xmm, r64`. -/
  | movToX (w : IntWidth) (dst : XReg) (src : Reg)
  /-- `MOVD r32, xmm` / `MOVQ r64, xmm`. -/
  | movFromX (w : IntWidth) (dst : Reg) (src : XReg)
  /-- `MOVAPS/MOVAPD dst, src` (register form). -/
  | movap (p : Precision) (dst src : XReg)
  /-- `ADDSS`, `SUBSS`, ..., `MAXSD dst, src`. -/
  | arith (op : ArithOp) (p : Precision) (dst : XReg) (src : XRM)
  /-- `SQRTSS/SQRTSD dst, src`. -/
  | sqrt (p : Precision) (dst : XReg) (src : XRM)
  /-- `CVTSI2SS/CVTSI2SD dst, r/m32` or `r/m64`. -/
  | cvtFromInt (p : Precision) (w : IntWidth) (dst : XReg) (src : GRM)
  /-- `CVTTSS2SI/CVTTSD2SI r32/r64, src` (truncating). -/
  | cvtToIntTrunc (p : Precision) (w : IntWidth) (dst : Reg) (src : XRM)
  /-- `CVTSS2SI/CVTSD2SI r32/r64, src` (rounding by MXCSR.RC). -/
  | cvtToInt (p : Precision) (w : IntWidth) (dst : Reg) (src : XRM)
  /-- `CVTSS2SD dst, src` when `p = single`, `CVTSD2SS dst, src` when
  `p = double`; `p` is the source format. -/
  | cvtPrec (p : Precision) (dst : XReg) (src : XRM)
  /-- `UCOMISS/UCOMISD a, b`. -/
  | ucomi (p : Precision) (a : XReg) (b : XRM)
  /-- `COMISS/COMISD a, b`. -/
  | comi (p : Precision) (a : XReg) (b : XRM)
  /-- `ANDPS`, `ANDNPS`, `ORPS`, `XORPS` (or the PD forms) `dst, src`. -/
  | logic (op : LogicOp) (p : Precision) (dst : XReg) (src : XRM)
  /-- `ROUNDSS/ROUNDSD dst, src, imm8`. -/
  | round (p : Precision) (dst : XReg) (src : XRM) (ctrl : RoundImm)
  /-- `CMPSS/CMPSD dst, src, imm8`. -/
  | cmp (p : Precision) (pred : CmpPred) (dst : XReg) (src : XRM)
  /-- `LDMXCSR m32`. -/
  | ldmxcsr (src : Mem)
  /-- `STMXCSR m32`. -/
  | stmxcsr (dst : Mem)
  deriving DecidableEq, Repr

/-- SS and PS forms are SSE; SD and PD forms are SSE2. -/
def Precision.feature : Precision → Feature
  | .single => .sse | .double => .sse2

/-- The CPUID feature named on the instruction's SDM page. -/
def Instr.feature : Instr → Feature
  | .movs p .. | .load p .. | .store p .. | .movap p .. | .arith _ p .. | .sqrt p ..
  | .cvtFromInt p .. | .cvtToIntTrunc p .. | .cvtToInt p .. | .ucomi p .. | .comi p ..
  | .logic _ p .. | .cmp p .. => p.feature
  | .movToX .. | .movFromX .. | .cvtPrec .. => .sse2
  | .round .. => .sse41
  | .ldmxcsr _ | .stmxcsr _ => .sse

end Float
end Silmaril.X86
