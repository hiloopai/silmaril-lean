module

public import Silmaril.X86.Ext.Syntax

/-!
# x87 instruction syntax

The x87 FPU instructions of 64-bit mode (SDM Vol. 2, the `D8`–`DF` escape
opcodes, and `9B` FWAIT), one constructor per operand form. Memory operands
are `X86.Ext.Mem`: a base register, no base, RIP-relative or `fs:`, with an
optional scaled index. Register operands `Fin 8` are stack positions ST(i).

The constructors are chosen so that every term has exactly one encoding:
forms the SDM does not have (FST m80 without pop, FIST m64 without pop) are
not expressible.
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

open Silmaril.X86.Ext (Mem)

/-- A memory floating-point format: `m32fp`, `m64fp`, `m80fp`. -/
inductive FFmt where
  | f32 | f64 | f80
  deriving DecidableEq, Repr

/-- The IEEE memory formats of FST, FCOM and the arithmetic forms. -/
inductive SFmt where
  | f32 | f64
  deriving DecidableEq, Repr

/-- A memory integer format: `m16int`, `m32int`, `m64int`. -/
inductive IFmt where
  | i16 | i32 | i64
  deriving DecidableEq, Repr

/-- The integer formats of FIST and the integer arithmetic forms. -/
inductive WFmt where
  | i16 | i32
  deriving DecidableEq, Repr

/-- The six arithmetic operations, by SDM mnemonic: `sub` is `dest − src`,
`subr` is `src − dest`, and likewise `div`/`divr`. -/
inductive Arith where
  | add | mul | sub | subr | div | divr
  deriving DecidableEq, Repr

/-- The FCMOVcc conditions: B (CF), E (ZF), BE (CF or ZF), U (PF) and their
negations. -/
inductive Cond where
  | b | e | be | u | nb | ne | nbe | nu
  deriving DecidableEq, Repr

/-- The instructions without an explicit operand. -/
inductive Nullary where
  | fnop | fchs | fabs | ftst | fxam
  | fld1 | fldl2t | fldl2e | fldpi | fldlg2 | fldln2 | fldz
  | f2xm1 | fyl2x | fptan | fpatan | fxtract | fprem1 | fdecstp | fincstp
  | fprem | fyl2xp1 | fsqrt | fsincos | frndint | fscale | fsin | fcos
  | fcompp | fucompp | fnclex | fninit | fnstswAx | fwait
  deriving DecidableEq, Repr

/-- An x87 instruction. -/
inductive Instr where
  /-- FLD m32fp/m64fp/m80fp (`D9 /0`, `DD /0`, `DB /5`). -/
  | fld (f : FFmt) (m : Mem)
  /-- FST m32fp/m64fp (`D9 /2`, `DD /2`). -/
  | fst (f : SFmt) (m : Mem)
  /-- FSTP m32fp/m64fp/m80fp (`D9 /3`, `DD /3`, `DB /7`). -/
  | fstp (f : FFmt) (m : Mem)
  /-- FILD m16int/m32int/m64int (`DF /0`, `DB /0`, `DF /5`). -/
  | fild (f : IFmt) (m : Mem)
  /-- FIST m16int/m32int (`DF /2`, `DB /2`). -/
  | fist (f : WFmt) (m : Mem)
  /-- FISTP m16int/m32int/m64int (`DF /3`, `DB /3`, `DF /7`). -/
  | fistp (f : IFmt) (m : Mem)
  /-- FISTTP m16int/m32int/m64int (`DF /1`, `DB /1`, `DD /1`; SSE3). -/
  | fisttp (f : IFmt) (m : Mem)
  /-- FADD/FMUL/FSUB/FSUBR/FDIV/FDIVR m32fp/m64fp (`D8 /r`, `DC /r`): ST(0) ← ST(0) op m. -/
  | arithMem (op : Arith) (f : SFmt) (m : Mem)
  /-- FIADD/... m16int/m32int (`DE /r`, `DA /r`). -/
  | arithInt (op : Arith) (f : WFmt) (m : Mem)
  /-- FCOM/FCOMP m32fp/m64fp (`D8 /2,/3`, `DC /2,/3`). -/
  | comMem (f : SFmt) (pop : Bool) (m : Mem)
  /-- FICOM/FICOMP m16int/m32int (`DE /2,/3`, `DA /2,/3`). -/
  | comInt (f : WFmt) (pop : Bool) (m : Mem)
  /-- `op ST(0), ST(i)` (`D8 C0+8r+i`): ST(0) ← ST(0) op ST(i). -/
  | arithSt0 (op : Arith) (i : Fin 8)
  /-- `op ST(i), ST(0)` and `opP ST(i), ST(0)` (`DC`/`DE C0+8r+i`): ST(i) ← ST(i) op ST(0). -/
  | arithSti (op : Arith) (i : Fin 8) (pop : Bool)
  /-- FLD ST(i) (`D9 C0+i`). -/
  | fldSt (i : Fin 8)
  /-- FST/FSTP ST(i) (`DD D0+i`, `DD D8+i`). -/
  | fstSt (i : Fin 8) (pop : Bool)
  /-- FXCH ST(i) (`D9 C8+i`). -/
  | fxch (i : Fin 8)
  /-- FFREE ST(i) (`DD C0+i`). -/
  | ffree (i : Fin 8)
  /-- FCOM/FCOMP ST(i) (`D8 D0+i`, `D8 D8+i`). -/
  | fcom (i : Fin 8) (pop : Bool)
  /-- FUCOM/FUCOMP ST(i) (`DD E0+i`, `DD E8+i`). -/
  | fucom (i : Fin 8) (pop : Bool)
  /-- FCOMI/FCOMIP/FUCOMI/FUCOMIP ST(0), ST(i) (`DB F0+i`, `DF F0+i`, `DB E8+i`, `DF E8+i`). -/
  | fcomi (unordered : Bool) (pop : Bool) (i : Fin 8)
  /-- FCMOVcc ST(0), ST(i) (`DA`/`DB C0+8c+i`). -/
  | fcmov (c : Cond) (i : Fin 8)
  /-- FLDCW m2byte (`D9 /5`). -/
  | fldcw (m : Mem)
  /-- FNSTCW m2byte (`D9 /7`). -/
  | fnstcw (m : Mem)
  /-- FNSTSW m2byte (`DD /7`). -/
  | fnstsw (m : Mem)
  /-- FLDENV m14/28byte (`D9 /4`). -/
  | fldenv (m : Mem)
  /-- FNSTENV m14/28byte (`D9 /6`). -/
  | fnstenv (m : Mem)
  /-- FRSTOR m94/108byte (`DD /4`). -/
  | frstor (m : Mem)
  /-- FNSAVE m94/108byte (`DD /6`). -/
  | fnsave (m : Mem)
  /-- FBLD m80dec (`DF /4`). -/
  | fbld (m : Mem)
  /-- FBSTP m80bcd (`DF /6`). -/
  | fbstp (m : Mem)
  /-- An instruction without operands. -/
  | nullary (op : Nullary)
  deriving DecidableEq, Repr

end Silmaril.X86.Features.Fpu
