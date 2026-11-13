module

public import Silmaril.X86.Ext.Syntax

/-!
# Baseline integer forms outside `X86.Ext`: syntax

The baseline-integer extension lane (no CPUID feature beyond x86-64) adds
the integer forms that the canonical integer machine `X86.Ext` rejects:

* ADC and SBB at 32 and 64 bits in every ALU form: `op r/m, reg`, `op reg, r/m`,
  `op r/m, imm32` (`81 /2`, `81 /3`), `op r/m, imm8` (`83 /2`, `83 /3`) and the
  accumulator form (`15`, `1D`) (`Instr.carry`);
* the eight ALU operations ADD, OR, ADC, SBB, AND, SUB, XOR and CMP at 16 bits
  (the `66` operand-size prefix) in the same five forms, with a 16-bit
  immediate (`Instr.alu16`);
* SHLD and SHRD by an imm8 or CL at 16, 32 and 64 bits (`0F A4/A5/AC/AD`,
  `Instr.shd`);
* BT, BTS, BTR and BTC with a register or imm8 bit offset, on a register or
  memory operand, at 16, 32 and 64 bits (`0F A3/AB/B3/BB`, `0F BA /4-7`,
  `Instr.bit`);
* PUSH imm32 and PUSH imm8 (`68`, `6A`), and `repz ret` (`F3 C3`).

Operands reuse `X86.Ext`'s `Reg`, `Mem` and `RM`, including RIP-relative and
`fs:` memory operands. 8-bit ALU forms and the AH-BH registers are not part of
this lane.
-/

@[expose] public section

namespace Silmaril.X86.Features.BaseInt

open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Sz RM Mem)

/-- Operand sizes of the lane: 16 bits (`66`), 32 bits, 64 bits (REX.W). -/
inductive Width where
  | w | d | q
  deriving DecidableEq, Repr

namespace Width

def bits : Width → Nat
  | .w => 16 | .d => 32 | .q => 64

def bytes : Width → Nat
  | .w => 2 | .d => 4 | .q => 8

/-- The 32/64-bit sizes of `X86.Ext`. -/
def ofSz : Sz → Width
  | .d => .d | .q => .q

@[simp] theorem bits_w : Width.w.bits = 16 := rfl
@[simp] theorem bits_d : Width.d.bits = 32 := rfl
@[simp] theorem bits_q : Width.q.bits = 64 := rfl

end Width

/-- The eight ALU operations, in the order of their ModRM `reg` digit. -/
inductive Op where
  | add | or | adc | sbb | and | sub | xor | cmp
  deriving DecidableEq, Repr

/-- ADC and SBB. -/
inductive CarryOp where
  | adc | sbb
  deriving DecidableEq, Repr

def CarryOp.toOp : CarryOp → Op
  | .adc => .adc | .sbb => .sbb

/-- The five ALU forms, with an `immBits`-bit full immediate. -/
inductive AluForm (immBits : Nat) where
  /-- `op r/m, reg` (opcode `8k+1`). -/
  | rm (dst : RM) (src : Reg)
  /-- `op reg, r/m` (opcode `8k+3`). -/
  | r (dst : Reg) (src : RM)
  /-- `op r/m, imm` (`81 /k`). -/
  | i (dst : RM) (imm : BitVec immBits)
  /-- `op r/m, imm8` (`83 /k`), sign-extended. -/
  | i8 (dst : RM) (imm : BitVec 8)
  /-- `op eAX, imm` (opcode `8k+5`). -/
  | a (imm : BitVec immBits)
  deriving DecidableEq, Repr

/-- The shift count of SHLD/SHRD: CL or an imm8, masked when executed. -/
inductive ShdCount where
  | cl
  | imm (n : BitVec 8)
  deriving DecidableEq, Repr

/-- BT, BTS, BTR, BTC, in the order of their `0F BA` digit (4 to 7). -/
inductive BtOp where
  | bt | bts | btr | btc
  deriving DecidableEq, Repr

/-- The bit offset of a BTx instruction. -/
inductive BtSrc where
  | reg (r : Reg)
  | imm (n : BitVec 8)
  deriving DecidableEq, Repr

/-- Instructions of the baseline-integer lane. -/
inductive Instr where
  /-- ADC/SBB at 32 or 64 bits. -/
  | carry (sz : Sz) (op : CarryOp) (form : AluForm 32)
  /-- The eight ALU operations at 16 bits. -/
  | alu16 (op : Op) (form : AluForm 16)
  /-- SHLD (`left = true`) or SHRD `dst, src, count`. -/
  | shd (sz : Width) (left : Bool) (dst : RM) (src : Reg) (count : ShdCount)
  /-- BT/BTS/BTR/BTC `dst, src`. -/
  | bit (sz : Width) (op : BtOp) (dst : RM) (src : BtSrc)
  /-- `push imm32` (`68 id`), sign-extended to 64 bits. -/
  | pushI (imm : BitVec 32)
  /-- `push imm8` (`6A ib`), sign-extended to 64 bits. -/
  | pushI8 (imm : BitVec 8)
  /-- `repz ret` (`F3 C3`). -/
  | repRet
  deriving DecidableEq, Repr

/-! ## Sub-families, for restrictions -/

namespace Instr

def isCarry : Instr → Bool
  | .carry .. => true | _ => false

def isAlu16 : Instr → Bool
  | .alu16 .. => true | _ => false

def isShd : Instr → Bool
  | .shd .. => true | _ => false

def isBit : Instr → Bool
  | .bit .. => true | _ => false

def isStack : Instr → Bool
  | .pushI _ | .pushI8 _ | .repRet => true | _ => false

end Instr

end Silmaril.X86.Features.BaseInt
