module

public import Silmaril.X86.Features.Ext.Avx.Ops
public import Silmaril.X86.Ext.Syntax

/-!
# Syntax of the `avx` lane

An instruction is a form (`Op`, the opcode table of `Ops.lean`) together with
the fields of its VEX encoding (SDM Vol. 2A, §2.3): VEX.L, VEX.W, the ModRM.reg
field extended by VEX.R, the VEX.vvvv register, the ModRM.rm operand and the
imm8. `Instr.canonical` says that the fields the form fixes have their fixed
value: a fixed VEX.W or VEX.L, the `/digit` in ModRM.reg, the operand kind,
VEX.vvvv = 1111b (register 0 here; the field is stored inverted) when the form
has no vvvv operand, and a zero immediate when the form has none. `Syntax` is
the type of canonical instructions; each has exactly one encoding.

The ModRM.rm operand (`Opnd`) is a register number (a vector register, or a
general-purpose register for forms such as VMOVD) or a memory operand of the
integer machine (`Ext.Mem`), which includes RIP-relative, base-less and
FS-based addressing. A VSIB operand (the gathers) is a memory operand whose
index field names a vector register.
-/

@[expose] public section

namespace Silmaril.X86.Features.Avx

/-- The ModRM.rm operand: a register number or a memory operand. -/
inductive Opnd where
  | reg (n : BitVec 4)
  | mem (m : Ext.Mem)
  deriving DecidableEq, Repr

/-- An instruction: a form with the fields of its VEX encoding. -/
structure Instr where
  op : Op
  /-- VEX.L: 256-bit vector length. -/
  l : Bool
  /-- VEX.W. -/
  w : Bool
  /-- ModRM.reg with VEX.R as bit 3. -/
  reg : BitVec 4
  /-- The register VEX.vvvv names (the field holds its one's complement). -/
  vvvv : BitVec 4
  rm : Opnd
  imm : BitVec 8
  deriving DecidableEq, Repr

/-- Opcodes followed by an imm8 (SDM Vol. 2A, Appendix A, the VEX opcode maps):
every `0F3A` opcode, and `0F 70`–`73` and `0F C2`, `C4`–`C6`. -/
def hasImm (map : BitVec 5) (opc : BitVec 8) : Bool :=
  map == 3#5 || (map == 1#5 && (opc == 0x70#8 || opc == 0x71#8 || opc == 0x72#8 ||
    opc == 0x73#8 || opc == 0xC2#8 || opc == 0xC4#8 || opc == 0xC5#8 || opc == 0xC6#8))

/-- Every VEX opcode of the lane has a ModRM byte except `0F 77`
(VZEROUPPER, VZEROALL). -/
def hasModRM (map : BitVec 5) (opc : BitVec 8) : Bool := !(map == 1#5 && opc == 0x77#8)

/-- The operand kind admits the operand. A form without ModRM uses register 0
in both fields. -/
def kindOk : Kind → Opnd → BitVec 4 → Bool
  | .any, _, _ => true
  | .reg, .reg _, _ => true
  | .mem, .mem _, _ => true
  | .none, .reg n, reg => n == 0#4 && reg == 0#4
  | _, _, _ => false

/-- The fields the form fixes have their fixed values. -/
def Instr.canonical (i : Instr) : Bool :=
  let f := i.op.info
  f.w.all (· == i.w) && f.l.all (· == i.l) && f.digit.all (fun d => i.reg == 0#1 ++ d) &&
    kindOk f.kind i.rm i.reg && (f.vvvv || i.vvvv == 0#4) && (hasImm f.map f.opc || i.imm == 0#8)

/-- The canonical instructions: the syntax of the lane. -/
abbrev Syntax := {i : Instr // i.canonical = true}

end Silmaril.X86.Features.Avx
