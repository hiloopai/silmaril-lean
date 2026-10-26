module

public import Silmaril.RiscV.LPS.Prelude

/-!
# LPS RISC-V instruction syntax (RV64GC base AST)

Hand translation of `theories/Riscv/Instr.v` (LPS commit `f1006fe8`, MIT).

Design rules, as upstream:

* immediates are kept at their *encoded* width with the sign bit included (I/S: 12 bits,
  B: 13, U: 20, J: 21); sign extension and shifting happen in the semantics;
* compressed instructions have their own syntax (`CInstr`, in `DecodeC`) and are expanded
  into this one, so the execution semantics is written once.

Rocq constructor names `ALU_ADD`, `M_MUL`, … become Lean constructors `AluOp.add`,
`MulOp.mul`, …; see `docs/RiscVLPS.md` for the table.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

/-- Integer register-register operations, opcodes OP / OP-32 (`aluop`). -/
inductive AluOp where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, Repr

/-- M extension operations (`mulop`). -/
inductive MulOp where
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- Branch conditions (`branch_cond`). -/
inductive BranchCond where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

/-- Memory access sizes in bytes (`msize`). -/
inductive MSize where
  | sz1 | sz2 | sz4 | sz8
  deriving DecidableEq, Repr

/-- A extension operations (`amoop`). -/
inductive AmoOp where
  | swap | add | xor | and | or | min | max | minu | maxu
  deriving DecidableEq, Repr

/-- `.w` / `.d` (`awidth`). -/
inductive AWidth where
  | w | d
  deriving DecidableEq, Repr

/-- Zicsr operations (`csrop`). -/
inductive CsrOp where
  | rw | rs | rc
  deriving DecidableEq, Repr

/-- F/D formats (`ffmt`). -/
inductive FFmt where
  | s | d
  deriving DecidableEq, Repr

/-- `fariop`. -/
inductive FAriOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

/-- `fmaop`. -/
inductive FmaOp where
  | madd | msub | nmsub | nmadd
  deriving DecidableEq, Repr

/-- `fsgnop`. -/
inductive FSgnOp where
  | sgnj | sgnjn | sgnjx
  deriving DecidableEq, Repr

/-- `fminmaxop`. -/
inductive FMinMaxOp where
  | min | max
  deriving DecidableEq, Repr

/-- `fcmpop`. -/
inductive FCmpOp where
  | eq | lt | le
  deriving DecidableEq, Repr

/-- Operand kind of an `Instr.fcvt`: integer (32/64, signed/unsigned) or FP format
(`fcvt_ty`). Decoding produces only the architecturally valid pairs. -/
inductive FCvtTy where
  | w | wu | l | lu | s | d
  deriving DecidableEq, Repr

/-- Direction of a raw `fmv` (`fmvdir`): `xF` is `fmv.x.*`, `fX` is `fmv.*.x`. -/
inductive FMvDir where
  | xF | fX
  deriving DecidableEq, Repr

/-- The RV64GC base instruction syntax (`instr`). -/
inductive Instr where
  -- RV32I / RV64I
  | lui (rd : Reg) (imm : BitVec 20)
  | auipc (rd : Reg) (imm : BitVec 20)
  /-- Bit 0 of `imm` is always 0. -/
  | jal (rd : Reg) (imm : BitVec 21)
  | jalr (rd rs1 : Reg) (imm : BitVec 12)
  /-- Bit 0 of `imm` is always 0. -/
  | branch (c : BranchCond) (rs1 rs2 : Reg) (imm : BitVec 13)
  | load (sz : MSize) (signed : Bool) (rd rs1 : Reg) (imm : BitVec 12)
  /-- `mem[rs1 + imm] := rs2`. -/
  | store (sz : MSize) (rs1 rs2 : Reg) (imm : BitVec 12)
  /-- `addi/slti/sltiu/xori/ori/andi`; never `sub` or a shift. -/
  | opImm (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12)
  /-- `slli/srli/srai`. -/
  | shiftImm (op : AluOp) (rd rs1 : Reg) (shamt : BitVec 6)
  | op (op : AluOp) (rd rs1 rs2 : Reg)
  /-- `addiw`. -/
  | opImm32 (rd rs1 : Reg) (imm : BitVec 12)
  /-- `slliw/srliw/sraiw`. -/
  | shiftImm32 (op : AluOp) (rd rs1 : Reg) (shamt : BitVec 5)
  /-- `addw/subw/sllw/srlw/sraw`. -/
  | op32 (op : AluOp) (rd rs1 rs2 : Reg)
  | fence (fm pred succ : BitVec 4) (rd rs1 : Reg)
  | fenceI (rd rs1 : Reg) (imm : BitVec 12)
  | ecall
  | ebreak
  -- M
  | mul (op : MulOp) (rd rs1 rs2 : Reg)
  /-- `mulw/divw/divuw/remw/remuw`. -/
  | mul32 (op : MulOp) (rd rs1 rs2 : Reg)
  -- A
  | lr (width : AWidth) (aq rl : Bool) (rd rs1 : Reg)
  | sc (width : AWidth) (aq rl : Bool) (rd rs1 rs2 : Reg)
  | amo (op : AmoOp) (width : AWidth) (aq rl : Bool) (rd rs1 rs2 : Reg)
  -- Zicsr
  | csr (op : CsrOp) (rd rs1 : Reg) (csr : BitVec 12)
  | csrI (op : CsrOp) (rd : Reg) (uimm : BitVec 5) (csr : BitVec 12)
  -- F/D loads and stores (`rd`/`rs2` name FP registers)
  | fLoad (fmt : FFmt) (rd rs1 : Reg) (imm : BitVec 12)
  | fStore (fmt : FFmt) (rs1 rs2 : Reg) (imm : BitVec 12)
  -- F/D computation
  | fma (op : FmaOp) (fmt : FFmt) (rd rs1 rs2 rs3 : Reg) (rm : BitVec 3)
  | fAri (op : FAriOp) (fmt : FFmt) (rd rs1 rs2 : Reg) (rm : BitVec 3)
  | fSqrt (fmt : FFmt) (rd rs1 : Reg) (rm : BitVec 3)
  | fSgnj (op : FSgnOp) (fmt : FFmt) (rd rs1 rs2 : Reg)
  | fMinMax (op : FMinMaxOp) (fmt : FFmt) (rd rs1 rs2 : Reg)
  | fCmp (op : FCmpOp) (fmt : FFmt) (rd rs1 rs2 : Reg)
  | fCvt (dst src : FCvtTy) (rd rs1 : Reg) (rm : BitVec 3)
  | fMv (dir : FMvDir) (fmt : FFmt) (rd rs1 : Reg)
  | fClass (fmt : FFmt) (rd rs1 : Reg)
  deriving DecidableEq, Repr

/-- Access size in bytes (`msize_bytes`). -/
def MSize.bytes : MSize → Int
  | .sz1 => 1
  | .sz2 => 2
  | .sz4 => 4
  | .sz8 => 8

end Silmaril.RiscV.LPS
