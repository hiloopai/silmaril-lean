module

public import Silmaril.RiscV.LPS.Machine
public import Silmaril.Machine.RiscV.Ext.Machine.Defs
/-!
# Embedding Silmaril's extended RV64 syntax into the LPS syntax

`Ext.Instr` (RV64IM integer subset, loads/stores, branches, `JAL`, `JALR`, `EBREAK`; see
`Silmaril.RiscV.Ext.Instr`) is a sub-syntax of the LPS RV64GC syntax `LPS.Instr`. `embed`
is the inclusion. Two encoding conventions differ and are converted here:

* Ext stores branch and `JAL` offsets without their always-zero bit 0 (`half`); LPS keeps
  the encoded-width immediate with bit 0 (`imm`), so `imm = half ++ 0`.
* Ext's `LD` is `LoadOp.ld` with `signed = false` (a full-width load); LPS decodes `ld` as
  `load .sz8 true`. Both extensions are the identity at 64 bits.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

open Silmaril.RiscV

/-- `RiscV.ImmOp` as an LPS ALU operation. -/
def embedImmOp : ImmOp → AluOp
  | .add => .add | .slt => .slt | .sltu => .sltu | .and => .and | .or => .or | .xor => .xor

/-- `RiscV.RegOp` as an LPS ALU operation. -/
def embedRegOp : RegOp → AluOp
  | .add => .add | .sub => .sub | .slt => .slt | .sltu => .sltu | .and => .and | .or => .or
  | .xor => .xor | .sll => .sll | .srl => .srl | .sra => .sra

/-- `RiscV.ShiftOp` as an LPS ALU operation. -/
def embedShiftOp : ShiftOp → AluOp
  | .sll => .sll | .srl => .srl | .sra => .sra

/-- The 21-instruction base fragment. -/
def embedBase : RiscV.Instr → Instr
  | .imm op rd rs1 v => .opImm (embedImmOp op) rd rs1 v
  | .reg op rd rs1 rs2 => .op (embedRegOp op) rd rs1 rs2
  | .shift op rd rs1 amount => .shiftImm (embedShiftOp op) rd rs1 amount
  | .upper .lui rd v => .lui rd v
  | .upper .auipc rd v => .auipc rd v

/-- `Ext.RegWOp` as an LPS ALU operation. -/
def embedRegWOp : Ext.RegWOp → AluOp
  | .add => .add | .sub => .sub | .sll => .sll | .srl => .srl | .sra => .sra

/-- `Ext.MulOp` as an LPS M operation. -/
def embedMulOp : Ext.MulOp → MulOp
  | .mul => .mul | .mulh => .mulh | .mulhsu => .mulhsu | .mulhu => .mulhu | .div => .div
  | .divu => .divu | .rem => .rem | .remu => .remu

/-- `Ext.MulWOp` as an LPS M operation (applied by `mul32`). -/
def embedMulWOp : Ext.MulWOp → MulOp
  | .mulw => .mul | .divw => .div | .divuw => .divu | .remw => .rem | .remuw => .remu

/-- Register-only instructions. -/
def embedCompute : Ext.Compute → Instr
  | .base b => embedBase b
  | .addiw rd rs1 imm => .opImm32 rd rs1 imm
  | .shiftW op rd rs1 amount => .shiftImm32 (embedShiftOp op) rd rs1 amount
  | .regW op rd rs1 rs2 => .op32 (embedRegWOp op) rd rs1 rs2
  | .mulDiv op rd rs1 rs2 => .mul (embedMulOp op) rd rs1 rs2
  | .mulDivW op rd rs1 rs2 => .mul32 (embedMulWOp op) rd rs1 rs2

/-- Load size and signedness, as LPS decodes them. -/
def embedLoadOp : Ext.LoadOp → MSize × Bool
  | .lb => (.sz1, true) | .lh => (.sz2, true) | .lw => (.sz4, true) | .ld => (.sz8, true)
  | .lbu => (.sz1, false) | .lhu => (.sz2, false) | .lwu => (.sz4, false)

/-- Store size. -/
def embedStoreOp : Ext.StoreOp → MSize
  | .sb => .sz1 | .sh => .sz2 | .sw => .sz4 | .sd => .sz8

/-- `Ext.BranchOp` as an LPS branch condition. -/
def embedBranchOp : Ext.BranchOp → BranchCond
  | .eq => .eq | .ne => .ne | .lt => .lt | .ge => .ge | .ltu => .ltu | .geu => .geu

/-- The inclusion of Silmaril's extended syntax into the LPS syntax. -/
def embed : Ext.Instr → Instr
  | .compute c => embedCompute c
  | .load op rd rs1 offset => .load (embedLoadOp op).1 (embedLoadOp op).2 rd rs1 offset
  | .store op rs1 rs2 offset => .store (embedStoreOp op) rs1 rs2 offset
  | .branch op rs1 rs2 half => .branch (embedBranchOp op) rs1 rs2 (half ++ (0 : BitVec 1))
  | .jal rd half => .jal rd (half ++ (0 : BitVec 1))
  | .jalr rd rs1 offset => .jalr rd rs1 offset
  | .ebreak => .ebreak

end Silmaril.RiscV.LPS
