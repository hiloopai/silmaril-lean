module

public import Silmaril.RiscV.LPS.Instr

/-!
# LPS 32-bit decoder (RV64IMAFD_Zicsr_Zifencei)

Hand translation of `theories/Riscv/Decode.v` (LPS commit `f1006fe8`, MIT).

`decode w = none` means "not a valid 32-bit instruction". Upstream aims to match binutils
`objdump` byte for byte, and keeps its policy notes inline; they are kept here. Immediates
are kept at their encoded width with the sign bit included: no sign extension happens here.
Field values are compared as natural numbers (`BitVec.toNat`), where upstream compares
`bv_unsigned` integers.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

section fields

variable (w : BitVec 32)

/-- `f_rd` (Decode.v). -/
def fRd : Reg := bits 7 5 w
/-- `f_rs1` (Decode.v). -/
def fRs1 : Reg := bits 15 5 w
/-- `f_rs2` (Decode.v). -/
def fRs2 : Reg := bits 20 5 w
/-- `f_rs3` (Decode.v). -/
def fRs3 : Reg := bits 27 5 w

/-- `imm_i` (Decode.v). -/
def immI : BitVec 12 := bits 20 12 w
/-- `imm_s` (Decode.v). -/
def immS : BitVec 12 := bits 25 7 w ++ bits 7 5 w
/-- `imm_b` (Decode.v). -/
def immB : BitVec 13 :=
  bits 31 1 w ++ (bits 7 1 w ++ (bits 25 6 w ++ (bits 8 4 w ++ (0 : BitVec 1))))
/-- `imm_u` (Decode.v). -/
def immU : BitVec 20 := bits 12 20 w
/-- `imm_j` (Decode.v). -/
def immJ : BitVec 21 :=
  bits 31 1 w ++ (bits 12 8 w ++ (bits 20 1 w ++ (bits 21 10 w ++ (0 : BitVec 1))))

end fields

/-- The 32-bit decoder (`decode`, Decode.v). -/
def decode (w : BitVec 32) : Option Instr :=
  let opc := (bits 0 7 w).toNat
  let rd := fRd w
  let f3 := (bits 12 3 w).toNat
  let rs1 := fRs1 w
  let rs2 := fRs2 w
  let f7 := (bits 25 7 w).toNat
  let rm : BitVec 3 := bits 12 3 w
  match opc with
  -- Words whose low two bits are not 11 fall through to `none` below, as do the
  -- 48-bit-and-up prefixes (bits[4:2] = 111).
  | 0x37 => some (.lui rd (immU w))
  | 0x17 => some (.auipc rd (immU w))
  | 0x6F => some (.jal rd (immJ w))
  | 0x67 => if f3 = 0 then some (.jalr rd rs1 (immI w)) else none
  | 0x63 => -- BRANCH
    let br c := some (Instr.branch c rs1 rs2 (immB w))
    match f3 with
    | 0 => br .eq | 1 => br .ne
    | 4 => br .lt | 5 => br .ge
    | 6 => br .ltu | 7 => br .geu
    | _ => none
  | 0x03 => -- LOAD; funct3 = 7 (an "ldu") does not exist
    let ld sz sg := some (Instr.load sz sg rd rs1 (immI w))
    match f3 with
    | 0 => ld .sz1 true | 1 => ld .sz2 true
    | 2 => ld .sz4 true | 3 => ld .sz8 true
    | 4 => ld .sz1 false | 5 => ld .sz2 false | 6 => ld .sz4 false
    | _ => none
  | 0x23 => -- STORE
    let st sz := some (Instr.store sz rs1 rs2 (immS w))
    match f3 with
    | 0 => st .sz1 | 1 => st .sz2 | 2 => st .sz4 | 3 => st .sz8
    | _ => none
  | 0x13 => -- OP-IMM; RV64 shifts have a 6-bit shamt (bit 25 may be set)
    let oi op := some (Instr.opImm op rd rs1 (immI w))
    let sh := bits 20 6 w
    match f3 with
    | 0 => oi .add | 2 => oi .slt | 3 => oi .sltu
    | 4 => oi .xor | 6 => oi .or | 7 => oi .and
    | 1 => -- slli: bits[31:26] must be 000000
      if (bits 26 6 w).toNat = 0 then some (.shiftImm .sll rd rs1 sh) else none
    | 5 =>
      match (bits 26 6 w).toNat with
      | 0x00 => some (.shiftImm .srl rd rs1 sh)
      | 0x10 => some (.shiftImm .sra rd rs1 sh)
      | _ => none
    | _ => none
  | 0x1B => -- OP-IMM-32; 5-bit shamt, bit 25 must be 0 (checked via funct7)
    let sh5 := bits 20 5 w
    match f3 with
    | 0 => some (.opImm32 rd rs1 (immI w))
    | 1 => if f7 = 0 then some (.shiftImm32 .sll rd rs1 sh5) else none
    | 5 =>
      match f7 with
      | 0x00 => some (.shiftImm32 .srl rd rs1 sh5)
      | 0x20 => some (.shiftImm32 .sra rd rs1 sh5)
      | _ => none
    | _ => none
  | 0x33 => -- OP: funct7 checked exactly (0x00 / 0x20 / 0x01 = M)
    let op o := some (Instr.op o rd rs1 rs2)
    let ml o := some (Instr.mul o rd rs1 rs2)
    match f7, f3 with
    | 0x00, 0 => op .add | 0x20, 0 => op .sub
    | 0x00, 1 => op .sll
    | 0x00, 2 => op .slt | 0x00, 3 => op .sltu
    | 0x00, 4 => op .xor
    | 0x00, 5 => op .srl | 0x20, 5 => op .sra
    | 0x00, 6 => op .or | 0x00, 7 => op .and
    | 0x01, 0 => ml .mul | 0x01, 1 => ml .mulh
    | 0x01, 2 => ml .mulhsu | 0x01, 3 => ml .mulhu
    | 0x01, 4 => ml .div | 0x01, 5 => ml .divu
    | 0x01, 6 => ml .rem | 0x01, 7 => ml .remu
    | _, _ => none
  | 0x3B => -- OP-32; the M subset here is only mulw/divw/divuw/remw/remuw
    let op o := some (Instr.op32 o rd rs1 rs2)
    let ml o := some (Instr.mul32 o rd rs1 rs2)
    match f7, f3 with
    | 0x00, 0 => op .add | 0x20, 0 => op .sub
    | 0x00, 1 => op .sll
    | 0x00, 5 => op .srl | 0x20, 5 => op .sra
    | 0x01, 0 => ml .mul
    | 0x01, 4 => ml .div | 0x01, 5 => ml .divu
    | 0x01, 6 => ml .rem | 0x01, 7 => ml .remu
    | _, _ => none
  | 0x0F => -- MISC-MEM. Empirically (binutils 2.4x objdump, rv64):
    -- * fence requires rd = rs1 = 0, and either fm = 0 (any pred/succ, 0 printing as
    --   "unknown") or the exact fm=8, pred=succ=rw combination (printed fence.tso); all
    --   other fm/field combinations are rejected.
    -- * fence.i decodes only as the exact word 0x0000100f.
    match f3 with
    | 0 =>
      if rd.toNat = 0 ∧ rs1.toNat = 0 ∧
          ((bits 28 4 w).toNat = 0 ∨ (bits 20 12 w).toNat = 0x833) then
        some (.fence (bits 28 4 w) (bits 24 4 w) (bits 20 4 w) rd rs1)
      else none
    | 1 => if w.toNat = 0x0000100F then some (.fenceI rd rs1 (immI w)) else none
    | _ => none
  | 0x73 => -- SYSTEM
    match f3 with
    | 0 =>
      -- Only ecall/ebreak; privileged instructions are out of scope and return `none`.
      -- POLICY (upstream, confirmed): binutils objdump for plain rv64 DOES print
      -- mret/wfi/sfence.vma etc.
      match w.toNat with
      | 0x00000073 => some .ecall
      | 0x00100073 => some .ebreak
      | _ => none
    | 1 => some (.csr .rw rd rs1 (bits 20 12 w))
    | 2 => some (.csr .rs rd rs1 (bits 20 12 w))
    | 3 => some (.csr .rc rd rs1 (bits 20 12 w))
    | 5 => some (.csrI .rw rd rs1 (bits 20 12 w))
    | 6 => some (.csrI .rs rd rs1 (bits 20 12 w))
    | 7 => some (.csrI .rc rd rs1 (bits 20 12 w))
    | _ => none -- funct3 = 4
  | 0x2F => -- AMO
    let aq := bit 26 w
    let rl := bit 25 w
    let go aw :=
      let am o := some (Instr.amo o aw aq rl rd rs1 rs2)
      match (bits 27 5 w).toNat with
      | 0x00 => am .add
      | 0x01 => am .swap
      | 0x02 => -- lr: rs2 must be 0 (binutils rejects rs2 ≠ 0)
        if rs2.toNat = 0 then some (.lr aw aq rl rd rs1) else none
      | 0x03 => some (.sc aw aq rl rd rs1 rs2)
      | 0x04 => am .xor
      | 0x08 => am .or
      | 0x0C => am .and
      | 0x10 => am .min
      | 0x14 => am .max
      | 0x18 => am .minu
      | 0x1C => am .maxu
      | _ => none
    match f3 with
    | 2 => go .w
    | 3 => go .d
    | _ => none
  | 0x07 => -- LOAD-FP: flw/fld only
    match f3 with
    | 2 => some (.fLoad .s rd rs1 (immI w))
    | 3 => some (.fLoad .d rd rs1 (immI w))
    | _ => none
  | 0x27 => -- STORE-FP
    match f3 with
    | 2 => some (.fStore .s rs1 rs2 (immS w))
    | 3 => some (.fStore .d rs1 rs2 (immS w))
    | _ => none
  | 0x43 | 0x47 | 0x4B | 0x4F => -- FMA group; fmt = bits[26:25]
    let mo : FmaOp :=
      match opc with
      | 0x43 => .madd | 0x47 => .msub
      | 0x4B => .nmsub | _ => .nmadd
    -- POLICY (upstream): rm kept raw; the reserved rm values 5/6 still decode here.
    match (bits 25 2 w).toNat with
    | 0 => some (.fma mo .s rd rs1 rs2 (fRs3 w) rm)
    | 1 => some (.fma mo .d rd rs1 rs2 (fRs3 w) rm)
    | _ => none -- fmt 10/11 illegal (no Q/H)
  | 0x53 => -- OP-FP: funct7 dispatch. rm kept raw for arith/sqrt/cvt
    -- (POLICY: reserved rm values 5/6 accepted).
    let cvtInt : Option FCvtTy := -- integer fcvt_ty selected by the rs2 field
      match rs2.toNat with
      | 0 => some .w | 1 => some .wu
      | 2 => some .l | 3 => some .lu
      | _ => none
    match f7 with
    | 0x00 => some (.fAri .add .s rd rs1 rs2 rm)
    | 0x01 => some (.fAri .add .d rd rs1 rs2 rm)
    | 0x04 => some (.fAri .sub .s rd rs1 rs2 rm)
    | 0x05 => some (.fAri .sub .d rd rs1 rs2 rm)
    | 0x08 => some (.fAri .mul .s rd rs1 rs2 rm)
    | 0x09 => some (.fAri .mul .d rd rs1 rs2 rm)
    | 0x0C => some (.fAri .div .s rd rs1 rs2 rm)
    | 0x0D => some (.fAri .div .d rd rs1 rs2 rm)
    | 0x2C => if rs2.toNat = 0 then some (.fSqrt .s rd rs1 rm) else none
    | 0x2D => if rs2.toNat = 0 then some (.fSqrt .d rd rs1 rm) else none
    | 0x10 | 0x11 =>
      let fmt : FFmt := if f7 = 0x10 then .s else .d
      match f3 with
      | 0 => some (.fSgnj .sgnj fmt rd rs1 rs2)
      | 1 => some (.fSgnj .sgnjn fmt rd rs1 rs2)
      | 2 => some (.fSgnj .sgnjx fmt rd rs1 rs2)
      | _ => none
    | 0x14 | 0x15 =>
      let fmt : FFmt := if f7 = 0x14 then .s else .d
      match f3 with
      | 0 => some (.fMinMax .min fmt rd rs1 rs2)
      | 1 => some (.fMinMax .max fmt rd rs1 rs2)
      | _ => none
    | 0x50 | 0x51 => -- fcmp: feq/flt/fle = funct3 2/1/0
      let fmt : FFmt := if f7 = 0x50 then .s else .d
      match f3 with
      | 2 => some (.fCmp .eq fmt rd rs1 rs2)
      | 1 => some (.fCmp .lt fmt rd rs1 rs2)
      | 0 => some (.fCmp .le fmt rd rs1 rs2)
      | _ => none
    | 0x60 => -- fcvt.{w,wu,l,lu}.s
      match cvtInt with
      | some dst => some (.fCvt dst .s rd rs1 rm)
      | none => none
    | 0x61 => -- fcvt.{w,wu,l,lu}.d
      match cvtInt with
      | some dst => some (.fCvt dst .d rd rs1 rm)
      | none => none
    | 0x68 => -- fcvt.s.{w,wu,l,lu}
      match cvtInt with
      | some src => some (.fCvt .s src rd rs1 rm)
      | none => none
    | 0x69 => -- fcvt.d.{w,wu,l,lu}. fcvt.d.w/fcvt.d.wu are exact: binutils masks rm to 0
      -- and rejects rm ≠ 0 (upstream: 0xd205c553 is invalid to objdump). fcvt.d.l and
      -- fcvt.d.lu round, so rm is free.
      match cvtInt with
      | some .w | some .wu =>
        if f3 = 0 then
          match cvtInt with
          | some src => some (.fCvt .d src rd rs1 rm)
          | none => none
        else none
      | some src => some (.fCvt .d src rd rs1 rm)
      | none => none
    | 0x20 => -- fcvt.s.d (rs2 = 1); rs2 = 0 would be fcvt.s.s: illegal
      if rs2.toNat = 1 then some (.fCvt .s .d rd rs1 rm) else none
    | 0x21 => -- fcvt.d.s (rs2 = 0); exact, so binutils rejects rm ≠ 0 (0x4205c553)
      if rs2.toNat = 0 ∧ f3 = 0 then some (.fCvt .d .s rd rs1 rm) else none
    | 0x70 => -- fmv.x.w (f3 = 0) / fclass.s (f3 = 1); rs2 must be 0
      if rs2.toNat = 0 then
        match f3 with
        | 0 => some (.fMv .xF .s rd rs1)
        | 1 => some (.fClass .s rd rs1)
        | _ => none
      else none
    | 0x71 => -- fmv.x.d / fclass.d
      if rs2.toNat = 0 then
        match f3 with
        | 0 => some (.fMv .xF .d rd rs1)
        | 1 => some (.fClass .d rd rs1)
        | _ => none
      else none
    | 0x78 => -- fmv.w.x
      if rs2.toNat = 0 ∧ f3 = 0 then some (.fMv .fX .s rd rs1) else none
    | 0x79 => -- fmv.d.x
      if rs2.toNat = 0 ∧ f3 = 0 then some (.fMv .fX .d rd rs1) else none
    | _ => none
  | _ => none

end Silmaril.RiscV.LPS
