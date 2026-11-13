module

public import Silmaril.X86.Features.Ext.BaseInt.Syntax
public import Silmaril.X86.Ext.Encoding
public import Silmaril.X86.Features.Restrict

/-!
# Baseline integer forms: encoding and decoding

The encoder reuses `X86.Ext`'s raw-instruction layer: `toRaw` builds an
`Ext.Raw` with `Ext.rmRaw` (ModRM operand, REX, SIB, displacement) and
`Raw.bytes` writes it, in the order gcc and gas emit (`64`, then `66`/`F3`,
then REX, then the opcode). The length decoder `parseRaw` is `Ext.parseRaw`
with this lane's opcode table `shape`; it reuses `Ext.pHead`, `Ext.pModrm` and
`Ext.pImm` and their round-trip lemmas.

`decoder` is the canonical decoder (`canonicalDecoder`): it accepts exactly
the byte strings that begin with `encode i` for some `i`, the same policy as
`Ext.decode` (redundant prefixes, non-minimal displacements and other
non-preferred spellings are rejected, which is sound: rejected bytes stay
outside the model).

## Disjointness from the integer decoder

`ext_decode_encode_append`: `Ext.decode` rejects every encoding of the lane,
whatever follows it. All forms but `81 /2`, `81 /3`, `83 /2` and `83 /3` have an
opcode outside `Ext.shape`, so `Ext.parseRaw` already rejects them; those four
parse, and `Ext.ofRaw` gives them no meaning (`AluOp.ofDigit` has no ADC or
SBB). `ext_decode_none` restates it for every byte string this decoder accepts,
which is what `step_of_ext` needs.
-/

-- Ported from legacy hiloopai/silmaril; its proofs predate the current unused-tactic linter.
set_option linter.unusedTactic false

@[expose] public section

namespace Silmaril.X86.Features.BaseInt

open Silmaril.X86 (Reg Byte)
open Silmaril.X86.Ext (Sz RM Mem Raw Pfx Opc Rex Imm ImmKind Shape ModrmPart ModrmOk OpcOk
  rmRaw plainRaw encodeRM decodeRM mkReg hiBit mkRex ByteParser PResult)
open Silmaril.X86.Ext.ByteParser

/-! ## Opcode fields -/

namespace Op

def digit : Op → BitVec 3
  | .add => 0 | .or => 1 | .adc => 2 | .sbb => 3 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7

def ofDigit (d : BitVec 3) : Op :=
  if d = 0 then .add else if d = 1 then .or else if d = 2 then .adc else if d = 3 then .sbb
  else if d = 4 then .and else if d = 5 then .sub else if d = 6 then .xor else .cmp

@[simp] theorem ofDigit_digit (op : Op) : ofDigit op.digit = op := by cases op <;> decide

/-- `op r/m, reg`. -/
def opRM : Op → Byte
  | .add => 0x01 | .or => 0x09 | .adc => 0x11 | .sbb => 0x19
  | .and => 0x21 | .sub => 0x29 | .xor => 0x31 | .cmp => 0x39

/-- `op reg, r/m`. -/
def opR : Op → Byte
  | .add => 0x03 | .or => 0x0B | .adc => 0x13 | .sbb => 0x1B
  | .and => 0x23 | .sub => 0x2B | .xor => 0x33 | .cmp => 0x3B

/-- `op eAX, imm`. -/
def opA : Op → Byte
  | .add => 0x05 | .or => 0x0D | .adc => 0x15 | .sbb => 0x1D
  | .and => 0x25 | .sub => 0x2D | .xor => 0x35 | .cmp => 0x3D

def ofOpRM (b : Byte) : Option Op :=
  if b = 0x01 then some .add else if b = 0x09 then some .or
  else if b = 0x11 then some .adc else if b = 0x19 then some .sbb
  else if b = 0x21 then some .and else if b = 0x29 then some .sub
  else if b = 0x31 then some .xor else if b = 0x39 then some .cmp else none

def ofOpR (b : Byte) : Option Op :=
  if b = 0x03 then some .add else if b = 0x0B then some .or
  else if b = 0x13 then some .adc else if b = 0x1B then some .sbb
  else if b = 0x23 then some .and else if b = 0x2B then some .sub
  else if b = 0x33 then some .xor else if b = 0x3B then some .cmp else none

def ofOpA (b : Byte) : Option Op :=
  if b = 0x05 then some .add else if b = 0x0D then some .or
  else if b = 0x15 then some .adc else if b = 0x1D then some .sbb
  else if b = 0x25 then some .and else if b = 0x2D then some .sub
  else if b = 0x35 then some .xor else if b = 0x3D then some .cmp else none

@[simp] theorem ofOpRM_opRM (op : Op) : ofOpRM op.opRM = some op := by cases op <;> decide
@[simp] theorem ofOpR_opR (op : Op) : ofOpR op.opR = some op := by cases op <;> decide
@[simp] theorem ofOpA_opA (op : Op) : ofOpA op.opA = some op := by cases op <;> decide
@[simp] theorem ofOpRM_opR (op : Op) : ofOpRM op.opR = none := by cases op <;> decide

/-- ADC and SBB among the eight operations. -/
def toCarry? : Op → Option CarryOp
  | .adc => some .adc | .sbb => some .sbb | _ => none

end Op

@[simp] theorem CarryOp.toCarry?_toOp (op : CarryOp) : op.toOp.toCarry? = some op := by
  cases op <;> rfl

namespace BtOp

def digit : BtOp → BitVec 3
  | .bt => 4 | .bts => 5 | .btr => 6 | .btc => 7

def ofDigit (d : BitVec 3) : Option BtOp :=
  if d = 4 then some .bt else if d = 5 then some .bts
  else if d = 6 then some .btr else if d = 7 then some .btc else none

/-- The register-offset opcode `0F xx`. -/
def opcode : BtOp → Byte
  | .bt => 0xA3 | .bts => 0xAB | .btr => 0xB3 | .btc => 0xBB

def ofOpcode (b : Byte) : Option BtOp :=
  if b = 0xA3 then some .bt else if b = 0xAB then some .bts
  else if b = 0xB3 then some .btr else if b = 0xBB then some .btc else none

@[simp] theorem ofDigit_digit (op : BtOp) : ofDigit op.digit = some op := by cases op <;> decide
@[simp] theorem ofOpcode_opcode (op : BtOp) : ofOpcode op.opcode = some op := by
  cases op <;> decide

end BtOp

namespace Width

/-- The legacy prefix selecting the size. -/
def pfx : Width → Pfx
  | .w => .opsize | _ => .none

/-- REX.W. -/
def rexW : Width → Bool
  | .q => true | _ => false

/-- The size selected by the prefix and REX.W (REX.W wins). -/
def ofFields (pfx : Pfx) (w : Bool) : Width :=
  if w then .q else if pfx = .opsize then .w else .d

@[simp] theorem ofFields_pfx_rexW (sz : Width) : ofFields sz.pfx sz.rexW = sz := by
  cases sz <;> decide

end Width

/-- The SHLD/SHRD opcode. -/
def shdOpcode (left : Bool) : ShdCount → Byte
  | .imm _ => if left then 0xA4 else 0xAC
  | .cl => if left then 0xA5 else 0xAD

def ShdCount.immField : ShdCount → Imm
  | .imm n => .i8 n
  | .cl => .none

/-! ## Raw fields -/

/-- A form without ModRM, with a legacy prefix. -/
def accRaw (pfx : Pfx) (w : Bool) (opc : Opc) (imm : Imm) : Raw :=
  ⟨false, pfx, mkRex w false false false false, opc, none, imm⟩

/-- The raw fields of an ALU form. -/
def formRaw {k : Nat} (pfx : Pfx) (w : Bool) (op : Op) (imm : BitVec k → Imm) :
    AluForm k → Raw
  | .rm dst src => rmRaw pfx w (.one op.opRM) src.lo (hiBit src) dst false .none
  | .r dst src => rmRaw pfx w (.one op.opR) dst.lo (hiBit dst) src false .none
  | .i dst v => rmRaw pfx w (.one 0x81) op.digit false dst false (imm v)
  | .i8 dst v => rmRaw pfx w (.one 0x83) op.digit false dst false (.i8 v)
  | .a v => accRaw pfx w (.one op.opA) (imm v)

def toRaw : Instr → Raw
  | .carry sz op form => formRaw .none sz.w op.toOp .i32 form
  | .alu16 op form => formRaw .opsize false op .i16 form
  | .shd sz left dst src count =>
    rmRaw sz.pfx sz.rexW (.two (shdOpcode left count)) src.lo (hiBit src) dst false count.immField
  | .bit sz op dst (.reg r) => rmRaw sz.pfx sz.rexW (.two op.opcode) r.lo (hiBit r) dst false .none
  | .bit sz op dst (.imm n) => rmRaw sz.pfx sz.rexW (.two 0xBA) op.digit false dst false (.i8 n)
  | .pushI v => accRaw .none false (.one 0x68) (.i32 v)
  | .pushI8 v => accRaw .none false (.one 0x6A) (.i8 v)
  | .repRet => accRaw .rep false (.one 0xC3) .none

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-! ## Length decoder -/

/-- The opcode table of the lane: whether a ModRM byte follows, and the
immediate. -/
def shape (pfx : Pfx) : Opc → Option Shape
  | .one b =>
    match pfx with
    | .rep => if b = 0xC3 then some ⟨false, .none⟩ else none
    | .nopPad _ => none
    | _ =>
      let full : ImmKind := if pfx = .opsize then .i16 else .i32
      if (Op.ofOpRM b).isSome ∨ (Op.ofOpR b).isSome then some ⟨true, .none⟩
      else if b = 0x81 then some ⟨true, full⟩
      else if b = 0x83 then some ⟨true, .i8⟩
      else if (Op.ofOpA b).isSome then some ⟨false, full⟩
      else if b = 0x68 then some ⟨false, .i32⟩
      else if b = 0x6A then some ⟨false, .i8⟩
      else none
  | .two b =>
    match pfx with
    | .none | .opsize =>
      if b = 0xA4 ∨ b = 0xAC ∨ b = 0xBA then some ⟨true, .i8⟩
      else if (BtOp.ofOpcode b).isSome ∨ b = 0xA5 ∨ b = 0xAD then some ⟨true, .none⟩
      else none
    | _ => none

def parseRaw : ByteParser Raw :=
  bind Ext.pHead fun h =>
  match shape h.2.1 h.2.2.2 with
  | none => fail
  | some sh =>
    bind (Ext.pModrm sh.modrm) fun mp =>
      map (fun imm => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, mp, imm⟩) (Ext.pImm sh.imm)

/-- The fields are consistent with the lane's `shape`. -/
def WF (r : Raw) : Prop :=
  OpcOk r.opc ∧ ∃ sh, shape r.pfx r.opc = some sh ∧ ModrmOk sh.modrm r.modrm ∧ r.imm.kind = sh.imm

theorem parseRaw_bytes {r : Raw} (h : WF r) (rest : List Byte) :
    parseRaw (r.bytes ++ rest) = .ok r rest := by
  obtain ⟨hopc, sh, hsh, hm, hi⟩ := h
  simp only [parseRaw, Raw.bytes, List.append_assoc]
  have head := Ext.pHead_bytes r.fs r.pfx r.rex hopc (Ext.modrmBytes r.modrm ++ (r.imm.bytes ++ rest))
  simp only [List.append_assoc] at head
  rw [bind_ok head]
  simp only [hsh]
  rw [bind_ok (Ext.pModrm_bytes hm _), ← hi, map_ok (Ext.pImm_bytes _ _)]

/-! ## Meaning of raw fields -/

/-- Forms with a ModRM byte. -/
def ofModrm (pfx : Pfx) (w rHi : Bool) (opc : Opc) (reg : BitVec 3) (op : RM) (imm : Imm) :
    Option Instr :=
  match opc with
  | .one b =>
    if pfx = .none then
      if b = 0x81 then
        match (Op.ofDigit reg).toCarry?, imm with
        | some c, .i32 v => some (.carry (Sz.ofW w) c (.i op v))
        | _, _ => none
      else if b = 0x83 then
        match (Op.ofDigit reg).toCarry?, imm with
        | some c, .i8 v => some (.carry (Sz.ofW w) c (.i8 op v))
        | _, _ => none
      else
        match (Op.ofOpRM b).bind Op.toCarry? with
        | some c => some (.carry (Sz.ofW w) c (.rm op (mkReg rHi reg)))
        | none => ((Op.ofOpR b).bind Op.toCarry?).map fun c =>
            .carry (Sz.ofW w) c (.r (mkReg rHi reg) op)
    else if pfx = .opsize ∧ w = false then
      if b = 0x81 then
        match imm with
        | .i16 v => some (.alu16 (Op.ofDigit reg) (.i op v))
        | _ => none
      else if b = 0x83 then
        match imm with
        | .i8 v => some (.alu16 (Op.ofDigit reg) (.i8 op v))
        | _ => none
      else
        match Op.ofOpRM b with
        | some o => some (.alu16 o (.rm op (mkReg rHi reg)))
        | none => (Op.ofOpR b).map fun o => .alu16 o (.r (mkReg rHi reg) op)
    else none
  | .two b =>
    if pfx = .none ∨ pfx = .opsize then
      let sz := Width.ofFields pfx w
      if b = 0xA4 then
        match imm with
        | .i8 n => some (.shd sz true op (mkReg rHi reg) (.imm n))
        | _ => none
      else if b = 0xA5 then some (.shd sz true op (mkReg rHi reg) .cl)
      else if b = 0xAC then
        match imm with
        | .i8 n => some (.shd sz false op (mkReg rHi reg) (.imm n))
        | _ => none
      else if b = 0xAD then some (.shd sz false op (mkReg rHi reg) .cl)
      else if b = 0xBA then
        match BtOp.ofDigit reg, imm with
        | some o, .i8 n => some (.bit sz o op (.imm n))
        | _, _ => none
      else (BtOp.ofOpcode b).map fun o => .bit sz o op (.reg (mkReg rHi reg))
    else none

/-- Forms without a ModRM byte. -/
def ofPlain (pfx : Pfx) (w : Bool) (opc : Opc) (imm : Imm) : Option Instr :=
  match opc, imm with
  | .one b, .i32 v =>
    if pfx = .none then
      if b = 0x68 then some (.pushI v)
      else ((Op.ofOpA b).bind Op.toCarry?).map fun c => .carry (Sz.ofW w) c (.a v)
    else none
  | .one b, .i16 v =>
    if pfx = .opsize ∧ w = false then (Op.ofOpA b).map fun o => .alu16 o (.a v) else none
  | .one b, .i8 v => if pfx = .none ∧ b = 0x6A then some (.pushI8 v) else none
  | .one b, .none => if pfx = .rep ∧ b = 0xC3 then some .repRet else none
  | _, _ => none

def ofRaw (r : Raw) : Option Instr :=
  match r.modrm with
  | some (m, sib, d) =>
    ofModrm r.pfx (r.rex.getD Rex.zero).w (r.rex.getD Rex.zero).r r.opc m.reg
      (decodeRM r.fs (r.rex.getD Rex.zero).x (r.rex.getD Rex.zero).b m sib d) r.imm
  | none => ofPlain r.pfx (r.rex.getD Rex.zero).w r.opc r.imm

theorem ofRaw_rmRaw (pfx : Pfx) (w : Bool) (opc : Opc) (reg : BitVec 3) (rHi : Bool) (op : RM)
    (force : Bool) (imm : Imm) :
    ofRaw (rmRaw pfx w opc reg rHi op force imm) = ofModrm pfx w rHi opc reg op imm := by
  simp only [ofRaw, rmRaw, Ext.mkRex_getD]
  rw [Ext.decodeRM_encodeRM]

theorem ofRaw_accRaw (pfx : Pfx) (w : Bool) (opc : Opc) (imm : Imm) :
    ofRaw (accRaw pfx w opc imm) = ofPlain pfx w opc imm := by
  simp [ofRaw, accRaw]

theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  cases i with
  | carry sz op form =>
    cases form <;> cases op <;>
      simp [toRaw, formRaw, ofRaw_rmRaw, ofRaw_accRaw, ofModrm, ofPlain, CarryOp.toOp, Op.opRM,
        Op.opR, Op.opA, Op.digit, Op.ofOpRM, Op.ofOpR, Op.ofOpA, Op.ofDigit, Op.toCarry?]
  | alu16 op form =>
    cases form <;> cases op <;>
      simp [toRaw, formRaw, ofRaw_rmRaw, ofRaw_accRaw, ofModrm, ofPlain, Op.opRM, Op.opR,
        Op.opA, Op.digit, Op.ofOpRM, Op.ofOpR, Op.ofOpA, Op.ofDigit]
  | shd sz left dst src count =>
    cases left <;> cases count <;> cases sz <;>
      simp [toRaw, ofRaw_rmRaw, ofModrm, shdOpcode, ShdCount.immField, Width.pfx, Width.rexW,
        Width.ofFields]
  | bit sz op dst src =>
    cases src <;> cases op <;> cases sz <;>
      simp [toRaw, ofRaw_rmRaw, ofModrm, BtOp.opcode, BtOp.ofOpcode, BtOp.digit, BtOp.ofDigit,
        Width.pfx, Width.rexW, Width.ofFields]
  | pushI v => simp [toRaw, ofRaw_accRaw, ofPlain]
  | pushI8 v => simp [toRaw, ofRaw_accRaw, ofPlain]
  | repRet => simp [toRaw, ofRaw_accRaw, ofPlain]

theorem wf_rmRaw {pfx : Pfx} {w : Bool} {opc : Opc} {reg : BitVec 3} {rHi : Bool} {op : RM}
    {force : Bool} {imm : Imm} (hopc : OpcOk opc) (h : shape pfx opc = some ⟨true, imm.kind⟩) :
    WF (rmRaw pfx w opc reg rHi op force imm) :=
  ⟨hopc, ⟨true, imm.kind⟩, h, Ext.encodeRM_ok op reg, rfl⟩

theorem wf_accRaw {pfx : Pfx} {w : Bool} {opc : Opc} {imm : Imm} (hopc : OpcOk opc)
    (h : shape pfx opc = some ⟨false, imm.kind⟩) : WF (accRaw pfx w opc imm) :=
  ⟨hopc, ⟨false, imm.kind⟩, h, trivial, rfl⟩

set_option linter.unnecessarySeqFocus false in
theorem wf_toRaw (i : Instr) : WF (toRaw i) := by
  cases i with
  | carry sz op form =>
    cases form <;> cases op <;> simp only [toRaw, formRaw, CarryOp.toOp] <;>
      first
      | (apply wf_rmRaw <;> simp only [OpcOk, Imm.kind] <;> decide)
      | (apply wf_accRaw <;> simp only [OpcOk, Imm.kind] <;> decide)
  | alu16 op form =>
    cases form <;> cases op <;> simp only [toRaw, formRaw] <;>
      first
      | (apply wf_rmRaw <;> simp only [OpcOk, Imm.kind] <;> decide)
      | (apply wf_accRaw <;> simp only [OpcOk, Imm.kind] <;> decide)
  | shd sz left dst src count =>
    cases left <;> cases count <;> cases sz <;>
      (apply wf_rmRaw <;> (try simp only [OpcOk, Imm.kind, ShdCount.immField, shdOpcode]);
        all_goals decide)
  | bit sz op dst src =>
    cases src <;> cases op <;> cases sz <;>
      (apply wf_rmRaw <;> (try simp only [OpcOk, Imm.kind]); all_goals decide)
  | pushI v => apply wf_accRaw <;> simp only [OpcOk, Imm.kind] <;> decide
  | pushI8 v => apply wf_accRaw <;> simp only [OpcOk, Imm.kind] <;> decide
  | repRet => apply wf_accRaw <;> simp only [OpcOk, Imm.kind] <;> decide

/-! ## Decoder -/

/-- Parse the raw fields and give them a meaning. -/
def parse (bytes : List Byte) : Option Instr :=
  match parseRaw bytes with
  | .ok r _ => ofRaw r
  | _ => none

theorem parse_encode_append (i : Instr) (rest : List Byte) : parse (encode i ++ rest) = some i := by
  simp [parse, encode, parseRaw_bytes (wf_toRaw i), ofRaw_toRaw]

theorem Raw.bytes_ne_nil (r : Raw) : r.bytes ≠ [] := by
  cases h : r.opc <;> simp [Raw.bytes, h, Opc.bytes]

theorem encode_ne_nil (i : Instr) : encode i ≠ [] := Raw.bytes_ne_nil _

/-- The canonical decoder of the lane. -/
def decoder : Machine.Decoder Instr :=
  canonicalDecoder parse encode parse_encode_append encode_ne_nil

def decode : List Byte → Option (Instr × Nat) := decoder.decode

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes :=
  canonicalDecoder_decode_iff parse_encode_append encode_ne_nil

/-! ## The integer decoder rejects the lane -/

theorem opcOk_one {b : Byte}
    (h : (b != 0x66#8 && b != 0xF3#8 && b != 0x2E#8 && b != 0x64#8 && b != 0x0F#8 &&
      !Ext.isRex b) = true) : OpcOk (.one b) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ext_decode_of_shape_none {r : Raw} (hopc : OpcOk r.opc)
    (h : Ext.shape r.pfx (r.rex.getD Rex.zero).w r.opc = none) (rest : List Byte) :
    Ext.decode (r.bytes ++ rest) = none := by
  have head := Ext.pHead_bytes r.fs r.pfx r.rex hopc (Ext.modrmBytes r.modrm ++ (r.imm.bytes ++ rest))
  simp only [List.append_assoc] at head
  have : Ext.parseRaw (r.bytes ++ rest) = .bad := by
    simp only [Ext.parseRaw, Raw.bytes, List.append_assoc]
    rw [bind_ok head]
    simp [h]
  simp [Ext.decode, this]

theorem ext_decode_of_ofRaw_none {r : Raw} (hwf : r.WF) (h : Ext.ofRaw r = none)
    (rest : List Byte) : Ext.decode (r.bytes ++ rest) = none := by
  simp [Ext.decode, Ext.parseRaw_bytes hwf, h]

private theorem ext_rm_shape {pfx : Pfx} {w : Bool} {opc : Opc} {reg : BitVec 3} {rHi : Bool}
    {op : RM} {force : Bool} {imm : Imm} (hopc : OpcOk opc) (h : Ext.shape pfx w opc = none)
    (rest : List Byte) : Ext.decode ((rmRaw pfx w opc reg rHi op force imm).bytes ++ rest) = none :=
  ext_decode_of_shape_none hopc (by simpa [rmRaw] using h) rest

private theorem ext_acc_shape {pfx : Pfx} {w : Bool} {opc : Opc} {imm : Imm} (hopc : OpcOk opc)
    (h : Ext.shape pfx w opc = none) (rest : List Byte) :
    Ext.decode ((accRaw pfx w opc imm).bytes ++ rest) = none :=
  ext_decode_of_shape_none hopc (by simpa [accRaw] using h) rest

set_option linter.unnecessarySeqFocus false in
/-- `Ext.decode` rejects every encoding of the lane, whatever follows it. -/
theorem ext_decode_encode_append (i : Instr) (rest : List Byte) :
    Ext.decode (encode i ++ rest) = none := by
  unfold encode
  cases i with
  | carry sz op form =>
    cases form with
    | rm dst src => cases op <;> cases sz <;> exact ext_rm_shape (opcOk_one (by decide)) (by decide) rest
    | r dst src => cases op <;> cases sz <;> exact ext_rm_shape (opcOk_one (by decide)) (by decide) rest
    | a v => cases op <;> cases sz <;> exact ext_acc_shape (opcOk_one (by decide)) (by decide) rest
    | i dst v =>
      apply ext_decode_of_ofRaw_none (Ext.wf_rmRaw (by cases sz <;> simp only [Imm.kind] <;> decide))
      cases op <;> simp [Ext.ofRaw_rmRaw, Ext.ofModrm, Op.digit, CarryOp.toOp,
        X86.AluOp.ofDigit]
    | i8 dst v =>
      apply ext_decode_of_ofRaw_none (Ext.wf_rmRaw (by cases sz <;> simp only [Imm.kind] <;> decide))
      cases op <;> simp [Ext.ofRaw_rmRaw, Ext.ofModrm, Op.digit, CarryOp.toOp,
        X86.AluOp.ofDigit]
  | alu16 op form =>
    cases form <;> cases op <;>
      first
      | exact ext_rm_shape (opcOk_one (by decide)) (by decide) rest
      | exact ext_acc_shape (opcOk_one (by decide)) (by decide) rest
  | shd sz left dst src count =>
    cases left <;> cases count <;> cases sz <;>
      (apply ext_rm_shape <;> (try simp only [OpcOk, shdOpcode]); all_goals decide)
  | bit sz op dst src =>
    cases src <;> cases op <;> cases sz <;>
      (apply ext_rm_shape <;> (try simp only [OpcOk, BtOp.opcode]); all_goals decide)
  | pushI v => exact ext_acc_shape (opcOk_one (by decide)) (by decide) rest
  | pushI8 v => exact ext_acc_shape (opcOk_one (by decide)) (by decide) rest
  | repRet => exact ext_acc_shape (opcOk_one (by decide)) (by decide) rest

/-- Every byte string the lane decodes, the integer decoder rejects. -/
theorem ext_decode_none {bytes : List Byte} {i : Instr} {n : Nat} (h : decode bytes = some (i, n)) :
    Ext.decode bytes = none := by
  obtain ⟨-, rest, rfl⟩ := decode_eq_some_iff.mp h
  exact ext_decode_encode_append i rest

end Silmaril.X86.Features.BaseInt
