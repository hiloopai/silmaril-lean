module

public import Silmaril.X86.Features.Ext.Sse2.Syntax
public import Silmaril.X86.Float.Encoding

/-!
# Byte codec for the SSE/SSE2 integer and move lane

The encoder and decoder reuse `X86.Float`'s field layer (`Silmaril.X86.Raw`:
mandatory prefix, REX, `0F`, opcode, ModRM/SIB/displacement) unchanged. Its
immediate table `hasImm8` does not list this lane's imm8 opcodes (`66 0F 70`,
`71`, `72`, `73`, `C4`, `C5`), so the imm8 is read after the `Raw` by
`parseImm8 (needsImm r)`. The instruction layer follows `X86.Float`: `toRaw`
is the opcode table, `candidate` reads it backwards and `ofRaw` keeps a
candidate only when `toRaw` reproduces every field (canonical encodings only).

* `decode_encode_append`, `decode_sound`, `byteDecoder`: the `Machine.Decoder`
  laws.
* `owned`: the lane's opcode space on `Raw` fields. `owned_toRaw` and
  `not_owned_floatToRaw` show that `X86.Float`'s scalar SSE encodings are
  outside it, which gives `decode_disjoint_float`.
* `ext_decode_encode`: the integer decoder `Ext.decode` rejects every
  encoding of the lane, whatever follows it.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse2

open Silmaril.X86
open Silmaril.X86.Float (XRM GRM IntWidth XRM.toOperand GRM.toOperand)

/-! ## Opcode tables -/

def MovKind.pfx : MovKind → Prefix
  | .dqa => .p66 | .dqu => .pF3 | .aps => .none | .ups => .none | .apd => .p66 | .upd => .p66

def MovKind.loadOpc : MovKind → Byte
  | .dqa | .dqu => 0x6F#8 | .aps | .apd => 0x28#8 | .ups | .upd => 0x10#8

def MovKind.storeOpc : MovKind → Byte
  | .dqa | .dqu => 0x7F#8 | .aps | .apd => 0x29#8 | .ups | .upd => 0x11#8

def Lane.addOpc : Lane → Byte
  | .b => 0xFC#8 | .w => 0xFD#8 | .d => 0xFE#8 | .q => 0xD4#8

def Lane.subOpc : Lane → Byte
  | .b => 0xF8#8 | .w => 0xF9#8 | .d => 0xFA#8 | .q => 0xFB#8

def Lane.unpackLoOpc : Lane → Byte
  | .b => 0x60#8 | .w => 0x61#8 | .d => 0x62#8 | .q => 0x6C#8

def Lane.unpackHiOpc : Lane → Byte
  | .b => 0x68#8 | .w => 0x69#8 | .d => 0x6A#8 | .q => 0x6D#8

/-- The `66 0F xx /r` opcode of each two-operand operation (SDM Vol. 2,
instruction pages; PSRLW `D1`, PSRAW `E1`, PSLLW `F1`, ...). -/
def BinOp.opcode : BinOp → Byte
  | .logic .and => 0xDB#8 | .logic .andn => 0xDF#8 | .logic .or => 0xEB#8
  | .logic .xor => 0xEF#8
  | .add l => l.addOpc
  | .sub l => l.subOpc
  | .cmpeq .b => 0x74#8 | .cmpeq .w => 0x75#8 | .cmpeq .d => 0x76#8
  | .unpackLo l => l.unpackLoOpc
  | .unpackHi l => l.unpackHiOpc
  | .shift .srlw => 0xD1#8 | .shift .srld => 0xD2#8 | .shift .srlq => 0xD3#8
  | .shift .sraw => 0xE1#8 | .shift .srad => 0xE2#8
  | .shift .sllw => 0xF1#8 | .shift .slld => 0xF2#8 | .shift .sllq => 0xF3#8

/-- The operation with a given opcode. -/
def BinOp.ofOpcode (b : Byte) : Option BinOp :=
  match b.toNat with
  | 0xDB => some (.logic .and) | 0xDF => some (.logic .andn) | 0xEB => some (.logic .or)
  | 0xEF => some (.logic .xor)
  | 0xFC => some (.add .b) | 0xFD => some (.add .w) | 0xFE => some (.add .d)
  | 0xD4 => some (.add .q)
  | 0xF8 => some (.sub .b) | 0xF9 => some (.sub .w) | 0xFA => some (.sub .d)
  | 0xFB => some (.sub .q)
  | 0x74 => some (.cmpeq .b) | 0x75 => some (.cmpeq .w) | 0x76 => some (.cmpeq .d)
  | 0x60 => some (.unpackLo .b) | 0x61 => some (.unpackLo .w) | 0x62 => some (.unpackLo .d)
  | 0x6C => some (.unpackLo .q)
  | 0x68 => some (.unpackHi .b) | 0x69 => some (.unpackHi .w) | 0x6A => some (.unpackHi .d)
  | 0x6D => some (.unpackHi .q)
  | 0xD1 => some (.shift .srlw) | 0xD2 => some (.shift .srld) | 0xD3 => some (.shift .srlq)
  | 0xE1 => some (.shift .sraw) | 0xE2 => some (.shift .srad)
  | 0xF1 => some (.shift .sllw) | 0xF2 => some (.shift .slld) | 0xF3 => some (.shift .sllq)
  | _ => none

theorem BinOp.ofOpcode_opcode (op : BinOp) : BinOp.ofOpcode op.opcode = some op := by
  rcases op with (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _) |
    (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl

theorem BinOp.opcode_of_ofOpcode {b : Byte} {op : BinOp} (h : BinOp.ofOpcode b = some op) :
    op.opcode = b := by
  have key : ∀ b : Byte, ∀ op, BinOp.ofOpcode b = some op → op.opcode = b := by decide
  exact key b op h

/-- The imm8 shift group (`66 0F 71/72/73`) and the ModRM `reg` digit of each
shift (SDM Vol. 2B, PSRLW/PSRLD/PSRLQ, PSRAW/PSRAD, PSLLW/PSLLD/PSLLQ). -/
def ShiftKind.immOpc : ShiftKind → Byte
  | .srlw | .sraw | .sllw => 0x71#8
  | .srld | .srad | .slld => 0x72#8
  | .srlq | .sllq => 0x73#8

def ShiftKind.digit : ShiftKind → BitVec 4
  | .srlw | .srld | .srlq => 2#4
  | .sraw | .srad => 4#4
  | .sllw | .slld | .sllq => 6#4

/-- The shift of the imm8 group with this opcode and digit. -/
def ShiftKind.ofImm (opc : Byte) (digit : BitVec 4) : Option ShiftKind :=
  match opc.toNat, digit.toNat with
  | 0x71, 2 => some .srlw | 0x71, 4 => some .sraw | 0x71, 6 => some .sllw
  | 0x72, 2 => some .srld | 0x72, 4 => some .srad | 0x72, 6 => some .slld
  | 0x73, 2 => some .srlq | 0x73, 6 => some .sllq
  | _, _ => none

/-- PSRLDQ is `66 0F 73 /3`, PSLLDQ is `66 0F 73 /7`. -/
def shiftBytesDigit (left : Bool) : BitVec 4 := if left then 7#4 else 3#4

/-- A `0F`-map instruction without an immediate inside the `Raw`. -/
def raw (pfx : Prefix) (w : BitVec 1) (opc : Byte) (reg : BitVec 4) (rm : Operand) : Raw :=
  { pfx, w, map := .m0F, opc, reg, rm, imm := none }

/-- The fields and the trailing imm8 of each instruction (SDM Vol. 2 opcode
lines). Loads and `/r` operations put the destination in ModRM `reg`; stores
(`7F`, `29`, `11`, `7E`, `D6`) put it in ModRM `r/m`. -/
def toRaw : Instr → Raw × Option Byte
  | .movLoad k dst m => (raw k.pfx 0#1 k.loadOpc dst.toBitVec (.mem m), none)
  | .movStore k m src => (raw k.pfx 0#1 k.storeOpc src.toBitVec (.mem m), none)
  | .movRR k dst src =>
    (raw k.toMovKind.pfx 0#1 k.toMovKind.loadOpc dst.toBitVec (.reg src.toBitVec), none)
  | .movRRStore k dst src => (raw k.pfx 0#1 k.storeOpc src.toBitVec (.reg dst.toBitVec), none)
  | .movdLoad w dst m => (raw .p66 w.wBit 0x6E#8 dst.toBitVec (.mem m), none)
  | .movdStore w m src => (raw .p66 w.wBit 0x7E#8 src.toBitVec (.mem m), none)
  | .movqLoad dst src => (raw .pF3 0#1 0x7E#8 dst.toBitVec src.toOperand, none)
  | .movqStore dst src => (raw .p66 0#1 0xD6#8 src.toBitVec dst.toOperand, none)
  | .binop op dst src => (raw .p66 0#1 op.opcode dst.toBitVec src.toOperand, none)
  | .shiftImm k dst imm => (raw .p66 0#1 k.immOpc k.digit (.reg dst.toBitVec), some imm)
  | .shiftBytes left dst imm =>
    (raw .p66 0#1 0x73#8 (shiftBytesDigit left) (.reg dst.toBitVec), some imm)
  | .pshufd dst src imm => (raw .p66 0#1 0x70#8 dst.toBitVec src.toOperand, some imm)
  | .pmovmskb dst src => (raw .p66 0#1 0xD7#8 dst.toBitVec (.reg src.toBitVec), none)
  | .pinsrw dst src imm => (raw .p66 0#1 0xC4#8 dst.toBitVec src.toOperand, some imm)
  | .pextrw dst src imm => (raw .p66 0#1 0xC5#8 dst.toBitVec (.reg src.toBitVec), some imm)

/-- Whether an imm8 follows the `Raw` fields. -/
def needsImm (r : Raw) : Bool :=
  r.map == .m0F && r.pfx == .p66 &&
    (r.opc == 0x70#8 || r.opc == 0x71#8 || r.opc == 0x72#8 || r.opc == 0x73#8 ||
      r.opc == 0xC4#8 || r.opc == 0xC5#8)

/-- The MOVxxx families by prefix and opcode. -/
def movCandidate (k : MovKind) (load : Bool) (r : Raw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match load, r.rm with
  | true, .mem m => some (.movLoad k x m)
  | false, .mem m => some (.movStore k m x)
  | true, .reg n =>
    match k with
    | .dqa => some (.movRR .dqa x (XReg.ofBitVec n))
    | .dqu => some (.movRR .dqu x (XReg.ofBitVec n))
    | .ups => some (.movRR .ups x (XReg.ofBitVec n))
    | .upd => some (.movRR .upd x (XReg.ofBitVec n))
    | .aps | .apd => none
  | false, .reg n => some (.movRRStore k (XReg.ofBitVec n) x)

/-- The `66 0F` table. -/
def p66Candidate (r : Raw) (imm : Option Byte) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match BinOp.ofOpcode r.opc with
  | some op => some (.binop op x r.rm.toXRM)
  | none =>
  match r.opc.toNat with
  | 0x10 => movCandidate .upd true r
  | 0x11 => movCandidate .upd false r
  | 0x28 => movCandidate .apd true r
  | 0x29 => movCandidate .apd false r
  | 0x6F => movCandidate .dqa true r
  | 0x7F => movCandidate .dqa false r
  | 0x6E =>
    match r.rm with
    | .mem m => some (.movdLoad (IntWidth.ofBit r.w) x m)
    | .reg _ => none
  | 0x7E =>
    match r.rm with
    | .mem m => some (.movdStore (IntWidth.ofBit r.w) m x)
    | .reg _ => none
  | 0xD6 => some (.movqStore r.rm.toXRM x)
  | 0xD7 =>
    match r.rm with
    | .reg n => some (.pmovmskb (Reg.ofBitVec r.reg) (XReg.ofBitVec n))
    | .mem _ => none
  | 0x70 => imm.map (.pshufd x r.rm.toXRM)
  | 0x71 | 0x72 =>
    match r.rm, imm with
    | .reg n, some b => (ShiftKind.ofImm r.opc r.reg).map fun k => .shiftImm k (XReg.ofBitVec n) b
    | _, _ => none
  | 0x73 =>
    match r.rm, imm with
    | .reg n, some b =>
      if r.reg = 3#4 then some (.shiftBytes false (XReg.ofBitVec n) b)
      else if r.reg = 7#4 then some (.shiftBytes true (XReg.ofBitVec n) b)
      else (ShiftKind.ofImm r.opc r.reg).map fun k => .shiftImm k (XReg.ofBitVec n) b
    | _, _ => none
  | 0xC4 => imm.map (.pinsrw x r.rm.toGRM)
  | 0xC5 =>
    match r.rm, imm with
    | .reg n, some b => some (.pextrw (Reg.ofBitVec r.reg) (XReg.ofBitVec n) b)
    | _, _ => none
  | _ => none

/-- Read the opcode tables. -/
def candidate (r : Raw) (imm : Option Byte) : Option Instr :=
  match r.map, r.pfx with
  | .m0F, .none =>
    match r.opc.toNat with
    | 0x10 => movCandidate .ups true r
    | 0x11 => movCandidate .ups false r
    | 0x28 => movCandidate .aps true r
    | 0x29 => movCandidate .aps false r
    | _ => none
  | .m0F, .p66 => p66Candidate r imm
  | .m0F, .pF3 =>
    match r.opc.toNat with
    | 0x6F => movCandidate .dqu true r
    | 0x7F => movCandidate .dqu false r
    | 0x7E => some (.movqLoad (XReg.ofBitVec r.reg) r.rm.toXRM)
    | _ => none
  | _, _ => none

/-- The instruction with these fields and immediate, if canonical. -/
def ofRaw (r : Raw) (imm : Option Byte) : Option Instr :=
  match candidate r imm with
  | some i => if toRaw i = (r, imm) then some i else none
  | none => none

theorem candidate_toRaw (i : Instr) : candidate (toRaw i).1 (toRaw i).2 = some i := by
  cases i with
  | binop op dst src =>
    simp only [toRaw, raw, candidate, p66Candidate, BinOp.ofOpcode_opcode, Option.some.injEq,
      Instr.binop.injEq, XReg.ofBitVec_toBitVec, true_and]
    exact Float.XRM.toOperand_toXRM src
  | movLoad k | movStore k | movRRStore k =>
    cases k <;> simp [toRaw, raw, candidate, p66Candidate, movCandidate, MovKind.pfx,
      MovKind.loadOpc, MovKind.storeOpc, BinOp.ofOpcode]
  | movRR k =>
    cases k <;> simp [toRaw, raw, candidate, p66Candidate, movCandidate, MovKind.pfx,
      MovKind.loadOpc, RRKind.toMovKind, BinOp.ofOpcode]
  | shiftImm k =>
    cases k <;> simp [toRaw, raw, candidate, p66Candidate, ShiftKind.immOpc, ShiftKind.digit,
      ShiftKind.ofImm, BinOp.ofOpcode]
  | shiftBytes left => cases left <;> simp [toRaw, raw, candidate, p66Candidate,
      shiftBytesDigit, BinOp.ofOpcode]
  | movqLoad | movqStore | pshufd | pinsrw =>
    simp [toRaw, raw, candidate, p66Candidate, BinOp.ofOpcode]
  | movdLoad | movdStore | pmovmskb | pextrw =>
    simp [toRaw, raw, candidate, p66Candidate, BinOp.ofOpcode]

@[simp] theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i).1 (toRaw i).2 = some i := by
  simp [ofRaw, candidate_toRaw]

theorem toRaw_of_ofRaw {r : Raw} {imm : Option Byte} {i : Instr} (h : ofRaw r imm = some i) :
    toRaw i = (r, imm) := by
  unfold ofRaw at h
  split at h
  · split_ifs at h with heq
    cases h
    exact heq
  · cases h

theorem toRaw_map (i : Instr) : (toRaw i).1.map = .m0F := by
  cases i <;> rfl

theorem toRaw_imm (i : Instr) : (toRaw i).1.imm = none := by
  cases i <;> rfl

/-! ## Opcode space -/

/-- Whether an operand is a memory operand. -/
def isMem : Operand → Bool
  | .mem _ => true
  | .reg _ => false

/-- The prefix/opcode pairs of the lane, ignoring the operand. -/
def ownedHead (pfx : Prefix) (opc : Byte) : Bool :=
  match pfx with
  | .none => [0x10#8, 0x11#8, 0x28#8, 0x29#8].contains opc
  | .p66 =>
    (BinOp.ofOpcode opc).isSome ||
      [0x10#8, 0x11#8, 0x28#8, 0x29#8, 0x6F#8, 0x7F#8, 0x6E#8, 0x7E#8, 0xD6#8, 0xD7#8, 0x70#8,
        0x71#8, 0x72#8, 0x73#8, 0xC4#8, 0xC5#8].contains opc
  | .pF3 => [0x6F#8, 0x7F#8, 0x7E#8].contains opc
  | .pF2 => false

/-- The lane's opcode space: `0F`-map fields with an owned prefix and opcode;
for `0F 28` (no prefix or `66`) and `66 0F 6E/7E`, only memory operands (the
register forms are `floatExt`'s). -/
def owned (r : Raw) : Bool :=
  r.map == .m0F && ownedHead r.pfx r.opc &&
    (if r.opc == 0x28#8 || ((r.opc == 0x6E#8 || r.opc == 0x7E#8) && r.pfx == .p66) then
      isMem r.rm else true)

theorem owned_toRaw (i : Instr) : owned (toRaw i).1 = true := by
  cases i
  case binop op _ _ =>
    rcases op with (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _) |
      (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl
  case movLoad k _ _ | movStore k _ _ | movRRStore k _ _ => cases k <;> rfl
  case movRR k _ _ => cases k <;> rfl
  case shiftImm k _ _ => cases k <;> rfl
  case shiftBytes left _ _ => cases left <;> rfl
  all_goals rfl

theorem ownedHead_safe {pfx : Prefix} {opc : Byte} (h : ownedHead pfx opc = true) :
    opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8 ∧ opc ≠ 0xC2#8 := by
  have h0 : ∀ opc : Byte, ownedHead .none opc = true →
      opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8 ∧ opc ≠ 0xC2#8 := by decide
  have h1 : ∀ opc : Byte, ownedHead .p66 opc = true →
      opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8 ∧ opc ≠ 0xC2#8 := by decide
  have h3 : ∀ opc : Byte, ownedHead .pF3 opc = true →
      opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8 ∧ opc ≠ 0xC2#8 := by decide
  cases pfx
  · exact h0 opc h
  · exact h1 opc h
  · simp [ownedHead] at h
  · exact h3 opc h

theorem toRaw_ownedHead (i : Instr) : ownedHead (toRaw i).1.pfx (toRaw i).1.opc = true := by
  have h := owned_toRaw i
  simp only [owned, Bool.and_eq_true] at h
  exact h.1.2

/-- The opcodes of the `Raw` layer's immediate table are not this lane's. -/
theorem toRaw_wellFormed (i : Instr) : (toRaw i).1.WellFormed := by
  obtain ⟨h38, h3A, hC2⟩ := ownedHead_safe (toRaw_ownedHead i)
  constructor
  · intro _
    exact ⟨h38, h3A⟩
  · rw [toRaw_imm, toRaw_map]
    simp [hasImm8, hC2]

/-- The trailing imm8 is present exactly when `needsImm` says so. -/
theorem toRaw_needsImm (i : Instr) : (toRaw i).2.isSome = needsImm (toRaw i).1 := by
  cases i
  case binop op _ _ =>
    rcases op with (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _) |
      (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl
  case movLoad k _ _ | movStore k _ _ | movRRStore k _ _ => cases k <;> rfl
  case movRR k _ _ => cases k <;> rfl
  case shiftImm k _ _ => cases k <;> rfl
  case shiftBytes left _ _ => cases left <;> rfl
  all_goals rfl

/-! ## Encoder and decoder -/

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).1.bytes ++ (toRaw i).2.toList

/-- Decode one instruction from the start of `bytes`, returning it with the
number of bytes consumed. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Raw.parse bytes with
  | some (r, rest) =>
    match parseImm8 (needsImm r) rest with
    | some (imm, rest') => (ofRaw r imm).map fun i => (i, bytes.length - rest'.length)
    | none => none
  | none => none

@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  unfold decode encode
  rw [List.append_assoc, Raw.parse_bytes _ (toRaw_wellFormed i)]
  simp only
  rw [parseImm8_toList (toRaw_needsImm i)]
  simp; omega

theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ n ≤ bytes.length ∧ bytes = encode i ++ bytes.drop n := by
  unfold decode at h
  split at h
  next r rest hp =>
    split at h
    next imm rest' hi =>
      obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hb : bytes = encode j ++ rest' := by
        rw [Raw.parse_sound hp, parseImm8_sound hi, encode, toRaw_of_ofRaw hj, List.append_assoc]
      have hn : bytes.length - rest'.length = (encode j).length := by
        rw [hb, List.length_append]; omega
      refine ⟨hn, by omega, ?_⟩
      rw [hn, hb, List.drop_left]
    next => cases h
  next => cases h

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, -, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

theorem decode_append {bytes more : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

theorem encode_length_ge (i : Instr) : 3 ≤ (encode i).length := by
  have := Raw.bytes_length_ge (toRaw i).1
  simp only [encode, List.length_append]
  omega

theorem encode_length_le (i : Instr) : (encode i).length ≤ 13 := by
  have := Raw.bytes_length_le (toRaw i).1
  have : (toRaw i).2.toList.length ≤ 1 := by cases (toRaw i).2 <;> simp
  simp only [encode, List.length_append]
  omega

/-- The codec as an instance of the shared decoder contract. -/
def byteDecoder : Machine.Decoder Instr where
  decode := decode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := decode_sound h
    have := encode_length_ge ‹_›
    omega
  decode_length_le h := (decode_sound h).2.1
  decode_append extra h := decode_append h
  decode_take {bytes i n} h := by
    obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
    rw [hn, List.take_left]
    simpa using decode_encode_append _ []
  decode_encode_append := decode_encode_append

/-- `X86.Float`'s scalar SSE encodings are outside the lane. -/
theorem not_owned_floatToRaw (i : Float.Instr) : owned (Float.toRaw i) = false := by
  cases i
  case arith op p _ _ => cases op <;> cases p <;> rfl
  case logic op p _ _ => cases op <;> cases p <;> rfl
  case movs p _ _ | load p _ _ | store p _ _ | movap p _ _ | sqrt p _ _ | cvtPrec p _ _
    | ucomi p _ _ | comi p _ _ | round p _ _ _ | cmp p _ _ _ => cases p <;> rfl
  case cvtFromInt p _ _ _ | cvtToIntTrunc p _ _ _ | cvtToInt p _ _ _ => cases p <;> rfl
  all_goals rfl

/-- No byte string decodes both here and in `X86.Float`. -/
theorem decode_disjoint_float (bytes : List Byte) :
    decode bytes = none ∨ Float.decode bytes = none := by
  cases h1 : decode bytes with
  | none => exact .inl rfl
  | some p =>
    right
    cases h2 : Float.decode bytes with
    | none => rfl
    | some q =>
      exfalso
      unfold decode at h1
      unfold Float.decode at h2
      split at h1
      next r rest hp =>
        rw [hp] at h2
        split at h1
        next imm rest' _ =>
          obtain ⟨j, hj, -⟩ := Option.map_eq_some_iff.mp h1
          obtain ⟨i, hi, -⟩ := Option.map_eq_some_iff.mp h2
          have e1 := congrArg Prod.fst (toRaw_of_ofRaw hj)
          have e2 := Float.toRaw_of_ofRaw hi
          simp only at e1
          have := owned_toRaw j
          rw [e1, ← e2, not_owned_floatToRaw] at this
          cases this
        next => cases h1
      next => cases h1

/-! ## The integer decoder rejects the lane -/

private def isBad {α : Type} : Ext.PResult α → Bool
  | .bad => true
  | _ => false

private theorem isBad_iff {α : Type} {r : Ext.PResult α} : isBad r = true ↔ r = .bad := by
  cases r <;> simp [isBad]

/-- Every owned prefix/opcode pair, under every REX nibble, is rejected by the
integer length decoder as soon as it reads the opcode. -/
private theorem heads_bad :
    ∀ pfx ∈ [Prefix.none, .p66, .pF3], ∀ opc : Byte, ownedHead pfx opc = true →
      ∀ n : BitVec 4, isBad (Ext.parseRaw (pfx.bytes ++ rexBytes n ++ [0x0F#8, opc])) = true := by
  decide +kernel

theorem ownedHead_pfx {pfx : Prefix} {opc : Byte} (h : ownedHead pfx opc = true) :
    pfx ∈ [Prefix.none, .p66, .pF3] := by
  cases pfx <;> simp_all [ownedHead]

/-- `Ext.decode` rejects every encoding of the lane, whatever follows it. -/
theorem ext_decode_encode (i : Instr) (more : List Byte) : Ext.decode (encode i ++ more) = none := by
  have ho := owned_toRaw i
  simp only [owned, Bool.and_eq_true] at ho
  obtain ⟨⟨-, hh⟩, -⟩ := ho
  have hbad := isBad_iff.mp (heads_bad _ (ownedHead_pfx hh) _ hh (toRaw i).1.rex)
  have henc : encode i ++ more =
      ((toRaw i).1.pfx.bytes ++ rexBytes (toRaw i).1.rex ++ [0x0F#8, (toRaw i).1.opc]) ++
        (((toRaw i).1.rm.bytes (nibbleLo (toRaw i).1.reg) ++ (toRaw i).1.imm.toList) ++
          ((toRaw i).2.toList ++ more)) := by
    simp [encode, Raw.bytes, toRaw_map, OpMap.bytes]
  unfold Ext.decode
  rw [henc, Ext.good_parseRaw.bad hbad]

end Silmaril.X86.Features.Sse2
