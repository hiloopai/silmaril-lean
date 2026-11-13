module

public import Silmaril.X86.Features.Ext.Sse2.Encoding
public import Silmaril.X86.Features.Ext.SsePacked.Encoding

/-!
# Codec agreement of the two SSE/SSE2 lanes

Two lanes encode the legacy SSE/SSE2 integer and move forms:

* `Sse2` (`isa/x86-ext-sse2`): the integer and move subset, with a verified
  codec checked against GNU as and native differential vectors. It is the
  **canonical** lane on the forms both decode.
* `SsePacked` (recovered in #3585, `isa/x86-sse-packed`): a superset of most of
  it (packed floating point, saturating and multiplying integer forms,
  non-temporal stores, RIP-relative operands, ...).

`toPacked` translates an `Sse2` instruction to the `SsePacked` instruction with
the same encoding. Its only gaps are the alternative register encodings that
`SsePacked` deliberately leaves out: MOVxxx `xmm, xmm` through the store opcode
(`movRRStore`) and MOVQ `xmm, xmm` through `66 0F D6` (`movqStore (.reg _)`).

## Results

* `sse2PRaw_bytes`, `sse2PRaw_wellFormed`: every `Sse2` encoding is the bytes
  of a well-formed `SsePacked.PRaw`.
* `toRaw_toPacked`: `SsePacked` encodes `toPacked i` with the same fields, so
  `encode_toPacked`: `SsePacked.encode j = Sse2.encode i`.
* `ofRaw_sse2PRaw`: `SsePacked`'s field reader returns exactly `toPacked i`.
* `decode_sse2_encode`: on every `Sse2` encoding followed by any bytes,
  `SsePacked.decode` returns `toPacked i` with the same length, or rejects the
  bytes when `toPacked i = none`. `decode_agree` restates it for any bytes that
  `Sse2.decode` accepts.
* `shadowed_iff`: an `SsePacked` instruction is decoded by `Sse2` too
  (`shadowed`) exactly when it is in the image of `toPacked`; the overlap of
  the two decoders is that image.
-/

@[expose] public section

namespace Silmaril.X86.Features.SseMerged

open Silmaril.X86 (XReg Mem Reg Byte)
open Silmaril.X86.Float (XRM GRM)

/-! ## The translation -/

def movKind : Sse2.MovKind → SsePacked.MovKind
  | .dqa => .dqa | .dqu => .dqu | .aps => .aps | .ups => .ups | .apd => .apd | .upd => .upd

def regMov : Sse2.RRKind → SsePacked.RegMov
  | .dqa => .dqa | .dqu => .dqu | .ups => .ups | .upd => .upd

def xrm : XRM → SsePacked.Src
  | .reg r => .reg r
  | .mem m => .mem (.mem m)

def grm : GRM → SsePacked.GSrc
  | .reg r => .reg r
  | .mem m => .mem (.mem m)

/-- The packed-integer operation of an `Sse2.BinOp`. -/
def binOp : Sse2.BinOp → SsePacked.PIntOp
  | .logic .and => .pand | .logic .andn => .pandn | .logic .or => .por | .logic .xor => .pxor
  | .add .b => .paddb | .add .w => .paddw | .add .d => .paddd | .add .q => .paddq
  | .sub .b => .psubb | .sub .w => .psubw | .sub .d => .psubd | .sub .q => .psubq
  | .cmpeq .b => .pcmpeqb | .cmpeq .w => .pcmpeqw | .cmpeq .d => .pcmpeqd
  | .unpackLo .b => .punpcklbw | .unpackLo .w => .punpcklwd | .unpackLo .d => .punpckldq
  | .unpackLo .q => .punpcklqdq
  | .unpackHi .b => .punpckhbw | .unpackHi .w => .punpckhwd | .unpackHi .d => .punpckhdq
  | .unpackHi .q => .punpckhqdq
  | .shift .srlw => .psrlw | .shift .srld => .psrld | .shift .srlq => .psrlq
  | .shift .sraw => .psraw | .shift .srad => .psrad
  | .shift .sllw => .psllw | .shift .slld => .pslld | .shift .sllq => .psllq

def shiftOp : Sse2.ShiftKind → SsePacked.PShiftOp
  | .srlw => .psrlw | .srld => .psrld | .srlq => .psrlq | .sraw => .psraw | .srad => .psrad
  | .sllw => .psllw | .slld => .pslld | .sllq => .psllq

/-- The `SsePacked` instruction with the same encoding, if `SsePacked` has the form. -/
def toPacked : Sse2.Instr → Option SsePacked.Instr
  | .movLoad k dst m => some (.load (movKind k) dst (.mem m))
  | .movStore k m src => some (.store (movKind k) (.mem m) src)
  | .movRR k dst src => some (.movReg (regMov k) dst src)
  | .movRRStore .. => none
  | .movdLoad w dst m => some (.movdLoad w dst (.mem m))
  | .movdStore w m src => some (.movdStore w (.mem m) src)
  | .movqLoad dst src => some (.movqLoad dst (xrm src))
  | .movqStore (.mem m) src => some (.movqStore (.mem m) src)
  | .movqStore (.reg _) _ => none
  | .binop op dst src => some (.pint (binOp op) dst (xrm src))
  | .shiftImm k dst imm => some (.pshiftImm (shiftOp k) dst imm)
  | .shiftBytes false dst imm => some (.pshiftImm .psrldq dst imm)
  | .shiftBytes true dst imm => some (.pshiftImm .pslldq dst imm)
  | .pshufd dst src imm => some (.pshuf .d dst (xrm src) imm)
  | .pmovmskb dst src => some (.movmsk .b dst src)
  | .pinsrw dst src imm => some (.pinsrw dst (grm src) imm)
  | .pextrw dst src imm => some (.pextrw dst src imm)

/-! ## `Sse2` encodings as `SsePacked` fields -/

/-- The fields of an `Sse2` encoding in `SsePacked`'s record (`Sse2` keeps its
imm8 outside `Raw`). -/
def sse2PRaw (i : Sse2.Instr) : SsePacked.PRaw :=
  let r := (Sse2.toRaw i).1
  ⟨r.pfx, r.w, r.opc, r.reg, .ofOperand r.rm, (Sse2.toRaw i).2⟩

theorem sse2PRaw_bytes (i : Sse2.Instr) : (sse2PRaw i).bytes = Sse2.encode i := by
  have hm := Sse2.toRaw_map i
  have hi := Sse2.toRaw_imm i
  unfold sse2PRaw Sse2.encode
  generalize Sse2.toRaw i = p at hm hi ⊢
  obtain ⟨⟨pfx, w, map, opc, reg, rm, imm⟩, imm8⟩ := p
  simp only at hm hi
  subst hm hi
  simp [SsePacked.PRaw.bytes, X86.Raw.bytes, SsePacked.PRaw.rex, X86.Raw.rex, X86.OpMap.bytes]

theorem sse2PRaw_wellFormed (i : Sse2.Instr) : (sse2PRaw i).WellFormed := by
  unfold SsePacked.PRaw.WellFormed
  cases i
  case binop op _ _ =>
    rcases op with (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _) |
      (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl
  case movLoad k _ _ | movStore k _ _ | movRRStore k _ _ => cases k <;> rfl
  case movRR k _ _ => cases k <;> rfl
  case shiftImm k _ _ => cases k <;> rfl
  case shiftBytes left _ _ => cases left <;> rfl
  all_goals rfl

theorem xrm_toOp (src : XRM) : (xrm src).toOp = .ofOperand src.toOperand := by
  cases src <;> rfl

theorem grm_toOp (src : GRM) : (grm src).toOp = .ofOperand src.toOperand := by
  cases src <;> rfl

/-- `SsePacked` gives `toPacked i` the fields of `i`. -/
theorem toRaw_toPacked {i : Sse2.Instr} {j : SsePacked.Instr} (h : toPacked i = some j) :
    SsePacked.toRaw j = sse2PRaw i := by
  cases i
  case binop op dst src =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    simp only [SsePacked.toRaw, SsePacked.mk, sse2PRaw, Sse2.toRaw, Sse2.raw, xrm_toOp,
      SsePacked.PRaw.mk.injEq, and_true, true_and]
    rcases op with (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _) |
      (_ | _ | _ | _) | (_ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _ | _) <;> rfl
  case movLoad k _ _ | movStore k _ _ =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    cases k <;> rfl
  case movRR k _ _ =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    cases k <;> rfl
  case movRRStore => cases h
  case movqStore dst _ =>
    cases dst with
    | reg => cases h
    | mem =>
      simp only [toPacked, Option.some.injEq] at h
      subst h
      rfl
  case shiftImm k _ _ =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    cases k <;> rfl
  case shiftBytes left _ _ =>
    cases left <;>
    · simp only [toPacked, Option.some.injEq] at h
      subst h
      rfl
  case movqLoad dst src | pshufd dst src _ =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    simp [SsePacked.toRaw, SsePacked.mk, sse2PRaw, Sse2.toRaw, Sse2.raw, xrm_toOp,
      SsePacked.ShufKind.pfx]
  case pinsrw dst src _ =>
    simp only [toPacked, Option.some.injEq] at h
    subst h
    simp [SsePacked.toRaw, SsePacked.mk, sse2PRaw, Sse2.toRaw, Sse2.raw, grm_toOp]
  all_goals
    simp only [toPacked, Option.some.injEq] at h
    subst h
    rfl

theorem encode_toPacked {i : Sse2.Instr} {j : SsePacked.Instr} (h : toPacked i = some j) :
    SsePacked.encode j = Sse2.encode i := by
  rw [SsePacked.encode, toRaw_toPacked h, sse2PRaw_bytes]

/-- `SsePacked`'s field reader on an `Sse2` encoding returns `toPacked`. -/
theorem ofRaw_sse2PRaw (i : Sse2.Instr) : SsePacked.ofRaw (sse2PRaw i) = toPacked i := by
  cases h : toPacked i with
  | some j => rw [← toRaw_toPacked h, SsePacked.ofRaw_toRaw]
  | none =>
    cases i
    case movRRStore k _ _ => cases k <;> rfl
    case movqStore dst _ =>
      cases dst with
      | reg => rfl
      | mem => cases h
    case shiftBytes left _ _ => cases left <;> cases h
    all_goals cases h

/-- **Codec agreement.** On an `Sse2` encoding followed by any bytes,
`SsePacked` decodes the translated instruction with the same length, and
rejects the bytes when `SsePacked` has no such form. -/
theorem decode_sse2_encode (i : Sse2.Instr) (rest : List Byte) :
    SsePacked.decode (Sse2.encode i ++ rest) =
      (toPacked i).map fun j => (j, (Sse2.encode i).length) := by
  unfold SsePacked.decode
  rw [← sse2PRaw_bytes, SsePacked.PRaw.parse_bytes _ (sse2PRaw_wellFormed i) rest]
  simp [ofRaw_sse2PRaw]

/-- The same for any bytes that `Sse2` decodes. -/
theorem decode_agree {bytes : List Byte} {i : Sse2.Instr} {n : Nat}
    (h : Sse2.decode bytes = some (i, n)) :
    SsePacked.decode bytes = (toPacked i).map fun j => (j, n) := by
  obtain ⟨rfl, -, hb⟩ := Sse2.decode_sound h
  rw [hb, decode_sse2_encode]

/-! ## The overlap -/

/-- `Sse2` also decodes the encoding of `j`. -/
def shadowed (j : SsePacked.Instr) : Bool := (Sse2.decode (SsePacked.encode j)).isSome

/-- The two decoders overlap exactly on the image of `toPacked`. -/
theorem shadowed_iff (j : SsePacked.Instr) : shadowed j = true ↔ ∃ i, toPacked i = some j := by
  constructor
  · intro h
    obtain ⟨⟨i, n⟩, hi⟩ := Option.isSome_iff_exists.mp h
    refine ⟨i, ?_⟩
    have hself : SsePacked.decode (SsePacked.encode j) = some (j, (SsePacked.encode j).length) := by
      simp
    have := decode_agree hi
    rw [hself] at this
    cases ht : toPacked i with
    | none => rw [ht] at this; cases this
    | some j' =>
      rw [ht] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      rw [this.1]
  · rintro ⟨i, hi⟩
    have hd : Sse2.decode (Sse2.encode i) = some (i, (Sse2.encode i).length) := by
      simpa using Sse2.decode_encode_append i []
    simp [shadowed, encode_toPacked hi, hd]

end Silmaril.X86.Features.SseMerged
