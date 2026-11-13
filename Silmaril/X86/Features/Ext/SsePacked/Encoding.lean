module

public import Silmaril.X86.Features.Ext.SsePacked.Syntax
public import Silmaril.X86.Float.Encoding

/-!
# Byte codec of the SSE/SSE2 packed lane

A verified prefix-code encoder and decoder for `SsePacked.Instr`, in the style of
`X86.Float.Encoding`, whose operand layers (ModRM, SIB, displacement, REX, the
mandatory prefix) it reuses. Two layers differ:

* **Operands.** `POperand` adds RIP-relative addressing (`mod = 00`,
  `r/m = 101`, then a disp32; SDM Vol. 2A, §2.2.1.6, Table 2-7) to
  `X86.Operand`. REX.X and REX.B must be clear with it (they are ignored by
  hardware, so a set bit is non-canonical).
* **Raw fields.** `PRaw` is `X86.Raw` without the `0F 38`/`0F 3A` maps (every
  instruction here is in the `0F` map) and with this lane's immediate table
  `hasImm` (`0F 70-73`, `C2`, `C4-C6`).

The opcode table is `toRaw`; `candidate` reads it backwards and `ofRaw` keeps a
candidate only if `toRaw` reproduces every field, so ignored or fixed fields
(REX.W on PADDD, the ModRM `r/m` of a fence) must have their canonical value.
The decoder accepts exactly the encoder's outputs followed by arbitrary bytes
(`decode_encode_append`, `decode_sound`), and `byteDecoder` packages the
`Machine.Decoder` laws.

`none` means "outside this canonical subset", not "invalid on hardware":
redundant prefixes, the alternative register encodings of the stores
(`0F 29 /r` with `mod = 11`, `66 0F D6` between registers), immediates of
CMPPS/CMPPD above 7, a set REX bit that the instruction ignores and
non-minimal displacements are all rejected.
-/

@[expose] public section

namespace Silmaril.X86.Features.SsePacked

open Silmaril.X86 (XReg Mem Reg Byte Operand Prefix parsePrefix parseRex rexBytes rexByte
  rexNibble nibbleHi nibbleLo fieldByte parseOperand imm32Bytes decodeImm32 parseImm8)
open Silmaril.X86.Float (Precision CmpPred LogicOp IntWidth ArithOp)

/-! ## Operands with RIP-relative addressing -/

/-- A ModRM `r/m` operand: register, base-register memory or RIP-relative. -/
inductive POperand where
  | reg (n : BitVec 4)
  | mem (m : Mem)
  | rip (disp : BitVec 32)
  deriving DecidableEq, Repr

namespace POperand

def ofOperand : Operand → POperand
  | .reg n => .reg n
  | .mem m => .mem m

def xBit : POperand → BitVec 1
  | reg _ => 0#1
  | mem m => m.xBit
  | rip _ => 0#1

def bBit : POperand → BitVec 1
  | reg n => nibbleHi n
  | mem m => m.base.hi
  | rip _ => 0#1

/-- The ModRM byte with `reg = regf` and the bytes that follow it. -/
def bytes (regf : BitVec 3) : POperand → List Byte
  | reg n => [fieldByte 3#2 regf (nibbleLo n)]
  | mem m => fieldByte m.modField regf m.rmField :: m.tailBytes
  | rip d => fieldByte 0#2 regf 5#3 :: imm32Bytes d

@[simp] theorem xBit_ofOperand (op : Operand) : (ofOperand op).xBit = op.xBit := by
  cases op <;> rfl

@[simp] theorem bBit_ofOperand (op : Operand) : (ofOperand op).bBit = op.bBit := by
  cases op <;> rfl

@[simp] theorem bytes_ofOperand (regf : BitVec 3) (op : Operand) :
    (ofOperand op).bytes regf = op.bytes regf := by
  cases op <;> rfl

end POperand

/-- The ModRM byte of a base-register memory operand is never the RIP-relative
pattern `mod = 00, r/m = 101`. -/
theorem Mem.not_ripForm (m : Mem) : ¬ (m.modField = 0#2 ∧ m.rmField = 5#3) := by
  rintro ⟨hm, hr⟩
  unfold Mem.modField X86.dispMod at hm
  split_ifs at hm with h0 h8
  · obtain ⟨-, h5⟩ := h0
    unfold Mem.rmField at hr
    split_ifs at hr
    · exact absurd hr (by decide)
    · exact h5 hr
  all_goals exact absurd hm (by decide)

/-- Read a ModRM byte and its operand bytes, given REX.X and REX.B. -/
def parsePOperand (x b : BitVec 1) : List Byte → Option ((BitVec 3 × POperand) × List Byte)
  | [] => none
  | mb :: rest =>
    if mb.top = 0#2 ∧ mb.low = 5#3 then
      if x = 0#1 ∧ b = 0#1 then
        (decodeImm32 rest).map fun d => ((mb.mid, .rip d), rest.drop 4)
      else none
    else (parseOperand x b (mb :: rest)).map fun ((regf, op), rest) =>
      ((regf, POperand.ofOperand op), rest)

theorem parsePOperand_bytes (regf : BitVec 3) (op : POperand) (rest : List Byte) :
    parsePOperand op.xBit op.bBit (op.bytes regf ++ rest) = some ((regf, op), rest) := by
  cases op with
  | reg n =>
    have h := X86.parseOperand_bytes regf (.reg n) rest
    simp only [Operand.xBit, Operand.bBit, Operand.bytes, List.cons_append, List.nil_append] at h
    simp [parsePOperand, POperand.xBit, POperand.bBit, POperand.bytes, h,
      POperand.ofOperand]
  | mem m =>
    have h := X86.parseOperand_bytes regf (.mem m) rest
    simp only [Operand.xBit, Operand.bBit, Operand.bytes, List.cons_append] at h
    have hn := Mem.not_ripForm m
    simp only [parsePOperand, POperand.xBit, POperand.bBit, POperand.bytes, List.cons_append,
      X86.fieldByte_top, X86.fieldByte_low, hn, ite_false, h, Option.map_some,
      POperand.ofOperand]
  | rip d =>
    simp [parsePOperand, POperand.xBit, POperand.bBit, POperand.bytes,
      List.drop_left' (X86.length_imm32Bytes d)]

theorem parsePOperand_sound {x b : BitVec 1} {bytes rest : List Byte} {regf : BitVec 3}
    {op : POperand} (h : parsePOperand x b bytes = some ((regf, op), rest)) :
    x = op.xBit ∧ b = op.bBit ∧ bytes = op.bytes regf ++ rest := by
  match bytes, h with
  | mb :: tail, h =>
    simp only [parsePOperand] at h
    split_ifs at h with hr hxb
    · obtain ⟨d, hd, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      refine ⟨hxb.1, hxb.2, ?_⟩
      have hrest := X86.imm32Bytes_of_decodeImm32 hd
      have hmb : fieldByte 0#2 mb.mid 5#3 = mb := by rw [← hr.1, ← hr.2, X86.fieldByte_eta]
      rw [POperand.bytes, List.cons_append, hrest, hmb]
    · obtain ⟨⟨⟨regf', op'⟩, rest'⟩, ho, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      obtain ⟨hx, hb, hbytes⟩ := X86.parseOperand_sound ho
      exact ⟨by simp [hx], by simp [hb], by simp [hbytes]⟩

/-! ## Raw fields -/

/-- The opcodes followed by an 8-bit immediate. -/
def hasImm (opc : Byte) : Bool :=
  opc == 0x70#8 || opc == 0x71#8 || opc == 0x72#8 || opc == 0x73#8 || opc == 0xC2#8 ||
    opc == 0xC4#8 || opc == 0xC5#8 || opc == 0xC6#8

/-- The fields of a legacy-encoded `0F`-map instruction with a ModRM byte. -/
structure PRaw where
  pfx : Prefix
  w : BitVec 1
  opc : Byte
  reg : BitVec 4
  rm : POperand
  imm : Option Byte
  deriving DecidableEq, Repr

namespace PRaw

def rex (r : PRaw) : BitVec 4 := rexNibble r.w (nibbleHi r.reg) r.rm.xBit r.rm.bBit

/-- The canonical bytes: prefix, REX (only when a bit is set), `0F`, opcode,
operand bytes, immediate. -/
def bytes (r : PRaw) : List Byte :=
  r.pfx.bytes ++ (rexBytes r.rex ++ (0x0F#8 :: r.opc :: (r.rm.bytes (nibbleLo r.reg) ++
    r.imm.toList)))

/-- The immediate is present exactly when the opcode takes one. -/
def WellFormed (r : PRaw) : Prop := r.imm.isSome = hasImm r.opc

/-- Read one instruction. -/
def parse (bytes : List Byte) : Option (PRaw × List Byte) :=
  match parsePrefix bytes with
  | (pfx, bytes) =>
  match parseRex bytes with
  | none => none
  | some (rex, bytes) =>
  match bytes with
  | esc :: opc :: bytes =>
    if esc = 0x0F#8 then
      match parsePOperand (rex.extractLsb' 1 1) (rex.extractLsb' 0 1) bytes with
      | none => none
      | some ((regf, rm), bytes) =>
        (parseImm8 (hasImm opc) bytes).map fun (imm, bytes) =>
          ({ pfx, w := rex.extractLsb' 3 1, opc, reg := rex.extractLsb' 2 1 ++ regf, rm, imm },
            bytes)
    else none
  | _ => none

theorem bytes_length_le (r : PRaw) : r.bytes.length ≤ 11 := by
  obtain ⟨pfx, w, opc, reg, rm, imm⟩ := r
  have hp : pfx.bytes.length ≤ 1 := by cases pfx <;> simp [Prefix.bytes]
  have hi : imm.toList.length ≤ 1 := by cases imm <;> simp
  have hx (n : BitVec 4) : (rexBytes n).length ≤ 1 := by unfold rexBytes; split <;> simp
  have hd (bl : BitVec 3) (d : BitVec 32) : (X86.dispBytes bl d).length ≤ 4 := by
    unfold X86.dispBytes; split_ifs <;> simp
  have ho (regf : BitVec 3) (op : POperand) : (op.bytes regf).length ≤ 6 := by
    cases op with
    | reg n => simp [POperand.bytes]
    | mem m =>
      simp only [POperand.bytes, Mem.tailBytes, List.length_cons, List.length_append]
      have := hd m.base.lo m.disp
      split_ifs <;> simp <;> omega
    | rip d => simp [POperand.bytes]
  have := hx (rexNibble w (nibbleHi reg) rm.xBit rm.bBit)
  have := ho (nibbleLo reg) rm
  simp only [bytes, rex, List.length_append, List.length_cons]
  omega

theorem bytes_length_ge (r : PRaw) : 3 ≤ r.bytes.length := by
  simp only [bytes, List.length_append, List.length_cons]
  cases r.rm <;> simp [POperand.bytes] <;> omega

end PRaw

theorem parsePrefix_rex (n : BitVec 4) (rest : List Byte) :
    parsePrefix (rexBytes n ++ 0x0F#8 :: rest) = (.none, rexBytes n ++ 0x0F#8 :: rest) := by
  unfold rexBytes
  split
  · simp [parsePrefix]
  · have h1 : rexByte n ≠ 0x66#8 := by revert n; decide
    have h2 : rexByte n ≠ 0xF2#8 := by revert n; decide
    have h3 : rexByte n ≠ 0xF3#8 := by revert n; decide
    simp [parsePrefix, h1, h2, h3]

namespace PRaw

/-- The parser recovers every well-formed `PRaw` from its bytes. -/
theorem parse_bytes (r : PRaw) (wf : r.WellFormed) (rest : List Byte) :
    parse (r.bytes ++ rest) = some (r, rest) := by
  obtain ⟨pfx, w, opc, reg, rm, imm⟩ := r
  unfold WellFormed at wf
  dsimp only at wf
  simp only [bytes, List.append_assoc, List.cons_append]
  unfold parse
  rw [X86.parsePrefix_bytes _ (parsePrefix_rex _ _)]
  simp only
  rw [X86.parseRex_rexBytes _ _ _ (by decide)]
  simp only [ite_true, rex, X86.rexNibble_x, X86.rexNibble_b, X86.rexNibble_w, X86.rexNibble_r]
  rw [parsePOperand_bytes]
  simp only
  rw [X86.parseImm8_toList wf]
  simp

/-- Every successful parse consumed the canonical bytes of its result. -/
theorem parse_sound {bytes rest : List Byte} {r : PRaw} (h : parse bytes = some (r, rest)) :
    bytes = r.bytes ++ rest := by
  unfold parse at h
  rcases hp : parsePrefix bytes with ⟨pfx, b1⟩
  rw [hp] at h
  simp only at h
  cases hr : parseRex b1 with
  | none => rw [hr] at h; cases h
  | some res =>
  obtain ⟨n, b2⟩ := res
  rw [hr] at h
  simp only at h
  match b2, h with
  | esc :: opc :: b3, h =>
  simp only at h
  split_ifs at h with hesc
  cases ho : parsePOperand (n.extractLsb' 1 1) (n.extractLsb' 0 1) b3 with
  | none => rw [ho] at h; cases h
  | some res =>
  obtain ⟨⟨regf, rm⟩, b4⟩ := res
  rw [ho] at h
  simp only at h
  obtain ⟨⟨imm, b5⟩, hi, heq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨hx, hb, h4⟩ := parsePOperand_sound ho
  rw [X86.parsePrefix_sound hp, X86.parseRex_sound hr, h4, X86.parseImm8_sound hi, hesc]
  have hrex : rexNibble (n.extractLsb' 3 1) (n.extractLsb' 2 1) rm.xBit rm.bBit = n := by
    rw [← hx, ← hb, X86.rexNibble_eta]
  simp [PRaw.bytes, rex, hrex]

/-- The prefix and opcode bytes determine the parsed prefix and opcode. -/
theorem parse_opc {p : Prefix} {n : BitVec 4} {o : Byte} {tail rest : List Byte} {r : PRaw}
    (h : parse (p.bytes ++ (rexBytes n ++ 0x0F#8 :: o :: tail)) = some (r, rest)) :
    r.opc = o := by
  unfold parse at h
  rw [X86.parsePrefix_bytes _ (parsePrefix_rex _ _)] at h
  simp only at h
  rw [X86.parseRex_rexBytes _ _ _ (by decide)] at h
  simp only [ite_true] at h
  cases ho : parsePOperand (n.extractLsb' 1 1) (n.extractLsb' 0 1) tail with
  | none => rw [ho] at h; cases h
  | some res =>
    rw [ho] at h
    obtain ⟨⟨imm, b5⟩, -, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    rw [← heq.1]

end PRaw

/-! ## Operand conversions -/

def Addr.toOp : Addr → POperand
  | .mem m => .mem m
  | .rip d => .rip d

def Src.toOp : Src → POperand
  | .reg r => .reg r.toBitVec
  | .mem a => a.toOp

def GSrc.toOp : GSrc → POperand
  | .reg r => .reg r.toBitVec
  | .mem a => a.toOp

def POperand.toSrc : POperand → Src
  | .reg n => .reg (XReg.ofBitVec n)
  | .mem m => .mem (.mem m)
  | .rip d => .mem (.rip d)

def POperand.toGSrc : POperand → GSrc
  | .reg n => .reg (Reg.ofBitVec n)
  | .mem m => .mem (.mem m)
  | .rip d => .mem (.rip d)

def POperand.toAddr? : POperand → Option Addr
  | .reg _ => none
  | .mem m => some (.mem m)
  | .rip d => some (.rip d)

@[simp] theorem Src.toOp_toSrc (s : Src) : s.toOp.toSrc = s := by
  cases s with
  | reg r => simp [Src.toOp, POperand.toSrc]
  | mem a => cases a <;> rfl

@[simp] theorem GSrc.toOp_toGSrc (s : GSrc) : s.toOp.toGSrc = s := by
  cases s with
  | reg r => simp [GSrc.toOp, POperand.toGSrc]
  | mem a => cases a <;> rfl

@[simp] theorem Addr.toOp_toAddr? (a : Addr) : a.toOp.toAddr? = some a := by
  cases a <;> rfl

/-! ## Opcode tables -/

def MovKind.pfx : MovKind → Prefix
  | .aps | .ups => .none
  | .apd | .upd | .dqa => .p66
  | .dqu => .pF3

def MovKind.loadOpc : MovKind → Byte
  | .aps | .apd => 0x28#8
  | .ups | .upd => 0x10#8
  | .dqa | .dqu => 0x6F#8

def MovKind.storeOpc : MovKind → Byte
  | .aps | .apd => 0x29#8
  | .ups | .upd => 0x11#8
  | .dqa | .dqu => 0x7F#8

def NTKind.pfx : NTKind → Prefix
  | .ps => .none
  | .pd | .dq => .p66

def NTKind.opc : NTKind → Byte
  | .ps | .pd => 0x2B#8
  | .dq => 0xE7#8

def MskKind.pfx : MskKind → Prefix
  | .ps => .none
  | .pd | .b => .p66

def MskKind.opc : MskKind → Byte
  | .ps | .pd => 0x50#8
  | .b => 0xD7#8

def PIntOp.opcode : PIntOp → Byte
  | .paddb => 0xFC#8 | .paddw => 0xFD#8 | .paddd => 0xFE#8 | .paddq => 0xD4#8
  | .psubb => 0xF8#8 | .psubw => 0xF9#8 | .psubd => 0xFA#8 | .psubq => 0xFB#8
  | .paddsb => 0xEC#8 | .paddsw => 0xED#8 | .paddusb => 0xDC#8 | .paddusw => 0xDD#8
  | .psubsb => 0xE8#8 | .psubsw => 0xE9#8 | .psubusb => 0xD8#8 | .psubusw => 0xD9#8
  | .pmullw => 0xD5#8 | .pmulhw => 0xE5#8 | .pmulhuw => 0xE4#8 | .pmuludq => 0xF4#8
  | .pmaddwd => 0xF5#8 | .psadbw => 0xF6#8
  | .pavgb => 0xE0#8 | .pavgw => 0xE3#8 | .pminub => 0xDA#8 | .pmaxub => 0xDE#8
  | .pminsw => 0xEA#8 | .pmaxsw => 0xEE#8
  | .pcmpeqb => 0x74#8 | .pcmpeqw => 0x75#8 | .pcmpeqd => 0x76#8
  | .pcmpgtb => 0x64#8 | .pcmpgtw => 0x65#8 | .pcmpgtd => 0x66#8
  | .pand => 0xDB#8 | .pandn => 0xDF#8 | .por => 0xEB#8 | .pxor => 0xEF#8
  | .punpcklbw => 0x60#8 | .punpcklwd => 0x61#8 | .punpckldq => 0x62#8 | .punpcklqdq => 0x6C#8
  | .punpckhbw => 0x68#8 | .punpckhwd => 0x69#8 | .punpckhdq => 0x6A#8 | .punpckhqdq => 0x6D#8
  | .packsswb => 0x63#8 | .packssdw => 0x6B#8 | .packuswb => 0x67#8
  | .psrlw => 0xD1#8 | .psrld => 0xD2#8 | .psrlq => 0xD3#8 | .psraw => 0xE1#8
  | .psrad => 0xE2#8 | .psllw => 0xF1#8 | .pslld => 0xF2#8 | .psllq => 0xF3#8

def PIntOp.ofOpcode? (b : Byte) : Option PIntOp :=
  match b.toNat with
  | 0xFC => some .paddb | 0xFD => some .paddw | 0xFE => some .paddd | 0xD4 => some .paddq
  | 0xF8 => some .psubb | 0xF9 => some .psubw | 0xFA => some .psubd | 0xFB => some .psubq
  | 0xEC => some .paddsb | 0xED => some .paddsw | 0xDC => some .paddusb | 0xDD => some .paddusw
  | 0xE8 => some .psubsb | 0xE9 => some .psubsw | 0xD8 => some .psubusb | 0xD9 => some .psubusw
  | 0xD5 => some .pmullw | 0xE5 => some .pmulhw | 0xE4 => some .pmulhuw | 0xF4 => some .pmuludq
  | 0xF5 => some .pmaddwd | 0xF6 => some .psadbw
  | 0xE0 => some .pavgb | 0xE3 => some .pavgw | 0xDA => some .pminub | 0xDE => some .pmaxub
  | 0xEA => some .pminsw | 0xEE => some .pmaxsw
  | 0x74 => some .pcmpeqb | 0x75 => some .pcmpeqw | 0x76 => some .pcmpeqd
  | 0x64 => some .pcmpgtb | 0x65 => some .pcmpgtw | 0x66 => some .pcmpgtd
  | 0xDB => some .pand | 0xDF => some .pandn | 0xEB => some .por | 0xEF => some .pxor
  | 0x60 => some .punpcklbw | 0x61 => some .punpcklwd | 0x62 => some .punpckldq
  | 0x6C => some .punpcklqdq
  | 0x68 => some .punpckhbw | 0x69 => some .punpckhwd | 0x6A => some .punpckhdq
  | 0x6D => some .punpckhqdq
  | 0x63 => some .packsswb | 0x6B => some .packssdw | 0x67 => some .packuswb
  | 0xD1 => some .psrlw | 0xD2 => some .psrld | 0xD3 => some .psrlq | 0xE1 => some .psraw
  | 0xE2 => some .psrad | 0xF1 => some .psllw | 0xF2 => some .pslld | 0xF3 => some .psllq
  | _ => none

theorem PIntOp.ofOpcode?_opcode (op : PIntOp) : PIntOp.ofOpcode? op.opcode = some op := by
  cases op <;> rfl

/-- The opcode of a shift by an immediate. -/
def PShiftOp.opcode : PShiftOp → Byte
  | .psrlw | .psraw | .psllw => 0x71#8
  | .psrld | .psrad | .pslld => 0x72#8
  | .psrlq | .psrldq | .psllq | .pslldq => 0x73#8

/-- The ModRM `reg` field (`/digit`) of a shift by an immediate. -/
def PShiftOp.digit : PShiftOp → BitVec 4
  | .psrlw | .psrld | .psrlq => 2#4
  | .psraw | .psrad => 4#4
  | .psllw | .pslld | .psllq => 6#4
  | .psrldq => 3#4
  | .pslldq => 7#4

def PShiftOp.ofFields? (opc : Byte) (digit : BitVec 4) : Option PShiftOp :=
  match opc.toNat, digit.toNat with
  | 0x71, 2 => some .psrlw | 0x71, 4 => some .psraw | 0x71, 6 => some .psllw
  | 0x72, 2 => some .psrld | 0x72, 4 => some .psrad | 0x72, 6 => some .pslld
  | 0x73, 2 => some .psrlq | 0x73, 3 => some .psrldq | 0x73, 6 => some .psllq
  | 0x73, 7 => some .pslldq
  | _, _ => none

theorem PShiftOp.ofFields?_opcode (op : PShiftOp) :
    PShiftOp.ofFields? op.opcode op.digit = some op := by
  cases op <;> rfl

def ShufKind.pfx : ShufKind → Prefix
  | .d => .p66 | .hw => .pF3 | .lw => .pF2

def CvtKind.pfx : CvtKind → Prefix
  | .dq2ps | .ps2pd => .none
  | .ps2dq | .pd2ps | .tpd2dq => .p66
  | .tps2dq | .dq2pd => .pF3
  | .pd2dq => .pF2

def CvtKind.opc : CvtKind → Byte
  | .dq2ps | .ps2dq | .tps2dq => 0x5B#8
  | .ps2pd | .pd2ps => 0x5A#8
  | .dq2pd | .pd2dq | .tpd2dq => 0xE6#8

def ApproxKind.pfx : ApproxKind → Prefix
  | .rcpps | .rsqrtps => .none
  | .rcpss | .rsqrtss => .pF3

def ApproxKind.opc : ApproxKind → Byte
  | .rcpps | .rcpss => 0x53#8
  | .rsqrtps | .rsqrtss => 0x52#8

def FenceKind.digit : FenceKind → BitVec 4
  | .lfence => 5#4 | .mfence => 6#4 | .sfence => 7#4

def PrefetchHint.digit : PrefetchHint → BitVec 4
  | .nta => 0#4 | .t0 => 1#4 | .t1 => 2#4 | .t2 => 3#4

/-- A field record with the given values and no immediate. -/
def mk (pfx : Prefix) (w : BitVec 1) (opc : Byte) (reg : BitVec 4) (rm : POperand)
    (imm : Option Byte := none) : PRaw :=
  { pfx, w, opc, reg, rm, imm }

/-- The fields of each instruction (SDM Vol. 2, opcode columns). The stores put
their source register in ModRM `reg`; PEXTRW, MOVMSKPS/PD and PMOVMSKB put the
general-purpose destination there; shifts by an immediate and the fences use it
for the `/digit` extension. -/
def toRaw : Instr → PRaw
  | .load k dst a => mk k.pfx 0#1 k.loadOpc dst.toBitVec a.toOp
  | .store k a src => mk k.pfx 0#1 k.storeOpc src.toBitVec a.toOp
  | .movReg k dst src => mk k.toMovKind.pfx 0#1 k.toMovKind.loadOpc dst.toBitVec (.reg src.toBitVec)
  | .storeNT k a src => mk k.pfx 0#1 k.opc src.toBitVec a.toOp
  | .maskmovdqu src mask => mk .p66 0#1 0xF7#8 src.toBitVec (.reg mask.toBitVec)
  | .movqLoad dst src => mk .pF3 0#1 0x7E#8 dst.toBitVec src.toOp
  | .movqStore a src => mk .p66 0#1 0xD6#8 src.toBitVec a.toOp
  | .movdLoad w dst a => mk .p66 w.wBit 0x6E#8 dst.toBitVec a.toOp
  | .movdStore w a src => mk .p66 w.wBit 0x7E#8 src.toBitVec a.toOp
  | .movHalfLoad high pd dst a =>
    mk (if pd then .p66 else .none) 0#1 (if high then 0x16#8 else 0x12#8) dst.toBitVec a.toOp
  | .movHalfStore high pd a src =>
    mk (if pd then .p66 else .none) 0#1 (if high then 0x17#8 else 0x13#8) src.toBitVec a.toOp
  | .movhlps dst src => mk .none 0#1 0x12#8 dst.toBitVec (.reg src.toBitVec)
  | .movlhps dst src => mk .none 0#1 0x16#8 dst.toBitVec (.reg src.toBitVec)
  | .movmsk k dst src => mk k.pfx 0#1 k.opc dst.toBitVec (.reg src.toBitVec)
  | .pinsrw dst src imm => mk .p66 0#1 0xC4#8 dst.toBitVec src.toOp (some imm)
  | .pextrw dst src imm => mk .p66 0#1 0xC5#8 dst.toBitVec (.reg src.toBitVec) (some imm)
  | .pint op dst src => mk .p66 0#1 op.opcode dst.toBitVec src.toOp
  | .pshiftImm op dst imm => mk .p66 0#1 op.opcode op.digit (.reg dst.toBitVec) (some imm)
  | .pshuf k dst src imm => mk k.pfx 0#1 0x70#8 dst.toBitVec src.toOp (some imm)
  | .arithp op p dst src => mk p.packedPrefix 0#1 op.opcode dst.toBitVec src.toOp
  | .sqrtp p dst src => mk p.packedPrefix 0#1 0x51#8 dst.toBitVec src.toOp
  | .cmpp p pred dst src => mk p.packedPrefix 0#1 0xC2#8 dst.toBitVec src.toOp (some pred.toByte)
  | .logicRip op p dst d => mk p.packedPrefix 0#1 op.opcode dst.toBitVec (.rip d)
  | .unpckp high p dst src =>
    mk p.packedPrefix 0#1 (if high then 0x15#8 else 0x14#8) dst.toBitVec src.toOp
  | .shufp p dst src imm => mk p.packedPrefix 0#1 0xC6#8 dst.toBitVec src.toOp (some imm)
  | .cvtp k dst src => mk k.pfx 0#1 k.opc dst.toBitVec src.toOp
  | .approx k dst src => mk k.pfx 0#1 k.opc dst.toBitVec src.toOp
  | .fence k => mk .none 0#1 0xAE#8 k.digit (.reg 0#4)
  | .prefetch h a => mk .none 0#1 0x18#8 h.digit a.toOp

/-- The `66` table. -/
def cand66 (r : PRaw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match PIntOp.ofOpcode? r.opc with
  | some op => some (.pint op x r.rm.toSrc)
  | none =>
  match r.opc.toNat with
  | 0x10 =>
    match r.rm with
    | .reg n => some (.movReg .upd x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.load .upd x)
  | 0x11 => r.rm.toAddr?.map fun a => .store .upd a x
  | 0x12 => r.rm.toAddr?.map (.movHalfLoad false true x)
  | 0x13 => r.rm.toAddr?.map fun a => .movHalfStore false true a x
  | 0x14 => some (.unpckp false .double x r.rm.toSrc)
  | 0x15 => some (.unpckp true .double x r.rm.toSrc)
  | 0x16 => r.rm.toAddr?.map (.movHalfLoad true true x)
  | 0x17 => r.rm.toAddr?.map fun a => .movHalfStore true true a x
  | 0x28 => r.rm.toAddr?.map (.load .apd x)
  | 0x29 => r.rm.toAddr?.map fun a => .store .apd a x
  | 0x2B => r.rm.toAddr?.map fun a => .storeNT .pd a x
  | 0x50 =>
    match r.rm with
    | .reg n => some (.movmsk .pd (Reg.ofBitVec r.reg) (XReg.ofBitVec n))
    | _ => none
  | 0x51 => some (.sqrtp .double x r.rm.toSrc)
  | 0x54 => match r.rm with | .rip d => some (.logicRip .and .double x d) | _ => none
  | 0x55 => match r.rm with | .rip d => some (.logicRip .andn .double x d) | _ => none
  | 0x56 => match r.rm with | .rip d => some (.logicRip .or .double x d) | _ => none
  | 0x57 => match r.rm with | .rip d => some (.logicRip .xor .double x d) | _ => none
  | 0x58 => some (.arithp .add .double x r.rm.toSrc)
  | 0x59 => some (.arithp .mul .double x r.rm.toSrc)
  | 0x5A => some (.cvtp .pd2ps x r.rm.toSrc)
  | 0x5B => some (.cvtp .ps2dq x r.rm.toSrc)
  | 0x5C => some (.arithp .sub .double x r.rm.toSrc)
  | 0x5D => some (.arithp .min .double x r.rm.toSrc)
  | 0x5E => some (.arithp .div .double x r.rm.toSrc)
  | 0x5F => some (.arithp .max .double x r.rm.toSrc)
  | 0x6E => r.rm.toAddr?.map (.movdLoad (IntWidth.ofBit r.w) x)
  | 0x6F =>
    match r.rm with
    | .reg n => some (.movReg .dqa x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.load .dqa x)
  | 0x70 => r.imm.map (.pshuf .d x r.rm.toSrc)
  | 0x71 | 0x72 | 0x73 =>
    match PShiftOp.ofFields? r.opc r.reg, r.rm, r.imm with
    | some op, .reg n, some b => some (.pshiftImm op (XReg.ofBitVec n) b)
    | _, _, _ => none
  | 0x7E => r.rm.toAddr?.map fun a => .movdStore (IntWidth.ofBit r.w) a x
  | 0x7F => r.rm.toAddr?.map fun a => .store .dqa a x
  | 0xC2 =>
    match r.imm with
    | some b => (CmpPred.ofByte? b).map fun pred => .cmpp .double pred x r.rm.toSrc
    | none => none
  | 0xC4 => r.imm.map (.pinsrw x r.rm.toGSrc)
  | 0xC5 =>
    match r.rm, r.imm with
    | .reg n, some b => some (.pextrw (Reg.ofBitVec r.reg) (XReg.ofBitVec n) b)
    | _, _ => none
  | 0xC6 => r.imm.map (.shufp .double x r.rm.toSrc)
  | 0xD6 => r.rm.toAddr?.map fun a => .movqStore a x
  | 0xD7 =>
    match r.rm with
    | .reg n => some (.movmsk .b (Reg.ofBitVec r.reg) (XReg.ofBitVec n))
    | _ => none
  | 0xE6 => some (.cvtp .tpd2dq x r.rm.toSrc)
  | 0xE7 => r.rm.toAddr?.map fun a => .storeNT .dq a x
  | 0xF7 =>
    match r.rm with
    | .reg n => some (.maskmovdqu x (XReg.ofBitVec n))
    | _ => none
  | _ => none

/-- The table without a mandatory prefix. -/
def candNone (r : PRaw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match r.opc.toNat with
  | 0x10 =>
    match r.rm with
    | .reg n => some (.movReg .ups x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.load .ups x)
  | 0x11 => r.rm.toAddr?.map fun a => .store .ups a x
  | 0x12 =>
    match r.rm with
    | .reg n => some (.movhlps x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.movHalfLoad false false x)
  | 0x13 => r.rm.toAddr?.map fun a => .movHalfStore false false a x
  | 0x14 => some (.unpckp false .single x r.rm.toSrc)
  | 0x15 => some (.unpckp true .single x r.rm.toSrc)
  | 0x16 =>
    match r.rm with
    | .reg n => some (.movlhps x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.movHalfLoad true false x)
  | 0x17 => r.rm.toAddr?.map fun a => .movHalfStore true false a x
  | 0x18 =>
    match r.reg.toNat, r.rm.toAddr? with
    | 0, some a => some (.prefetch .nta a)
    | 1, some a => some (.prefetch .t0 a)
    | 2, some a => some (.prefetch .t1 a)
    | 3, some a => some (.prefetch .t2 a)
    | _, _ => none
  | 0x28 => r.rm.toAddr?.map (.load .aps x)
  | 0x29 => r.rm.toAddr?.map fun a => .store .aps a x
  | 0x2B => r.rm.toAddr?.map fun a => .storeNT .ps a x
  | 0x50 =>
    match r.rm with
    | .reg n => some (.movmsk .ps (Reg.ofBitVec r.reg) (XReg.ofBitVec n))
    | _ => none
  | 0x51 => some (.sqrtp .single x r.rm.toSrc)
  | 0x52 => some (.approx .rsqrtps x r.rm.toSrc)
  | 0x53 => some (.approx .rcpps x r.rm.toSrc)
  | 0x54 => match r.rm with | .rip d => some (.logicRip .and .single x d) | _ => none
  | 0x55 => match r.rm with | .rip d => some (.logicRip .andn .single x d) | _ => none
  | 0x56 => match r.rm with | .rip d => some (.logicRip .or .single x d) | _ => none
  | 0x57 => match r.rm with | .rip d => some (.logicRip .xor .single x d) | _ => none
  | 0x58 => some (.arithp .add .single x r.rm.toSrc)
  | 0x59 => some (.arithp .mul .single x r.rm.toSrc)
  | 0x5A => some (.cvtp .ps2pd x r.rm.toSrc)
  | 0x5B => some (.cvtp .dq2ps x r.rm.toSrc)
  | 0x5C => some (.arithp .sub .single x r.rm.toSrc)
  | 0x5D => some (.arithp .min .single x r.rm.toSrc)
  | 0x5E => some (.arithp .div .single x r.rm.toSrc)
  | 0x5F => some (.arithp .max .single x r.rm.toSrc)
  | 0xAE =>
    match r.reg.toNat, r.rm with
    | 5, .reg _ => some (.fence .lfence)
    | 6, .reg _ => some (.fence .mfence)
    | 7, .reg _ => some (.fence .sfence)
    | _, _ => none
  | 0xC2 =>
    match r.imm with
    | some b => (CmpPred.ofByte? b).map fun pred => .cmpp .single pred x r.rm.toSrc
    | none => none
  | 0xC6 => r.imm.map (.shufp .single x r.rm.toSrc)
  | _ => none

/-- The `F3` table. -/
def candF3 (r : PRaw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match r.opc.toNat with
  | 0x52 => some (.approx .rsqrtss x r.rm.toSrc)
  | 0x53 => some (.approx .rcpss x r.rm.toSrc)
  | 0x5B => some (.cvtp .tps2dq x r.rm.toSrc)
  | 0x6F =>
    match r.rm with
    | .reg n => some (.movReg .dqu x (XReg.ofBitVec n))
    | rm => rm.toAddr?.map (.load .dqu x)
  | 0x70 => r.imm.map (.pshuf .hw x r.rm.toSrc)
  | 0x7E => some (.movqLoad x r.rm.toSrc)
  | 0x7F => r.rm.toAddr?.map fun a => .store .dqu a x
  | 0xE6 => some (.cvtp .dq2pd x r.rm.toSrc)
  | _ => none

/-- The `F2` table. -/
def candF2 (r : PRaw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match r.opc.toNat with
  | 0x70 => r.imm.map (.pshuf .lw x r.rm.toSrc)
  | 0xE6 => some (.cvtp .pd2dq x r.rm.toSrc)
  | _ => none

/-- Read the opcode tables. `ofRaw` accepts the candidate only when its
encoding reproduces every field. -/
def candidate (r : PRaw) : Option Instr :=
  match r.pfx with
  | .p66 => cand66 r
  | .none => candNone r
  | .pF3 => candF3 r
  | .pF2 => candF2 r

def ofRaw (r : PRaw) : Option Instr :=
  match candidate r with
  | some i => if toRaw i = r then some i else none
  | none => none

section CandidateToRaw

local macro "cand_simp" : tactic =>
  `(tactic| simp [toRaw, mk, candidate, cand66, candNone, candF3, candF2, PIntOp.ofOpcode?, Addr.toOp, POperand.toAddr?, MovKind.pfx, MovKind.loadOpc, MovKind.storeOpc, RegMov.toMovKind,
    NTKind.pfx, NTKind.opc, MskKind.pfx, MskKind.opc, PShiftOp.opcode, PShiftOp.digit,
    PShiftOp.ofFields?, ShufKind.pfx, ArithOp.opcode, LogicOp.opcode, Precision.packedPrefix,
    CvtKind.pfx, CvtKind.opc, ApproxKind.pfx, ApproxKind.opc, FenceKind.digit,
    PrefetchHint.digit])

private theorem cand_load (k : MovKind) (dst : XReg) (a : Addr) :
    candidate (toRaw (.load k dst a)) = some (.load k dst a) := by
  cases k <;> cases a <;> cand_simp
private theorem cand_store (k : MovKind) (a : Addr) (src : XReg) :
    candidate (toRaw (.store k a src)) = some (.store k a src) := by
  cases k <;> cases a <;> cand_simp
private theorem cand_movReg (k : RegMov) (dst src : XReg) :
    candidate (toRaw (.movReg k dst src)) = some (.movReg k dst src) := by
  cases k <;> cand_simp
private theorem cand_storeNT (k : NTKind) (a : Addr) (src : XReg) :
    candidate (toRaw (.storeNT k a src)) = some (.storeNT k a src) := by
  cases k <;> cases a <;> cand_simp
private theorem cand_maskmovdqu (src msk : XReg) :
    candidate (toRaw (.maskmovdqu src msk)) = some (.maskmovdqu src msk) := by cand_simp
private theorem cand_movqLoad (dst : XReg) (src : Src) :
    candidate (toRaw (.movqLoad dst src)) = some (.movqLoad dst src) := by cand_simp
private theorem cand_movqStore (a : Addr) (src : XReg) :
    candidate (toRaw (.movqStore a src)) = some (.movqStore a src) := by cases a <;> cand_simp
private theorem cand_movdLoad (w : IntWidth) (dst : XReg) (a : Addr) :
    candidate (toRaw (.movdLoad w dst a)) = some (.movdLoad w dst a) := by cases a <;> cand_simp
private theorem cand_movdStore (w : IntWidth) (a : Addr) (src : XReg) :
    candidate (toRaw (.movdStore w a src)) = some (.movdStore w a src) := by cases a <;> cand_simp
private theorem cand_movHalfLoad (high pd : Bool) (dst : XReg) (a : Addr) :
    candidate (toRaw (.movHalfLoad high pd dst a)) = some (.movHalfLoad high pd dst a) := by
  cases high <;> cases pd <;> cases a <;> cand_simp
private theorem cand_movHalfStore (high pd : Bool) (a : Addr) (src : XReg) :
    candidate (toRaw (.movHalfStore high pd a src)) = some (.movHalfStore high pd a src) := by
  cases high <;> cases pd <;> cases a <;> cand_simp
private theorem cand_movhlps (dst src : XReg) :
    candidate (toRaw (.movhlps dst src)) = some (.movhlps dst src) := by cand_simp
private theorem cand_movlhps (dst src : XReg) :
    candidate (toRaw (.movlhps dst src)) = some (.movlhps dst src) := by cand_simp
private theorem cand_movmsk (k : MskKind) (dst : Reg) (src : XReg) :
    candidate (toRaw (.movmsk k dst src)) = some (.movmsk k dst src) := by cases k <;> cand_simp
private theorem cand_pinsrw (dst : XReg) (src : GSrc) (imm : Byte) :
    candidate (toRaw (.pinsrw dst src imm)) = some (.pinsrw dst src imm) := by cand_simp
private theorem cand_pextrw (dst : Reg) (src : XReg) (imm : Byte) :
    candidate (toRaw (.pextrw dst src imm)) = some (.pextrw dst src imm) := by cand_simp
private theorem cand_pint (op : PIntOp) (dst : XReg) (src : Src) :
    candidate (toRaw (.pint op dst src)) = some (.pint op dst src) := by
  simp [toRaw, mk, candidate, cand66, PIntOp.ofOpcode?_opcode]
private theorem cand_pshiftImm (op : PShiftOp) (dst : XReg) (imm : Byte) :
    candidate (toRaw (.pshiftImm op dst imm)) = some (.pshiftImm op dst imm) := by
  cases op <;> cand_simp
private theorem cand_pshuf (k : ShufKind) (dst : XReg) (src : Src) (imm : Byte) :
    candidate (toRaw (.pshuf k dst src imm)) = some (.pshuf k dst src imm) := by
  cases k <;> cand_simp
private theorem cand_arithp (op : ArithOp) (p : Precision) (dst : XReg) (src : Src) :
    candidate (toRaw (.arithp op p dst src)) = some (.arithp op p dst src) := by
  cases op <;> cases p <;> cand_simp
private theorem cand_sqrtp (p : Precision) (dst : XReg) (src : Src) :
    candidate (toRaw (.sqrtp p dst src)) = some (.sqrtp p dst src) := by cases p <;> cand_simp
private theorem cand_cmpp (p : Precision) (pred : CmpPred) (dst : XReg) (src : Src) :
    candidate (toRaw (.cmpp p pred dst src)) = some (.cmpp p pred dst src) := by
  cases p <;> cand_simp
private theorem cand_logicRip (op : LogicOp) (p : Precision) (dst : XReg) (d : BitVec 32) :
    candidate (toRaw (.logicRip op p dst d)) = some (.logicRip op p dst d) := by
  cases op <;> cases p <;> cand_simp
private theorem cand_unpckp (high : Bool) (p : Precision) (dst : XReg) (src : Src) :
    candidate (toRaw (.unpckp high p dst src)) = some (.unpckp high p dst src) := by
  cases high <;> cases p <;> cand_simp
private theorem cand_shufp (p : Precision) (dst : XReg) (src : Src) (imm : Byte) :
    candidate (toRaw (.shufp p dst src imm)) = some (.shufp p dst src imm) := by
  cases p <;> cand_simp
private theorem cand_cvtp (k : CvtKind) (dst : XReg) (src : Src) :
    candidate (toRaw (.cvtp k dst src)) = some (.cvtp k dst src) := by cases k <;> cand_simp
private theorem cand_approx (k : ApproxKind) (dst : XReg) (src : Src) :
    candidate (toRaw (.approx k dst src)) = some (.approx k dst src) := by cases k <;> cand_simp
private theorem cand_fence (k : FenceKind) :
    candidate (toRaw (.fence k)) = some (.fence k) := by cases k <;> cand_simp
private theorem cand_prefetch (h : PrefetchHint) (a : Addr) :
    candidate (toRaw (.prefetch h a)) = some (.prefetch h a) := by
  cases h <;> cases a <;> cand_simp

theorem candidate_toRaw (i : Instr) : candidate (toRaw i) = some i := by
  cases i
  · apply cand_load
  · apply cand_store
  · apply cand_movReg
  · apply cand_storeNT
  · apply cand_maskmovdqu
  · apply cand_movqLoad
  · apply cand_movqStore
  · apply cand_movdLoad
  · apply cand_movdStore
  · apply cand_movHalfLoad
  · apply cand_movHalfStore
  · apply cand_movhlps
  · apply cand_movlhps
  · apply cand_movmsk
  · apply cand_pinsrw
  · apply cand_pextrw
  · apply cand_pint
  · apply cand_pshiftImm
  · apply cand_pshuf
  · apply cand_arithp
  · apply cand_sqrtp
  · apply cand_cmpp
  · apply cand_logicRip
  · apply cand_unpckp
  · apply cand_shufp
  · apply cand_cvtp
  · apply cand_approx
  · apply cand_fence
  · apply cand_prefetch

end CandidateToRaw

@[simp] theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  simp [ofRaw, candidate_toRaw]

theorem toRaw_of_ofRaw {r : PRaw} {i : Instr} (h : ofRaw r = some i) : toRaw i = r := by
  unfold ofRaw at h
  split at h
  · split_ifs at h with heq
    cases h
    exact heq
  · cases h

theorem toRaw_wellFormed (i : Instr) : (toRaw i).WellFormed := by
  unfold PRaw.WellFormed
  cases i with
  | load k | store k => cases k <;> rfl
  | movReg k => cases k <;> rfl
  | storeNT k => cases k <;> rfl
  | movmsk k => cases k <;> rfl
  | movHalfLoad high pd | movHalfStore high pd => cases high <;> rfl
  | pint op => cases op <;> rfl
  | pshiftImm op => cases op <;> rfl
  | arithp op => cases op <;> rfl
  | logicRip op => cases op <;> rfl
  | unpckp high => cases high <;> rfl
  | cvtp k => cases k <;> rfl
  | approx k => cases k <;> rfl
  | _ => rfl

/-! ## Encoder and decoder -/

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-- Decode one instruction from the start of `bytes`. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match PRaw.parse bytes with
  | some (r, rest) => (ofRaw r).map fun i => (i, bytes.length - rest.length)
  | none => none

@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  simp [decode, encode, PRaw.parse_bytes _ (toRaw_wellFormed i)]

@[simp] theorem decode_encode (i : Instr) : decode (encode i) = some (i, (encode i).length) := by
  simpa using decode_encode_append i []

theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ n ≤ bytes.length ∧ bytes = encode i ++ bytes.drop n := by
  unfold decode at h
  split at h
  next r rest hp =>
    obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hb : bytes = encode j ++ rest := by
      rw [PRaw.parse_sound hp, encode, toRaw_of_ofRaw hj]
    have hn : bytes.length - rest.length = (encode j).length := by
      rw [hb, List.length_append]; omega
    refine ⟨hn, by omega, ?_⟩
    rw [hn, hb, List.drop_left]
  next => cases h

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, -, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

theorem decode_unique {bytes : List Byte} {i j : Instr} (hi : encode i <+: bytes)
    (hj : encode j <+: bytes) : i = j := by
  obtain ⟨ri, rfl⟩ := hi
  obtain ⟨rj, hj⟩ := hj
  have h := decode_encode_append i ri
  rw [← hj, decode_encode_append] at h
  exact (Prod.mk.inj (Option.some.inj h)).1.symm

theorem encode_injective : Function.Injective encode := by
  intro i j h
  exact decode_unique (bytes := encode i) (List.prefix_refl _) (h ▸ List.prefix_refl _)

theorem decode_append {bytes more : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

theorem encode_length_le (i : Instr) : (encode i).length ≤ 11 := PRaw.bytes_length_le _

theorem encode_length_ge (i : Instr) : 3 ≤ (encode i).length := PRaw.bytes_length_ge _

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
    simp
  decode_encode_append := decode_encode_append

end Silmaril.X86.Features.SsePacked
