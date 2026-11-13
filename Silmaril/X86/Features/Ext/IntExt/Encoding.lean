module

public import Silmaril.X86.Features.Ext.IntExt.Syntax
public import Silmaril.X86.Ext.Encoding
public import Silmaril.Machine.Decoder

/-!
# Integer extensions: byte codec

A verified encoder and prefix-code decoder for `IntExt.Instr`, written from
the Intel SDM Vol. 2A, Chapter 2 (legacy, REX and VEX formats) and the opcode
lines of the instruction pages.

## Layers

1. **Raw fields** (`Raw`): an optional FS override (`64`), then either a legacy
   head (an optional `66`/`F2`/`F3` prefix, an optional REX prefix and the
   one-byte, `0F`, `0F 38` or `0F 3A` map) or a three-byte VEX prefix
   (`C4 RXBmmmmm WvvvvLpp`, with L = 0), the opcode, ModRM with SIB and
   displacement (Ext's operand encoding, `Ext.encodeRM`), and an immediate.
   `parse_bytes` is the round trip of every well-formed `Raw`.
2. **Instructions.** `toRaw` is the opcode table, `ofRaw` reads it backwards
   (`ofRaw_toRaw`).
3. **Canonical decoding.** `decode` parses, reads the instruction and then
   accepts only if the input begins with that instruction's canonical
   encoding. `canonicalDecoder` shows that this construction satisfies the
   five `Machine.Decoder` laws for any encoder that the guess function
   recovers; `byteDecoder` is the result.

| Instruction | Encoding |
| --- | --- |
| `adc`/`sbb r/m, r` | `REX? 11`/`19 /r` |
| `adc`/`sbb r, r/m` | `REX? 13`/`1B /r` |
| `adc`/`sbb r/m, imm32` / `imm8` | `REX? 81 /2`/`/3 id`, `REX? 83 /2`/`/3 ib` |
| `adc`/`sbb eAX/rAX, imm32` | `REX.W? 15`/`1D id` |
| `imul r, r/m, imm32` / `imm8` | `REX? 69 /r id`, `REX? 6B /r ib` |
| `imul r/m` | `REX? F7 /5` |
| `test r/m, imm32` | `REX? F7 /0 id` |
| `push imm32` / `imm8` | `68 id`, `6A ib` |
| `bsf`/`bsr r, r/m` | `REX? 0F BC`/`BD /r` |
| `bt`/`bts`/`btr`/`btc r/m, r` | `REX? 0F A3`/`AB`/`B3`/`BB /r` |
| `bt`/`bts`/`btr`/`btc r/m, imm8` | `REX? 0F BA /4`–`/7 ib` |
| `shld r/m, r, imm8` / `cl` | `REX? 0F A4 /r ib`, `REX? 0F A5 /r` |
| `shrd r/m, r, imm8` / `cl` | `REX? 0F AC /r ib`, `REX? 0F AD /r` |
| `xadd r, r` | `REX? 0F C1 /r` (`mod = 11`) |
| `cmpxchg r, r` | `REX? 0F B1 /r` (`mod = 11`) |
| `adcx`/`adox r, r/m` | `66`/`F3 REX? 0F 38 F6 /r` |
| `movbe r, m` / `m, r` | `REX? 0F 38 F0`/`F1 /r` |
| `andn`, `bextr`, `bzhi` | `VEX.LZ.0F38.W F2`/`F7`/`F5 /r` |
| `blsr`/`blsmsk`/`blsi` | `VEX.LZ.0F38.W F3 /1`/`/2`/`/3` |
| `pdep`/`pext` | `VEX.LZ.F2`/`F3.0F38.W F5 /r` |
| `mulx` | `VEX.LZ.F2.0F38.W F6 /r` |
| `sarx`/`shlx`/`shrx` | `VEX.LZ.F3`/`66`/`F2.0F38.W F7 /r` |
| `rorx` | `VEX.LZ.F2.0F3A.W F0 /r ib` |

W (REX.W or VEX.W) selects 64-bit operand size. REX is emitted exactly when
one of its bits is set, the three-byte VEX form `C4` is the only VEX form
(the BMI maps are not reachable with `C5`), and unused VEX fields (`vvvv` of
RORX, `R` of the BLS group) take their canonical value. These are the choices
of the GNU assembler; the vector files check the encoder against `as` byte for
byte. `none` means "outside this canonical subset", not "invalid on hardware".
-/

@[expose] public section

namespace Silmaril.X86.Features.IntExt

open Silmaril.X86 (Byte Reg imm32Bytes)
open Silmaril.X86.Ext (Sz RM Mem Rex ModRM SIB Disp Imm ImmKind ModrmPart modrmBytes rexBytes
  segBytes encodeRM decodeRM mkReg hiBit mkRex isRex PResult pModrm pImm ModrmOk)

/-! ## Canonical decoders from a guess function -/

section Generic

variable {α : Type} (encode : α → List Byte) (guess : List Byte → Option α)

/-- Decode by guessing an instruction and accepting it only when the input
begins with its encoding. -/
def guessDecode (bytes : List Byte) : Option (α × Nat) :=
  match guess bytes with
  | some i => if bytes.take (encode i).length = encode i then some (i, (encode i).length) else none
  | none => none

variable {encode guess}

theorem guessDecode_sound {bytes : List Byte} {i : α} {n : Nat}
    (h : guessDecode encode guess bytes = some (i, n)) :
    n = (encode i).length ∧ bytes.take n = encode i := by
  unfold guessDecode at h
  split at h
  · split_ifs at h with ht
    cases h
    exact ⟨rfl, ht⟩
  · cases h

/-- A guess that recovers every encoding, whatever follows it, gives a decoder
satisfying the `Machine.Decoder` laws. -/
def canonicalDecoder (hne : ∀ i, encode i ≠ [])
    (hg : ∀ i rest, guess (encode i ++ rest) = some i) : Machine.Decoder α where
  decode := guessDecode encode guess
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := guessDecode_sound h
    exact List.length_pos_iff.mpr (hne _)
  decode_length_le {bytes i n} h := by
    obtain ⟨rfl, ht⟩ := guessDecode_sound h
    have := congrArg List.length ht
    simp only [List.length_take] at this
    omega
  decode_append {bytes i n} extra h := by
    obtain ⟨rfl, ht⟩ := guessDecode_sound h
    have hle : (encode i).length ≤ bytes.length := by
      have := congrArg List.length ht
      simp only [List.length_take] at this
      omega
    have hb : bytes = encode i ++ bytes.drop (encode i).length := by
      conv_lhs => rw [← List.take_append_drop (encode i).length bytes]
      rw [ht]
    unfold guessDecode
    rw [hb, List.append_assoc, hg]
    simp
  decode_take {bytes i n} h := by
    obtain ⟨rfl, ht⟩ := guessDecode_sound h
    rw [ht]
    unfold guessDecode
    have := hg i []
    rw [List.append_nil] at this
    simp [this]
  decode_encode_append i rest := by
    unfold guessDecode
    simp [hg]

end Generic

/-! ## Raw fields -/

/-- A legacy prefix, or the implied prefix of a VEX `pp` field. -/
inductive Pfx where
  | none | p66 | pF2 | pF3
  deriving DecidableEq, Repr

def Pfx.bytes : Pfx → List Byte
  | .none => [] | .p66 => [0x66] | .pF2 => [0xF2] | .pF3 => [0xF3]

/-- The VEX `pp` field. -/
def Pfx.pp : Pfx → BitVec 2
  | .none => 0 | .p66 => 1 | .pF3 => 2 | .pF2 => 3

def Pfx.ofPp (b : BitVec 2) : Pfx :=
  if b = 0 then .none else if b = 1 then .p66 else if b = 2 then .pF3 else .pF2

@[simp] theorem Pfx.ofPp_pp (p : Pfx) : Pfx.ofPp p.pp = p := by cases p <;> rfl

/-- The opcode map. -/
inductive Map where
  | one | m0F | m0F38 | m0F3A
  deriving DecidableEq, Repr

/-- The escape bytes of a legacy encoding. -/
def Map.bytes : Map → List Byte
  | .one => [] | .m0F => [0x0F] | .m0F38 => [0x0F, 0x38] | .m0F3A => [0x0F, 0x3A]

/-- The VEX `mmmmm` field. -/
def Map.vexCode : Map → BitVec 5
  | .one => 0 | .m0F => 1 | .m0F38 => 2 | .m0F3A => 3

/-- The fields of a VEX prefix, with R, X, B and vvvv in their true (not
inverted) sense. -/
structure Vex where
  pp : Pfx
  r : Bool
  x : Bool
  b : Bool
  w : Bool
  vvvv : BitVec 4
  deriving DecidableEq, Repr

/-- A legacy or a VEX head. -/
inductive Enc where
  | legacy (pfx : Pfx) (rex : Option Rex)
  | vex (v : Vex)
  deriving DecidableEq, Repr

/-- The second byte of a three-byte VEX prefix: `R̄ X̄ B̄ mmmmm`. -/
def vexByte1 (r x b : Bool) (m : Map) : Byte :=
  BitVec.ofBool (!r) ++ BitVec.ofBool (!x) ++ BitVec.ofBool (!b) ++ m.vexCode

/-- The third byte: `W v̄v̄v̄v̄ L pp`, with L = 0. -/
def vexByte2 (w : Bool) (vvvv : BitVec 4) (pp : Pfx) : Byte :=
  BitVec.ofBool w ++ ~~~vvvv ++ 0#1 ++ pp.pp

def Enc.bytes : Enc → Map → List Byte
  | .legacy p rex, m => p.bytes ++ rexBytes rex ++ m.bytes
  | .vex v, m => [0xC4, vexByte1 v.r v.x v.b m, vexByte2 v.w v.vvvv v.pp]

/-- The raw fields of one instruction. -/
structure Raw where
  fs : Bool
  enc : Enc
  map : Map
  opc : Byte
  modrm : Option ModrmPart
  imm : Imm
  deriving DecidableEq, Repr

def Raw.bytes (r : Raw) : List Byte :=
  segBytes r.fs ++ r.enc.bytes r.map ++ r.opc :: (modrmBytes r.modrm ++ r.imm.bytes)

/-- The immediate of an opcode: none, an imm8, an imm32, or (for `F7`) an
imm32 exactly when ModRM `reg` is 0 (TEST). -/
inductive ImmSpec where
  | none | i8 | i32 | f7
  deriving DecidableEq, Repr

def ImmSpec.kind : ImmSpec → Option ModrmPart → ImmKind
  | .none, _ => .none
  | .i8, _ => .i8
  | .i32, _ => .i32
  | .f7, some (m, _, _) => if m.reg = 0 then .i32 else .none
  | .f7, Option.none => .none

/-- Whether an opcode takes ModRM, and its immediate. The one-byte and `0F`
tables list only the opcodes of the lane; `0F 38` and `0F 3A` follow the
architectural rule (ModRM always; an imm8 exactly in `0F 3A`). -/
def shape : Map → Byte → Option (Bool × ImmSpec)
  | .one, b =>
    if b = 0x11 ∨ b = 0x13 ∨ b = 0x19 ∨ b = 0x1B then some (true, .none)
    else if b = 0x81 ∨ b = 0x69 then some (true, .i32)
    else if b = 0x83 ∨ b = 0x6B then some (true, .i8)
    else if b = 0xF7 then some (true, .f7)
    else if b = 0x15 ∨ b = 0x1D ∨ b = 0x68 then some (false, .i32)
    else if b = 0x6A then some (false, .i8)
    else none
  | .m0F, b =>
    if b = 0xBC ∨ b = 0xBD ∨ b = 0xA3 ∨ b = 0xAB ∨ b = 0xB3 ∨ b = 0xBB ∨ b = 0xA5 ∨ b = 0xAD ∨
        b = 0xC1 ∨ b = 0xB1 then some (true, .none)
    else if b = 0xBA ∨ b = 0xA4 ∨ b = 0xAC then some (true, .i8)
    else none
  | .m0F38, _ => some (true, .none)
  | .m0F3A, _ => some (true, .i8)

/-! ## Parsing -/

def parseSeg : List Byte → Bool × List Byte
  | b :: t => if b = 0x64 then (true, t) else (false, b :: t)
  | [] => (false, [])

def parsePfx : List Byte → Pfx × List Byte
  | b :: t =>
    if b = 0x66 then (.p66, t) else if b = 0xF2 then (.pF2, t)
    else if b = 0xF3 then (.pF3, t) else (.none, b :: t)
  | [] => (.none, [])

def parseRex : List Byte → Option Rex × List Byte
  | b :: t => if isRex b then (some (Rex.ofByte b), t) else (none, b :: t)
  | [] => (none, [])

def parseMap : List Byte → Map × List Byte
  | b :: t =>
    if b = 0x0F then
      match t with
      | c :: u => if c = 0x38 then (.m0F38, u) else if c = 0x3A then (.m0F3A, u) else (.m0F, c :: u)
      | [] => (.m0F, [])
    else (.one, b :: t)
  | [] => (.one, [])

/-- The two VEX payload bytes after `C4`. -/
def parseVex : List Byte → Option (Vex × Map × List Byte)
  | b1 :: b2 :: t =>
    if b2.getLsbD 2 then none
    else
      let m := b1.extractLsb' 0 5
      let v : Vex := ⟨Pfx.ofPp (b2.extractLsb' 0 2), !b1.getLsbD 7, !b1.getLsbD 6, !b1.getLsbD 5,
        b2.getLsbD 7, ~~~(b2.extractLsb' 3 4)⟩
      if m = 2 then some (v, .m0F38, t) else if m = 3 then some (v, .m0F3A, t) else none
  | _ => none

/-- The legacy or VEX head, after any segment override. -/
def parseHead : List Byte → Option (Enc × Map × List Byte)
  | b :: t =>
    if b = 0xC4 then (parseVex t).map fun r => (.vex r.1, r.2.1, r.2.2)
    else
      let a := parsePfx (b :: t)
      let c := parseRex a.2
      let d := parseMap c.2
      some (.legacy a.1 c.1, d.1, d.2)
  | [] => none

/-- Read the raw fields of one instruction, with the bytes after it. -/
def parse (bytes : List Byte) : Option (Raw × List Byte) :=
  match parseHead (parseSeg bytes).2 with
  | none => none
  | some (enc, map, u) =>
    match u with
    | [] => none
    | opc :: u =>
      match shape map opc with
      | none => none
      | some (hm, spec) =>
        match pModrm hm u with
        | .ok mp u' =>
          match pImm (spec.kind mp) u' with
          | .ok imm u'' => some (⟨(parseSeg bytes).1, enc, map, opc, mp, imm⟩, u'')
          | _ => none
        | _ => none

/-! ## Round trip of the raw layer -/

/-- An opcode byte that cannot be read as part of the head. -/
def OpcOk : Map → Byte → Prop
  | .one, b => b ≠ 0x0F ∧ b ≠ 0x66 ∧ b ≠ 0xF2 ∧ b ≠ 0xF3 ∧ b ≠ 0xC4 ∧ b ≠ 0x64 ∧ isRex b = false
  | .m0F, b => b ≠ 0x38 ∧ b ≠ 0x3A
  | _, _ => True

private theorem opcOk_one : ∀ b : Byte, (shape .one b).isSome = true →
    b ≠ 0x0F ∧ b ≠ 0x66 ∧ b ≠ 0xF2 ∧ b ≠ 0xF3 ∧ b ≠ 0xC4 ∧ b ≠ 0x64 ∧ isRex b = false := by
  decide

private theorem opcOk_0F : ∀ b : Byte, (shape .m0F b).isSome = true → b ≠ 0x38 ∧ b ≠ 0x3A := by
  decide

theorem opcOk_of_shape {m : Map} {b : Byte} (h : (shape m b).isSome = true) : OpcOk m b := by
  cases m
  · exact opcOk_one b h
  · exact opcOk_0F b h
  · trivial
  · trivial

/-- The raw fields are consistent: the opcode's shape, ModRM and immediate
agree, and VEX selects the `0F 38` or `0F 3A` map. -/
def Raw.WF (r : Raw) : Prop :=
  (∃ hm spec, shape r.map r.opc = some (hm, spec) ∧ ModrmOk hm r.modrm ∧
    r.imm.kind = spec.kind r.modrm) ∧
  (∀ v, r.enc = .vex v → r.map = .m0F38 ∨ r.map = .m0F3A)

private theorem rex_ne {c : Byte} (hc : isRex c = false) (x : Rex) : x.byte ≠ c := by
  intro h
  have := Ext.isRex_byte x
  rw [h, hc] at this
  cases this

private theorem isRex_66 : isRex (0x66 : Byte) = false := by decide
private theorem isRex_F2 : isRex (0xF2 : Byte) = false := by decide
private theorem isRex_F3 : isRex (0xF3 : Byte) = false := by decide
private theorem isRex_0F : isRex (0x0F : Byte) = false := by decide
private theorem isRex_C4 : isRex (0xC4 : Byte) = false := by decide
private theorem isRex_64 : isRex (0x64 : Byte) = false := by decide

private theorem vexByte1_fields (r x b : Bool) (m : Map) :
    (vexByte1 r x b m).extractLsb' 0 5 = m.vexCode ∧ (vexByte1 r x b m).getLsbD 7 = !r ∧
      (vexByte1 r x b m).getLsbD 6 = !x ∧ (vexByte1 r x b m).getLsbD 5 = !b := by
  cases m <;> revert r x b <;> decide

private theorem vexByte2_fields (w : Bool) (vvvv : BitVec 4) (pp : Pfx) :
    (vexByte2 w vvvv pp).getLsbD 2 = false ∧ (vexByte2 w vvvv pp).getLsbD 7 = w ∧
      ~~~((vexByte2 w vvvv pp).extractLsb' 3 4) = vvvv ∧
      (vexByte2 w vvvv pp).extractLsb' 0 2 = pp.pp := by
  cases pp <;> revert w vvvv <;> decide

/-- The head parser reads back every head followed by an admissible opcode. -/
theorem parseHead_bytes (enc : Enc) (map : Map) (opc : Byte) (rest : List Byte)
    (hopc : OpcOk map opc) (hv : ∀ v, enc = .vex v → map = .m0F38 ∨ map = .m0F3A) :
    parseHead (enc.bytes map ++ opc :: rest) = some (enc, map, opc :: rest) := by
  cases enc with
  | vex v =>
    obtain ⟨h1, h2, h3, h4⟩ := vexByte1_fields v.r v.x v.b map
    obtain ⟨g1, g2, g3, g4⟩ := vexByte2_fields v.w v.vvvv v.pp
    rcases hv v rfl with rfl | rfl <;>
    · simp only [Enc.bytes, List.cons_append, parseHead, ↓reduceIte, parseVex, g1, Bool.false_eq_true,
        h1, h2, h3, h4, g2, g3, g4, Pfx.ofPp_pp, Bool.not_not]
      simp [Map.vexCode]
  | legacy p rex =>
    have hrex : ∀ x : Rex, x.byte ≠ 0x66 ∧ x.byte ≠ 0xF2 ∧ x.byte ≠ 0xF3 ∧ x.byte ≠ 0x0F ∧
        x.byte ≠ 0xC4 := fun x =>
      ⟨rex_ne isRex_66 x, rex_ne isRex_F2 x, rex_ne isRex_F3 x, rex_ne isRex_0F x,
        rex_ne isRex_C4 x⟩
    cases map <;> simp only [OpcOk] at hopc <;> cases p <;> rcases rex with _ | x <;>
      simp_all [Enc.bytes, Pfx.bytes, rexBytes, Map.bytes, parseHead, parsePfx, parseRex,
        parseMap, Ext.isRex_byte]

/-- The first byte of a head is never the FS override. -/
theorem parseSeg_bytes (fs : Bool) (enc : Enc) (map : Map) (opc : Byte) (rest : List Byte)
    (hopc : OpcOk map opc) :
    parseSeg (segBytes fs ++ (enc.bytes map ++ opc :: rest)) = (fs, enc.bytes map ++ opc :: rest) := by
  cases fs
  · have hrex := rex_ne isRex_64
    cases enc with
    | vex v => simp [Enc.bytes, parseSeg]
    | legacy p rex =>
      cases map <;> simp only [OpcOk] at hopc <;> cases p <;> rcases rex with _ | x <;>
        simp_all [Enc.bytes, Pfx.bytes, rexBytes, Map.bytes, parseSeg]
  · simp [parseSeg]

theorem parse_bytes {r : Raw} (h : r.WF) (rest : List Byte) :
    parse (r.bytes ++ rest) = some (r, rest) := by
  obtain ⟨⟨hm, spec, hs, hmo, hi⟩, hv⟩ := h
  have hopc : OpcOk r.map r.opc := opcOk_of_shape (by simp [hs])
  unfold parse Raw.bytes
  simp only [List.append_assoc, List.cons_append]
  rw [parseSeg_bytes _ _ _ _ _ hopc, parseHead_bytes _ _ _ _ hopc hv]
  simp only [hs]
  rw [Ext.pModrm_bytes hmo]
  simp only
  rw [← hi, Ext.pImm_bytes]

/-! ## The opcode table -/

def CarryOp.opcode : CarryOp → Byte | .adc => 0x11 | .sbb => 0x19
def CarryOp.opcodeR : CarryOp → Byte | .adc => 0x13 | .sbb => 0x1B
def CarryOp.opcodeA : CarryOp → Byte | .adc => 0x15 | .sbb => 0x1D
def CarryOp.digit : CarryOp → BitVec 3 | .adc => 2 | .sbb => 3

def CarryOp.ofDigit (d : BitVec 3) : Option CarryOp :=
  if d = 2 then some .adc else if d = 3 then some .sbb else none

def BitOp.opcode : BitOp → Byte | .bt => 0xA3 | .bts => 0xAB | .btr => 0xB3 | .btc => 0xBB
def BitOp.digit : BitOp → BitVec 3 | .bt => 4 | .bts => 5 | .btr => 6 | .btc => 7

def BitOp.ofDigit (d : BitVec 3) : Option BitOp :=
  if d = 4 then some .bt else if d = 5 then some .bts else if d = 6 then some .btr
  else if d = 7 then some .btc else none

def BlsOp.digit : BlsOp → BitVec 3 | .blsr => 1 | .blsmsk => 2 | .blsi => 3

def BlsOp.ofDigit (d : BitVec 3) : Option BlsOp :=
  if d = 1 then some .blsr else if d = 2 then some .blsmsk else if d = 3 then some .blsi else none

/-- The VEX `pp` and `0F 38` opcode of a three-operand form. -/
def Vop.pfx : Vop → Pfx
  | .andn | .bextr | .bzhi => .none
  | .pdep | .shrx | .mulx => .pF2
  | .pext | .sarx => .pF3
  | .shlx => .p66

def Vop.opcode : Vop → Byte
  | .andn => 0xF2 | .bextr => 0xF7 | .bzhi => 0xF5 | .pdep => 0xF5 | .pext => 0xF5
  | .sarx => 0xF7 | .shlx => 0xF7 | .shrx => 0xF7 | .mulx => 0xF6

/-- The second opcode byte of SHLD/SHRD. -/
def shdOpcode (right : Bool) : ShdCount → Byte
  | .imm _ => if right then 0xAC else 0xA4
  | .cl => if right then 0xAD else 0xA5

def ShdCount.imm' : ShdCount → Imm
  | .imm n => .i8 n
  | .cl => .none

/-- A legacy form with a ModRM operand. -/
def legacyRaw (pfx : Pfx) (w : Bool) (map : Map) (opc : Byte) (reg : BitVec 3) (rHi : Bool)
    (op : RM) (imm : Imm) : Raw :=
  ⟨op.isFs, .legacy pfx (mkRex w rHi (encodeRM op).x (encodeRM op).b false), map, opc,
    some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩, (encodeRM op).sib, (encodeRM op).disp), imm⟩

/-- A VEX form with a ModRM operand. -/
def vexRaw (pp : Pfx) (w : Bool) (map : Map) (opc : Byte) (reg : BitVec 3) (rHi : Bool)
    (vvvv : BitVec 4) (op : RM) (imm : Imm) : Raw :=
  ⟨op.isFs, .vex ⟨pp, rHi, (encodeRM op).x, (encodeRM op).b, w, vvvv⟩, map, opc,
    some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩, (encodeRM op).sib, (encodeRM op).disp), imm⟩

/-- The raw fields of each instruction. -/
def toRaw : Instr → Raw
  | .carry op sz dst src => legacyRaw .none sz.w .one op.opcode src.lo (hiBit src) dst .none
  | .carryR op sz dst src => legacyRaw .none sz.w .one op.opcodeR dst.lo (hiBit dst) src .none
  | .carryI op sz dst imm => legacyRaw .none sz.w .one 0x81 op.digit false dst (.i32 imm)
  | .carryI8 op sz dst imm => legacyRaw .none sz.w .one 0x83 op.digit false dst (.i8 imm)
  | .carryA op sz imm =>
    ⟨false, .legacy .none (mkRex sz.w false false false false), .one, op.opcodeA, none, .i32 imm⟩
  | .imulI sz dst src imm => legacyRaw .none sz.w .one 0x69 dst.lo (hiBit dst) src (.i32 imm)
  | .imulI8 sz dst src imm => legacyRaw .none sz.w .one 0x6B dst.lo (hiBit dst) src (.i8 imm)
  | .imul1 sz src => legacyRaw .none sz.w .one 0xF7 5 false src .none
  | .testI sz dst imm => legacyRaw .none sz.w .one 0xF7 0 false dst (.i32 imm)
  | .pushI imm => ⟨false, .legacy .none none, .one, 0x68, none, .i32 imm⟩
  | .pushI8 imm => ⟨false, .legacy .none none, .one, 0x6A, none, .i8 imm⟩
  | .scan rev sz dst src =>
    legacyRaw .none sz.w .m0F (if rev then 0xBD else 0xBC) dst.lo (hiBit dst) src .none
  | .bit op sz dst src => legacyRaw .none sz.w .m0F op.opcode src.lo (hiBit src) dst .none
  | .bitI op sz dst imm => legacyRaw .none sz.w .m0F 0xBA op.digit false dst (.i8 imm)
  | .shd right sz dst src count =>
    legacyRaw .none sz.w .m0F (shdOpcode right count) src.lo (hiBit src) dst count.imm'
  | .xadd sz dst src => legacyRaw .none sz.w .m0F 0xC1 src.lo (hiBit src) (.reg dst) .none
  | .cmpxchg sz dst src => legacyRaw .none sz.w .m0F 0xB1 src.lo (hiBit src) (.reg dst) .none
  | .adx op sz dst src =>
    legacyRaw (match op with | .adcx => .p66 | .adox => .pF3) sz.w .m0F38 0xF6 dst.lo (hiBit dst)
      src .none
  | .movbeLoad sz dst src => legacyRaw .none sz.w .m0F38 0xF0 dst.lo (hiBit dst) (.mem src) .none
  | .movbeStore sz dst src => legacyRaw .none sz.w .m0F38 0xF1 src.lo (hiBit src) (.mem dst) .none
  | .vop op sz dst v src =>
    vexRaw op.pfx sz.w .m0F38 op.opcode dst.lo (hiBit dst) v.toBitVec src .none
  | .bls op sz dst src => vexRaw .none sz.w .m0F38 0xF3 op.digit false dst.toBitVec src .none
  | .rorx sz dst src imm => vexRaw .pF2 sz.w .m0F3A 0xF0 dst.lo (hiBit dst) 0 src (.i8 imm)

/-- The legacy forms with a ModRM operand, by prefix, map and opcode. -/
def ofLegacy (p : Pfx) (map : Map) (opc : Byte) (sz : Sz) (digit : BitVec 3) (reg : Reg)
    (op : RM) (imm : Imm) : Option Instr :=
  match p, map with
  | .none, .one =>
    if opc = 0x11 then some (.carry .adc sz op reg)
    else if opc = 0x19 then some (.carry .sbb sz op reg)
    else if opc = 0x13 then some (.carryR .adc sz reg op)
    else if opc = 0x1B then some (.carryR .sbb sz reg op)
    else if opc = 0x81 then
      match imm with
      | .i32 v => (CarryOp.ofDigit digit).map fun o => .carryI o sz op v
      | _ => none
    else if opc = 0x83 then
      match imm with
      | .i8 v => (CarryOp.ofDigit digit).map fun o => .carryI8 o sz op v
      | _ => none
    else if opc = 0x69 then
      match imm with
      | .i32 v => some (.imulI sz reg op v)
      | _ => none
    else if opc = 0x6B then
      match imm with
      | .i8 v => some (.imulI8 sz reg op v)
      | _ => none
    else if opc = 0xF7 then
      if digit = 5 then some (.imul1 sz op)
      else if digit = 0 then
        match imm with
        | .i32 v => some (.testI sz op v)
        | _ => none
      else none
    else none
  | .none, .m0F =>
    if opc = 0xBC then some (.scan false sz reg op)
    else if opc = 0xBD then some (.scan true sz reg op)
    else if opc = 0xA3 then some (.bit .bt sz op reg)
    else if opc = 0xAB then some (.bit .bts sz op reg)
    else if opc = 0xB3 then some (.bit .btr sz op reg)
    else if opc = 0xBB then some (.bit .btc sz op reg)
    else if opc = 0xBA then
      match imm with
      | .i8 v => (BitOp.ofDigit digit).map fun o => .bitI o sz op v
      | _ => none
    else if opc = 0xA4 then
      match imm with
      | .i8 v => some (.shd false sz op reg (.imm v))
      | _ => none
    else if opc = 0xAC then
      match imm with
      | .i8 v => some (.shd true sz op reg (.imm v))
      | _ => none
    else if opc = 0xA5 then some (.shd false sz op reg .cl)
    else if opc = 0xAD then some (.shd true sz op reg .cl)
    else if opc = 0xC1 then
      match op with
      | .reg d => some (.xadd sz d reg)
      | .mem _ => none
    else if opc = 0xB1 then
      match op with
      | .reg d => some (.cmpxchg sz d reg)
      | .mem _ => none
    else none
  | .none, .m0F38 =>
    if opc = 0xF0 then
      match op with
      | .mem m => some (.movbeLoad sz reg m)
      | .reg _ => none
    else if opc = 0xF1 then
      match op with
      | .mem m => some (.movbeStore sz m reg)
      | .reg _ => none
    else none
  | .p66, .m0F38 => if opc = 0xF6 then some (.adx .adcx sz reg op) else none
  | .pF3, .m0F38 => if opc = 0xF6 then some (.adx .adox sz reg op) else none
  | _, _ => none

/-- The VEX forms, by `pp`, map and opcode. -/
def ofVex (p : Pfx) (map : Map) (opc : Byte) (sz : Sz) (digit : BitVec 3) (reg v : Reg)
    (op : RM) (imm : Imm) : Option Instr :=
  match map with
  | .m0F38 =>
    match p with
    | .none =>
      if opc = 0xF2 then some (.vop .andn sz reg v op)
      else if opc = 0xF7 then some (.vop .bextr sz reg v op)
      else if opc = 0xF5 then some (.vop .bzhi sz reg v op)
      else if opc = 0xF3 then (BlsOp.ofDigit digit).map fun o => .bls o sz v op
      else none
    | .pF2 =>
      if opc = 0xF5 then some (.vop .pdep sz reg v op)
      else if opc = 0xF7 then some (.vop .shrx sz reg v op)
      else if opc = 0xF6 then some (.vop .mulx sz reg v op)
      else none
    | .pF3 =>
      if opc = 0xF5 then some (.vop .pext sz reg v op)
      else if opc = 0xF7 then some (.vop .sarx sz reg v op)
      else none
    | .p66 => if opc = 0xF7 then some (.vop .shlx sz reg v op) else none
  | .m0F3A =>
    if p = .pF2 ∧ opc = 0xF0 then
      match imm with
      | .i8 n => some (.rorx sz reg op n)
      | _ => none
    else none
  | _ => none

/-- The forms without ModRM. -/
def ofPlain (enc : Enc) (map : Map) (opc : Byte) (imm : Imm) : Option Instr :=
  match enc, map, imm with
  | .legacy .none rex, .one, .i32 v =>
    if opc = 0x68 then some (.pushI v)
    else if opc = 0x15 then some (.carryA .adc (Sz.ofW (rex.getD Rex.zero).w) v)
    else if opc = 0x1D then some (.carryA .sbb (Sz.ofW (rex.getD Rex.zero).w) v)
    else none
  | .legacy .none _, .one, .i8 v => if opc = 0x6A then some (.pushI8 v) else none
  | _, _, _ => none

/-- The instruction with these raw fields, if any. -/
def ofRaw (r : Raw) : Option Instr :=
  match r.modrm with
  | none => ofPlain r.enc r.map r.opc r.imm
  | some (m, sib, d) =>
    match r.enc with
    | .legacy p rex =>
      let x := rex.getD Rex.zero
      ofLegacy p r.map r.opc (Sz.ofW x.w) m.reg (mkReg x.r m.reg)
        (decodeRM r.fs x.x x.b m sib d) r.imm
    | .vex v =>
      ofVex v.pp r.map r.opc (Sz.ofW v.w) m.reg (mkReg v.r m.reg) (Reg.ofBitVec v.vvvv)
        (decodeRM r.fs v.x v.b m sib d) r.imm

theorem ofRaw_legacyRaw (pfx : Pfx) (w : Bool) (map : Map) (opc : Byte) (reg : BitVec 3)
    (rHi : Bool) (op : RM) (imm : Imm) :
    ofRaw (legacyRaw pfx w map opc reg rHi op imm) =
      ofLegacy pfx map opc (Sz.ofW w) reg (mkReg rHi reg) op imm := by
  simp only [ofRaw, legacyRaw, Ext.mkRex_getD]
  rw [Ext.decodeRM_encodeRM]

theorem ofRaw_vexRaw (pp : Pfx) (w : Bool) (map : Map) (opc : Byte) (reg : BitVec 3)
    (rHi : Bool) (vvvv : BitVec 4) (op : RM) (imm : Imm) :
    ofRaw (vexRaw pp w map opc reg rHi vvvv op imm) =
      ofVex pp map opc (Sz.ofW w) reg (mkReg rHi reg) (Reg.ofBitVec vvvv) op imm := by
  simp only [ofRaw, vexRaw]
  rw [Ext.decodeRM_encodeRM]

@[simp] theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  cases i with
  | carry op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, CarryOp.opcode]
  | carryR op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, CarryOp.opcodeR]
  | carryI op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, CarryOp.digit, CarryOp.ofDigit]
  | carryI8 op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, CarryOp.digit, CarryOp.ofDigit]
  | carryA op sz => cases op <;> simp [toRaw, ofRaw, ofPlain, CarryOp.opcodeA]
  | pushI | pushI8 => simp [toRaw, ofRaw, ofPlain]
  | scan rev => cases rev <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy]
  | bit op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, BitOp.opcode]
  | bitI op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy, BitOp.digit, BitOp.ofDigit]
  | shd right sz dst src count =>
    cases right <;> cases count <;>
      simp [toRaw, ofRaw_legacyRaw, ofLegacy, shdOpcode, ShdCount.imm']
  | adx op => cases op <;> simp [toRaw, ofRaw_legacyRaw, ofLegacy]
  | vop op => cases op <;> simp [toRaw, ofRaw_vexRaw, ofVex, Vop.pfx, Vop.opcode]
  | bls op => cases op <;> simp [toRaw, ofRaw_vexRaw, ofVex, BlsOp.digit, BlsOp.ofDigit]
  | _ => simp [toRaw, ofRaw_legacyRaw, ofRaw_vexRaw, ofLegacy, ofVex]

private theorem wf_legacyRaw {pfx : Pfx} {w : Bool} {map : Map} {opc : Byte} {reg : BitVec 3}
    {rHi : Bool} {op : RM} {imm : Imm} {spec : ImmSpec} (hs : shape map opc = some (true, spec))
    (hi : imm.kind = spec.kind (some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩,
      (encodeRM op).sib, (encodeRM op).disp))) :
    (legacyRaw pfx w map opc reg rHi op imm).WF :=
  ⟨⟨true, spec, hs, Ext.encodeRM_ok op reg, hi⟩, fun _ h => by cases h⟩

private theorem wf_vexRaw {pp : Pfx} {w : Bool} {map : Map} {opc : Byte} {reg : BitVec 3}
    {rHi : Bool} {vvvv : BitVec 4} {op : RM} {imm : Imm} {spec : ImmSpec}
    (hs : shape map opc = some (true, spec))
    (hi : imm.kind = spec.kind (some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩,
      (encodeRM op).sib, (encodeRM op).disp)))
    (hm : map = .m0F38 ∨ map = .m0F3A) :
    (vexRaw pp w map opc reg rHi vvvv op imm).WF :=
  ⟨⟨true, spec, hs, Ext.encodeRM_ok op reg, hi⟩, fun _ _ => hm⟩

theorem toRaw_wf (i : Instr) : (toRaw i).WF := by
  cases i with
  | carry op => cases op <;> exact wf_legacyRaw (spec := .none) (by decide) rfl
  | carryR op => cases op <;> exact wf_legacyRaw (spec := .none) (by decide) rfl
  | carryI op => exact wf_legacyRaw (spec := .i32) (by decide) rfl
  | carryI8 op => exact wf_legacyRaw (spec := .i8) (by decide) rfl
  | carryA op sz =>
    refine ⟨⟨false, .i32, ?_, trivial, rfl⟩, fun _ h => by cases h⟩
    cases op <;> rfl
  | pushI => exact ⟨⟨false, .i32, rfl, trivial, rfl⟩, fun _ h => by cases h⟩
  | pushI8 => exact ⟨⟨false, .i8, rfl, trivial, rfl⟩, fun _ h => by cases h⟩
  | imulI => exact wf_legacyRaw (spec := .i32) (by decide) rfl
  | imulI8 => exact wf_legacyRaw (spec := .i8) (by decide) rfl
  | imul1 => exact wf_legacyRaw (spec := .f7) (by decide) rfl
  | testI => exact wf_legacyRaw (spec := .f7) (by decide) rfl
  | scan rev => cases rev <;> exact wf_legacyRaw (spec := .none) (by decide) rfl
  | bit op => cases op <;> exact wf_legacyRaw (spec := .none) (by decide) rfl
  | bitI op => exact wf_legacyRaw (spec := .i8) (by decide) rfl
  | shd right sz dst src count =>
    cases right <;> cases count
    · exact wf_legacyRaw (spec := .none) (by decide) rfl
    · exact wf_legacyRaw (spec := .i8) rfl rfl
    · exact wf_legacyRaw (spec := .none) (by decide) rfl
    · exact wf_legacyRaw (spec := .i8) rfl rfl
  | xadd => exact wf_legacyRaw (spec := .none) (by decide) rfl
  | cmpxchg => exact wf_legacyRaw (spec := .none) (by decide) rfl
  | adx => exact wf_legacyRaw (spec := .none) rfl rfl
  | movbeLoad => exact wf_legacyRaw (spec := .none) rfl rfl
  | movbeStore => exact wf_legacyRaw (spec := .none) rfl rfl
  | vop => exact wf_vexRaw (spec := .none) rfl rfl (.inl rfl)
  | bls => exact wf_vexRaw (spec := .none) rfl rfl (.inl rfl)
  | rorx => exact wf_vexRaw (spec := .i8) rfl rfl (.inr rfl)

/-! ## Encoder and decoder -/

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-- Read an instruction from the raw fields, without the canonicity check. -/
def guess (bytes : List Byte) : Option Instr := (parse bytes).bind fun r => ofRaw r.1

theorem guess_encode (i : Instr) (rest : List Byte) : guess (encode i ++ rest) = some i := by
  simp [guess, encode, parse_bytes (toRaw_wf i)]

theorem encode_ne_nil (i : Instr) : encode i ≠ [] := by
  simp [encode, Raw.bytes]

/-- Decode one instruction from the front of the bytes. Only canonical
encodings are accepted. -/
def decode (bytes : List Byte) : Option (Instr × Nat) := guessDecode encode guess bytes

/-- The codec as a `Machine.Decoder`. -/
def byteDecoder : Machine.Decoder Instr := canonicalDecoder encode_ne_nil guess_encode

@[simp] theorem byteDecoder_decode : byteDecoder.decode = decode := rfl
@[simp] theorem byteDecoder_encode : byteDecoder.encode = encode := rfl

@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) :=
  byteDecoder.decode_encode_append i rest

/-- A successful decode consumed the canonical encoding of its result. -/
theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat} (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ ∃ rest, bytes = encode i ++ rest := by
  obtain ⟨rfl, ht⟩ := guessDecode_sound h
  refine ⟨rfl, bytes.drop (encode i).length, ?_⟩
  conv_lhs => rw [← List.take_append_drop (encode i).length bytes]
  rw [ht]

end Silmaril.X86.Features.IntExt
