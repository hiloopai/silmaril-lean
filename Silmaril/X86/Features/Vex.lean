module

public import Silmaril.X86.Ext.Raw

/-!
# The VEX prefix

The VEX prefix of 64-bit mode (Intel SDM Vol. 2A, §2.3.5, Figures 2-8 and 2-9),
shared by every lane that decodes VEX-encoded instructions (AVX/AVX2/FMA/F16C,
the AVX-512 opmask instructions, and the BMI/BMI2 forms):

* `C5 R̄vvvv̄Lpp` (two bytes), usable when VEX.X = VEX.B = 0, the map is `0F`
  (`mmmmm = 00001`) and VEX.W = 0;
* `C4 R̄X̄B̄mmmmm Wvvvv̄Lpp` (three bytes) otherwise.

R, X, B and vvvv are stored inverted. `Prefix` holds the logical field values.
`Prefix.bytes` is the canonical encoding: the two-byte form exactly when it
can be used (`Prefix.short`), as the GNU and LLVM assemblers emit.

`pPrefix` reads a prefix (`pPayload` after its first byte) with the prefix
laws of `Ext.ByteParser.Good` (`good_pPrefix`), and reads back every canonical
encoding (`pPrefix_bytes`). It accepts the three-byte form of a prefix that
has a two-byte form too: a lane that wants only canonical encodings re-encodes
and compares, as `Avx.decode` does.

The byte builders (`c5Byte`, `c4Byte1`, `c4Byte2`) and their field lemmas
(`c5Byte_fields`, …) are the reusable layer for lanes with their own raw
format; the EVEX P1 byte `W v̄v̄v̄v̄ 1 pp` is `c4Byte2 w v true pp`
(SDM Vol. 2A, §2.7.1, Figure 2-10).
-/

@[expose] public section

namespace Silmaril.X86.Features.Vex

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (ByteParser PResult)
open Silmaril.X86.Ext.ByteParser

/-! ## Prefix bytes -/

/-- `R̄vvvv̄Lpp`, the payload of `C5`. -/
def c5Byte (r : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) : Byte :=
  (BitVec.ofBool (!r) ++ ~~~vvvv ++ BitVec.ofBool l ++ pp : BitVec 8)

/-- `R̄X̄B̄mmmmm`, the first payload byte of `C4`. -/
def c4Byte1 (r x b : Bool) (map : BitVec 5) : Byte :=
  (BitVec.ofBool (!r) ++ BitVec.ofBool (!x) ++ BitVec.ofBool (!b) ++ map : BitVec 8)

/-- `Wvvvv̄Lpp`, the second payload byte of `C4`. -/
def c4Byte2 (w : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) : Byte :=
  (BitVec.ofBool w ++ ~~~vvvv ++ BitVec.ofBool l ++ pp : BitVec 8)

theorem c5Byte_fields (r : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) :
    (!(c5Byte r vvvv l pp).getLsbD 7) = r ∧ ~~~((c5Byte r vvvv l pp).extractLsb' 3 4) = vvvv ∧
      (c5Byte r vvvv l pp).getLsbD 2 = l ∧ (c5Byte r vvvv l pp).extractLsb' 0 2 = pp := by
  revert r vvvv l pp; decide +kernel

theorem c4Byte1_fields (r x b : Bool) (map : BitVec 5) :
    (!(c4Byte1 r x b map).getLsbD 7) = r ∧ (!(c4Byte1 r x b map).getLsbD 6) = x ∧
      (!(c4Byte1 r x b map).getLsbD 5) = b ∧ (c4Byte1 r x b map).extractLsb' 0 5 = map := by
  revert r x b map; decide +kernel

theorem c4Byte2_fields (w : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) :
    (c4Byte2 w vvvv l pp).getLsbD 7 = w ∧ ~~~((c4Byte2 w vvvv l pp).extractLsb' 3 4) = vvvv ∧
      (c4Byte2 w vvvv l pp).getLsbD 2 = l ∧ (c4Byte2 w vvvv l pp).extractLsb' 0 2 = pp := by
  revert w vvvv l pp; decide +kernel

/-- The two-byte and three-byte payloads put R, vvvv, L and pp in the same
bits: `c5Byte` is `c4Byte2` with R̄ in place of W. -/
theorem c5Byte_eq_c4Byte2 (r : Bool) (vvvv : BitVec 4) (l : Bool) (pp : BitVec 2) :
    c5Byte r vvvv l pp = c4Byte2 (!r) vvvv l pp := rfl

/-! ## Prefixes -/

/-- The fields of a VEX prefix, with R, X, B and vvvv at their logical values. -/
structure Prefix where
  r : Bool
  x : Bool
  b : Bool
  /-- `mmmmm`: 1 = `0F`, 2 = `0F38`, 3 = `0F3A`. -/
  map : BitVec 5
  w : Bool
  vvvv : BitVec 4
  l : Bool
  pp : BitVec 2
  deriving DecidableEq, Repr

namespace Prefix

variable (p : Prefix)

/-- The two-byte form can encode the prefix. -/
def short : Bool := !p.x && !p.b && p.map == 1#5 && !p.w

/-- The first byte of the canonical encoding. -/
def lead : Byte := if p.short then 0xC5#8 else 0xC4#8

/-- The payload bytes of the canonical encoding. -/
def payload : List Byte :=
  if p.short then [c5Byte p.r p.vvvv p.l p.pp]
  else [c4Byte1 p.r p.x p.b p.map, c4Byte2 p.w p.vvvv p.l p.pp]

/-- The canonical encoding. -/
def bytes : List Byte := p.lead :: p.payload

/-- The fields of a two-byte payload. -/
def ofC5 (p1 : Byte) : Prefix :=
  ⟨!p1.getLsbD 7, false, false, 1#5, false, ~~~(p1.extractLsb' 3 4), p1.getLsbD 2,
    p1.extractLsb' 0 2⟩

/-- The fields of a three-byte payload. -/
def ofC4 (p1 p2 : Byte) : Prefix :=
  ⟨!p1.getLsbD 7, !p1.getLsbD 6, !p1.getLsbD 5, p1.extractLsb' 0 5, p2.getLsbD 7,
    ~~~(p2.extractLsb' 3 4), p2.getLsbD 2, p2.extractLsb' 0 2⟩

theorem lead_cases : p.lead = 0xC5#8 ∨ p.lead = 0xC4#8 := by
  unfold lead; split <;> simp

theorem lead_ne_64 : p.lead ≠ 0x64#8 := by
  rcases p.lead_cases with h | h <;> rw [h] <;> decide

theorem bytes_ne_nil : p.bytes ≠ [] := by simp [bytes]

/-- A three-byte payload reads back its fields. -/
theorem ofC4_bytes : ofC4 (c4Byte1 p.r p.x p.b p.map) (c4Byte2 p.w p.vvvv p.l p.pp) = p := by
  obtain ⟨h1, h2, h3, h4⟩ := c4Byte1_fields p.r p.x p.b p.map
  obtain ⟨h5, h6, h7, h8⟩ := c4Byte2_fields p.w p.vvvv p.l p.pp
  simp only [ofC4, h1, h2, h3, h4, h5, h6, h7, h8]

/-- A two-byte payload reads back the fields of a short prefix. -/
theorem ofC5_bytes (h : p.short = true) : ofC5 (c5Byte p.r p.vvvv p.l p.pp) = p := by
  obtain ⟨r, x, b, map, w, vvvv, l, pp⟩ := p
  simp only [short, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := c5Byte_fields r vvvv l pp
  simp only [ofC5, h1, h2, h3, h4]

end Prefix

/-! ## The prefix parser -/

/-- The payload of a VEX prefix, given its first byte. -/
def pPayload (b0 : Byte) : ByteParser Prefix :=
  if b0 = 0xC5#8 then map Prefix.ofC5 byte
  else if b0 = 0xC4#8 then bind byte fun p1 => map (Prefix.ofC4 p1) byte
  else fail

/-- A VEX prefix. -/
def pPrefix : ByteParser Prefix := bind byte pPayload

theorem good_pPayload (b0 : Byte) : Good (pPayload b0) := by
  unfold pPayload
  exact good_ite (good_map _ good_byte)
    (good_ite (good_bind good_byte fun _ => good_map _ good_byte) good_fail)

theorem good_pPrefix : Good pPrefix := good_bind good_byte good_pPayload

/-- The payload parser reads back the canonical payload. -/
theorem pPayload_payload (p : Prefix) (rest : List Byte) :
    pPayload p.lead (p.payload ++ rest) = .ok p rest := by
  unfold Prefix.lead Prefix.payload
  by_cases hs : p.short = true
  · simp only [hs, ↓reduceIte, pPayload, List.cons_append, List.nil_append, map_byte_cons,
      p.ofC5_bytes hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pPayload, List.cons_append, List.nil_append]
    simp only [show ¬((0xC4#8 : Byte) = 0xC5#8) by decide, ↓reduceIte]
    rw [bind_ok (byte_cons _ _), map_byte_cons, p.ofC4_bytes]

/-- The prefix parser reads back every canonical encoding. -/
theorem pPrefix_bytes (p : Prefix) (rest : List Byte) : pPrefix (p.bytes ++ rest) = .ok p rest := by
  simp only [pPrefix, Prefix.bytes, List.cons_append, ByteParser.bind, byte_cons]
  exact pPayload_payload p rest

/-- The prefix parser only accepts input starting with `C5` or `C4`. -/
theorem pPrefix_head {bytes : List Byte} {p : Prefix} {rest : List Byte}
    (h : pPrefix bytes = .ok p rest) : ∃ b0 tl, bytes = b0 :: tl ∧ (b0 = 0xC5#8 ∨ b0 = 0xC4#8) := by
  cases bytes with
  | nil => simp [pPrefix, ByteParser.bind] at h
  | cons b0 tl =>
    refine ⟨b0, tl, rfl, ?_⟩
    simp only [pPrefix, ByteParser.bind, byte_cons, pPayload] at h
    by_cases h5 : b0 = 0xC5#8
    · exact .inl h5
    · by_cases h4 : b0 = 0xC4#8
      · exact .inr h4
      · simp [h5, h4] at h

/-! ## The opcode key -/

/-- The implied prefix `pp`, the map `mmmmm` and the opcode byte of a
VEX-encoded instruction: what selects its opcode-table row. Lanes that share
the VEX space are disjoint when their tables have no key in common
(`key_bytes`). -/
def key : List Byte → Option (BitVec 2 × BitVec 5 × Byte)
  | b0 :: p1 :: rest =>
    if b0 = 0xC5#8 then
      match rest with
      | opc :: _ => some (p1.extractLsb' 0 2, 1#5, opc)
      | [] => none
    else if b0 = 0xC4#8 then
      match rest with
      | p2 :: opc :: _ => some (p2.extractLsb' 0 2, p1.extractLsb' 0 5, opc)
      | _ => none
    else none
  | _ => none

/-- The key of a canonical prefix followed by an opcode. -/
theorem key_bytes (p : Prefix) (opc : Byte) (rest : List Byte) :
    key (p.bytes ++ opc :: rest) = some (p.pp, p.map, opc) := by
  unfold Prefix.bytes Prefix.lead Prefix.payload
  by_cases hs : p.short = true
  · have hmap : p.map = 1#5 := by
      simp only [Prefix.short, Bool.and_eq_true, beq_iff_eq] at hs
      exact hs.1.2
    obtain ⟨-, -, -, h4⟩ := c5Byte_fields p.r p.vvvv p.l p.pp
    simp [hs, key, h4, hmap]
  · obtain ⟨-, -, -, h4⟩ := c4Byte1_fields p.r p.x p.b p.map
    obtain ⟨-, -, -, h8⟩ := c4Byte2_fields p.w p.vvvv p.l p.pp
    simp only [hs, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, key]
    simp [h4, h8]

/-- A list with a key starts with `C5` or `C4`. -/
theorem key_head {bytes : List Byte} {k : BitVec 2 × BitVec 5 × Byte} (h : key bytes = some k) :
    ∃ b0 tl, bytes = b0 :: tl ∧ (b0 = 0xC5#8 ∨ b0 = 0xC4#8) := by
  match bytes, h with
  | b0 :: p1 :: rest, h =>
    refine ⟨b0, p1 :: rest, rfl, ?_⟩
    unfold key at h
    by_cases h5 : b0 = 0xC5#8
    · exact .inl h5
    · by_cases h4 : b0 = 0xC4#8
      · exact .inr h4
      · simp [h5, h4] at h

end Silmaril.X86.Features.Vex
