module

public import Silmaril.Machine.RiscV.Ext.Encoding.Defs
public import Silmaril.Machine.RiscV.Blocks.Defs
/-!
# The extended RV64 codec as a byte decoder

Instructions are stored as four little-endian bytes. `byteDecoder` instantiates
the shared `Machine.Decoder` contract; on base instructions its bytes are
exactly `RiscV.encodeBytes` (`encodeBytes_ofBase`). Fetch permissions and
alignment are handled by `Ext.fetch`, not here.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

abbrev Byte := BitVec 8

/-- A 32-bit word from exactly four little-endian bytes. -/
def wordOfBytes : List Byte → Option (BitVec 32)
  | [byte0, byte1, byte2, byte3] => some (byte3 ++ byte2 ++ byte1 ++ byte0)
  | _ => none

/-- The four little-endian bytes of a 32-bit word. -/
def wordBytes (word : BitVec 32) : List Byte :=
  [word.extractLsb' 0 8, word.extractLsb' 8 8, word.extractLsb' 16 8, word.extractLsb' 24 8]

@[simp] theorem wordOfBytes_wordBytes (word : BitVec 32) :
    wordOfBytes (wordBytes word) = some word := by
  simp only [wordOfBytes, wordBytes, Option.some.injEq]
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

theorem wordOfBytes_eq_some {bytes : List Byte} {word : BitVec 32}
    (h : wordOfBytes bytes = some word) : bytes = wordBytes word := by
  match bytes, h with
  | [byte0, byte1, byte2, byte3], h =>
    simp only [wordOfBytes, Option.some.injEq] at h
    subst h
    simp only [wordBytes, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 8 from Nat.le_refl 8),
        BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 16 by decide),
        BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 24 by decide), Nat.reduceSub,
        BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_eq_self]

theorem wordOfBytes_isSome {bytes : List Byte} (h : bytes.length = 4) :
    ∃ word, wordOfBytes bytes = some word := by
  match bytes, h with
  | [_, _, _, _], _ => exact ⟨_, rfl⟩

/-- The four little-endian bytes of an instruction's encoding. -/
def encodeBytes (instr : Instr) : List Byte := wordBytes (encode instr)

@[simp] theorem encodeBytes_length (instr : Instr) : (encodeBytes instr).length = 4 := rfl

@[simp] theorem encodeBytes_ofBase (instr : RiscV.Instr) :
    encodeBytes (.ofBase instr) = RiscV.encodeBytes instr := rfl

/-- Decode one instruction from the first four bytes, little-endian. -/
def decodeBytes : List Byte → Option (Instr × Nat)
  | byte0 :: byte1 :: byte2 :: byte3 :: _ =>
    (decode (byte3 ++ byte2 ++ byte1 ++ byte0)).map fun instr => (instr, 4)
  | _ => none

theorem decodeBytes_length {bytes : List Byte} {instr : Instr} {length : Nat}
    (h : decodeBytes bytes = some (instr, length)) : length = 4 ∧ 4 ≤ bytes.length := by
  match bytes, h with
  | _ :: _ :: _ :: _ :: _, h =>
    simp only [decodeBytes, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    simp

private theorem encode_reassemble (instr : Instr) :
    (encode instr).extractLsb' 24 8 ++ (encode instr).extractLsb' 16 8 ++
      (encode instr).extractLsb' 8 8 ++ (encode instr).extractLsb' 0 8 = encode instr := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

/-- The extended codec as a shared byte decoder. -/
def byteDecoder : Machine.Decoder Instr where
  decode := decodeBytes
  encode := encodeBytes
  decode_length_pos h := by rw [(decodeBytes_length h).1]; decide
  decode_length_le h := by rw [(decodeBytes_length h).1]; exact (decodeBytes_length h).2
  decode_append {bytes} _ _ extra h := by
    match bytes, h with
    | _ :: _ :: _ :: _ :: _, h => exact h
  decode_take {bytes} _ _ h := by
    obtain ⟨rfl, -⟩ := decodeBytes_length h
    match bytes, h with
    | _ :: _ :: _ :: _ :: _, h => exact h
  decode_encode_append instr rest := by
    simp [encodeBytes, wordBytes, decodeBytes, encode_reassemble]

@[simp] theorem byteDecoder_decode : byteDecoder.decode = decodeBytes := rfl
@[simp] theorem byteDecoder_encode : byteDecoder.encode = encodeBytes := rfl

/-- Accepted bytes are exactly an encoding followed by arbitrary bytes. -/
theorem decodeBytes_eq_some {bytes : List Byte} {instr : Instr} {length : Nat}
    (h : decodeBytes bytes = some (instr, length)) :
    length = 4 ∧ bytes = encodeBytes instr ++ bytes.drop 4 := by
  match bytes, h with
  | byte0 :: byte1 :: byte2 :: byte3 :: rest, h =>
    simp only [decodeBytes, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, hdecode, rfl, rfl⟩ := h
    have hencode := encode_decode hdecode
    refine ⟨rfl, ?_⟩
    have := wordOfBytes_eq_some (bytes := [byte0, byte1, byte2, byte3]) rfl
    rw [← hencode] at this
    simp only [encodeBytes, List.drop_succ_cons, List.drop_zero]
    rw [← this]
    rfl

/-- On bytes, the extended decoder extends the base byte decoder. -/
theorem decodeBytes_of_base {bytes : List Byte} {instr : RiscV.Instr} {length : Nat}
    (h : RiscV.decodeBytes bytes = some (instr, length)) :
    decodeBytes bytes = some (.ofBase instr, length) := by
  match bytes, h with
  | _ :: _ :: _ :: _ :: _, h =>
    simp only [RiscV.decodeBytes, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, hdecode, rfl, rfl⟩ := h
    simp [decodeBytes, decode_of_base hdecode]

end Silmaril.RiscV.Ext
