module
public import Mathlib.Data.BitVec
@[expose] public section

namespace Silmaril.Machine.LittleEndian

/-- Byte `index` of a 64-bit word, with its least significant byte first. -/
def wordByte (word : BitVec 64) (index : Nat) : BitVec 8 :=
  (word >>> (8 * index)).setWidth 8

/-- Serialize a list of 64-bit words in little-endian order. -/
def encodeWords (words : List (BitVec 64)) : List (BitVec 8) :=
  List.ofFn fun index : Fin (8 * words.length) =>
    wordByte (words[index.val / 8]'(by have := index.isLt; omega)) (index.val % 8)

@[simp] theorem encodeWords_length (words : List (BitVec 64)) :
    (encodeWords words).length = 8 * words.length := by simp [encodeWords]

theorem encodeWords_byte (words : List (BitVec 64)) (word : Fin words.length)
    (byte : Fin 8) :
    (encodeWords words)[8 * word.val + byte.val]? = some (wordByte words[word] byte.val) := by
  have hi : 8 * word.val + byte.val < 8 * words.length := by omega
  have hd : (8 * word.val + byte.val) / 8 = word.val := by omega
  have hm : (8 * word.val + byte.val) % 8 = byte.val := by omega
  simp [encodeWords, hi, hd, hm]

/-- Byte lookup by a flat array offset. -/
theorem encodeWords_get (words : List (BitVec 64)) (index : Nat)
    (bound : index < (encodeWords words).length) :
    (encodeWords words)[index] =
      wordByte (words[index / 8]'(by rw [encodeWords_length] at bound; omega)) (index % 8) := by
  have h := encodeWords_byte words ⟨index / 8, by rw [encodeWords_length] at bound; omega⟩
    ⟨index % 8, by omega⟩
  have address : 8 * (index / 8) + index % 8 = index := by omega
  simp only [address, List.getElem?_eq_getElem bound, Option.some.injEq] at h
  exact h

/-- Serialization preserves concatenation without padding between arrays. -/
theorem encodeWords_append (first second : List (BitVec 64)) :
    encodeWords (first ++ second) = encodeWords first ++ encodeWords second := by
  apply List.ext_getElem
  · simp [Nat.mul_add]
  · intro index leftBound rightBound
    have totalBound : index < 8 * (first.length + second.length) := by
      simpa only [encodeWords_length, List.length_append] using leftBound
    rw [encodeWords_get]
    by_cases firstPart : index < 8 * first.length
    · have byteBound : index < (encodeWords first).length := by simpa using firstPart
      have wordBound : index / 8 < first.length := by omega
      rw [List.getElem_append_left byteBound, encodeWords_get, List.getElem_append_left wordBound]
    · have wordBound : first.length ≤ index / 8 := by omega
      have byteBound : (encodeWords first).length ≤ index := by rw [encodeWords_length]; omega
      have quotient : (index - 8 * first.length) / 8 = index / 8 - first.length := by omega
      have remainder : (index - 8 * first.length) % 8 = index % 8 := by omega
      rw [List.getElem_append_right byteBound, encodeWords_get, List.getElem_append_right wordBound]
      simp only [encodeWords_length, quotient, remainder]

end Silmaril.Machine.LittleEndian
