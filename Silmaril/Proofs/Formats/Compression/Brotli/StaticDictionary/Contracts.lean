module

public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs
import Silmaril.Formats.Compression.Brotli.Distance.Thms
import Silmaril.Data.IncludeBytes
import Init.Data.ByteArray.Lemmas
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary

open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.StaticDictionary

theorem bucketOffset_succ {length : Nat} (fits : length < 25) :
    bucketOffset (length + 1) = bucketOffset length + length * wordCount length := by
  have next : length + 1 ≤ 25 := fits
  simp only [bucketOffset, Nat.min_eq_left next, Nat.min_eq_left (Nat.le_of_lt fits),
    List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem bucketOffset_mono {lo hi : Nat} (ordered : lo ≤ hi) :
    bucketOffset lo ≤ bucketOffset hi := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | @step n _ ih =>
    apply Nat.le_trans ih
    by_cases fits : n < 25
    · rw [bucketOffset_succ fits]
      exact Nat.le_add_right _ _
    · have enough : 25 ≤ n := by omega
      simp [bucketOffset, Nat.min_eq_right enough, Nat.min_eq_right (Nat.le_succ_of_le enough)]

theorem wordCount_eq {length : Nat} (valid : WordLength length) :
    wordCount length = 2 ^ Distance.dictionaryDepths[length]'(Nat.lt_succ_of_le valid.2) := by
  simp [wordCount, Distance.dictionaryWordCount, Nat.not_lt_of_ge valid.1, Nat.lt_succ_of_le valid.2]

private theorem wordCount_pos {length : Nat} (valid : WordLength length) : 0 < wordCount length := by
  rw [wordCount_eq valid]
  exact Nat.two_pow_pos _

private theorem decode_size {chunk len : Nat} {literals : List Nat}
    (fits : len ≤ chunk * literals.length) : (Silmaril.IncludeBytes.decode chunk len literals).size = len := by
  change (Silmaril.IncludeBytes.bytesChunks chunk len literals).length = len
  induction literals generalizing len with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero] at fits
    simp [Silmaril.IncludeBytes.bytesChunks_nil, Nat.eq_zero_of_le_zero fits]
  | cons head tail ih =>
    simp only [List.length_cons, Nat.mul_succ] at fits
    have remaining : len - chunk ≤ chunk * tail.length := by omega
    rw [Silmaril.IncludeBytes.bytesChunks_cons, List.length_append, Silmaril.IncludeBytes.length_bytesLE, ih remaining]
    omega

theorem canonical_size : canonicalBytes.size = 122784 := by
  unfold canonicalBytes
  apply decode_size
  decide

theorem dictionary_extent : bucketOffset 25 = canonicalBytes.size := by
  rw [canonical_size]
  decide

theorem wordExtent {length index : Nat} (valid : WordLength length) (inRange : index < wordCount length) :
    wordOffset length index + length ≤ bucketOffset (length + 1) ∧
      bucketOffset (length + 1) ≤ canonicalBytes.size := by
  have fits : length < 25 := Nat.lt_succ_of_le valid.2
  constructor
  · rw [wordOffset, bucketOffset_succ fits, Nat.add_assoc, ← Nat.succ_mul, Nat.mul_comm length]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right length (Nat.succ_le_of_lt inRange)) _
  · rw [← dictionary_extent]
    exact bucketOffset_mono fits

theorem splitAddress_iff {length wordId : Nat} {address : Address} :
    splitAddress length wordId = .ok address ↔
      WordLength length ∧ wordId < transformCount * wordCount length ∧
      address = ⟨length, wordId % wordCount length, wordId / wordCount length⟩ := by
  unfold splitAddress
  by_cases valid : WordLength length
  · by_cases fits : wordId < transformCount * wordCount length
    · simp [valid, fits, Nat.not_le_of_gt fits, eq_comm]
    · simp [valid, fits, Nat.le_of_not_gt fits]
  · simp [valid]

theorem splitAddress_sound {length wordId : Nat} {address : Address}
    (parsed : splitAddress length wordId = .ok address) :
    ∃ valid : WordLength length,
      address.length = length ∧
      address.index = wordId % wordCount length ∧ address.index < wordCount length ∧
      address.transform = wordId >>> Distance.dictionaryDepths[length]'(Nat.lt_succ_of_le valid.2) ∧
      address.transform < transformCount ∧
      wordId = address.transform * wordCount length + address.index := by
  obtain ⟨valid, fits, rfl⟩ := splitAddress_iff.mp parsed
  have positive := wordCount_pos valid
  refine ⟨valid, rfl, rfl, Nat.mod_lt _ positive, ?_, ?_, (Nat.div_add_mod' _ _).symm⟩
  · rw [Nat.shiftRight_eq_div_pow, wordCount_eq valid]
  · exact (Nat.div_lt_iff_lt_mul positive).2 fits

theorem splitAddress_roundtrip {length index transform : Nat}
    (valid : WordLength length) (inRange : index < wordCount length) (transformFits : transform < transformCount) :
    splitAddress length (transform * wordCount length + index) = .ok ⟨length, index, transform⟩ := by
  have belowNext : transform * wordCount length + index < (transform + 1) * wordCount length := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left inRange _
  have fits := Nat.lt_of_lt_of_le belowNext (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt transformFits))
  have remainder : (transform * wordCount length + index) % wordCount length = index := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt inRange]
  have quotient : (transform * wordCount length + index) / wordCount length = transform := by
    rw [Nat.mul_comm transform, Nat.mul_add_div (wordCount_pos valid), Nat.div_eq_of_lt inRange, Nat.add_zero]
  exact splitAddress_iff.mpr ⟨valid, fits, by rw [remainder, quotient]⟩

theorem lookup_iff {length index : Nat} {word : ByteArray} :
    lookup length index = .ok word ↔
      WordLength length ∧ index < wordCount length ∧
      word = canonicalBytes.extract (wordOffset length index) (wordOffset length index + length) := by
  unfold lookup
  by_cases valid : WordLength length
  · by_cases fits : index < wordCount length
    · simp [valid, fits, Nat.not_le_of_gt fits, eq_comm]
    · simp [valid, fits, Nat.le_of_not_gt fits]
  · simp [valid]

theorem lookup_size {length index : Nat} {word : ByteArray} (parsed : lookup length index = .ok word) :
    word.size = length := by
  obtain ⟨valid, fits, rfl⟩ := lookup_iff.mp parsed
  obtain ⟨inBucket, inDictionary⟩ := wordExtent valid fits
  rw [ByteArray.size_extract, Nat.min_eq_left (Nat.le_trans inBucket inDictionary), Nat.add_sub_cancel_left]

theorem lookup_byte {length index ordinal : Nat} {word : ByteArray}
    (parsed : lookup length index = .ok word) (inWord : ordinal < length) :
    word[ordinal]? = canonicalBytes[wordOffset length index + ordinal]? := by
  have localBound : ordinal < word.size := by simpa only [lookup_size parsed] using inWord
  obtain ⟨_, _, rfl⟩ := lookup_iff.mp parsed
  let offset := wordOffset length index
  have inDictionary : offset + ordinal < canonicalBytes.size := ByteArray.getElem_extract_aux localBound
  rw [getElem?_pos (canonicalBytes.extract offset (offset + length)) ordinal localBound,
    getElem?_pos canonicalBytes (offset + ordinal) inDictionary]
  exact congrArg some (ByteArray.getElem_extract localBound)

theorem resolved_lookup {bounds : Distance.Bounds} {ring after : Distance.Ring}
    {length code distance wordId : Nat}
    (resolved : Distance.Resolved bounds ring length code distance (.staticDictionary distance length wordId) after) :
    ∃ address word, splitAddress length wordId = .ok address ∧ lookup length address.index = .ok word := by
  obtain ⟨_, _, _, _, lo, hi, _, fits, _⟩ := Distance.Resolved.valid resolved
  have valid : WordLength length := ⟨lo, hi⟩
  have count : wordCount length = Distance.dictionaryWordCount length := by
    simp [wordCount, Nat.not_lt_of_ge lo]
  have parsed : splitAddress length wordId = .ok ⟨length, wordId % wordCount length, wordId / wordCount length⟩ :=
    splitAddress_iff.mpr ⟨valid, by simpa only [count, transformCount] using fits, rfl⟩
  refine ⟨_, _, parsed, lookup_iff.mpr ⟨valid, Nat.mod_lt _ (wordCount_pos valid), rfl⟩⟩

end Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary
