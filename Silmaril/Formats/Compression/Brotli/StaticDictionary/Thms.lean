module

public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.StaticDictionary

theorem canonical_size : canonicalBytes.size = 122784 :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.canonical_size

theorem wordCount_eq {length : Nat} (valid : WordLength length) :
    wordCount length = 2 ^ Distance.dictionaryDepths[length]'(Nat.lt_succ_of_le valid.2) :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.wordCount_eq valid

theorem bucketOffset_succ {length : Nat} (fits : length < 25) :
    bucketOffset (length + 1) = bucketOffset length + length * wordCount length :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.bucketOffset_succ fits

theorem dictionary_extent : bucketOffset 25 = canonicalBytes.size :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.dictionary_extent

/-- A valid index stays in its length bucket and inside the dictionary. -/
theorem wordExtent {length index : Nat} (valid : WordLength length) (inRange : index < wordCount length) :
    wordOffset length index + length ≤ bucketOffset (length + 1) ∧
      bucketOffset (length + 1) ≤ canonicalBytes.size :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.wordExtent valid inRange

theorem splitAddress_iff {length wordId : Nat} {address : Address} :
    splitAddress length wordId = .ok address ↔
      WordLength length ∧ wordId < transformCount * wordCount length ∧
      address = ⟨length, wordId % wordCount length, wordId / wordCount length⟩ :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.splitAddress_iff

/-- The quotient agrees with the RFC right shift. It and the base index
    are bounded and reconstruct the original word ID exactly. -/
theorem splitAddress_sound {length wordId : Nat} {address : Address}
    (parsed : splitAddress length wordId = .ok address) :
    ∃ valid : WordLength length,
      address.length = length ∧
      address.index = wordId % wordCount length ∧ address.index < wordCount length ∧
      address.transform = wordId >>> Distance.dictionaryDepths[length]'(Nat.lt_succ_of_le valid.2) ∧
      address.transform < transformCount ∧
      wordId = address.transform * wordCount length + address.index :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.splitAddress_sound parsed

theorem splitAddress_roundtrip {length index transform : Nat}
    (valid : WordLength length) (inRange : index < wordCount length) (transformFits : transform < transformCount) :
    splitAddress length (transform * wordCount length + index) = .ok ⟨length, index, transform⟩ :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.splitAddress_roundtrip valid inRange transformFits

theorem lookup_iff {length index : Nat} {word : ByteArray} :
    lookup length index = .ok word ↔
      WordLength length ∧ index < wordCount length ∧
      word = canonicalBytes.extract (wordOffset length index) (wordOffset length index + length) :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.lookup_iff

theorem lookup_size {length index : Nat} {word : ByteArray} (parsed : lookup length index = .ok word) :
    word.size = length :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.lookup_size parsed

theorem lookup_byte {length index ordinal : Nat} {word : ByteArray}
    (parsed : lookup length index = .ok word) (inWord : ordinal < length) :
    word[ordinal]? = canonicalBytes[wordOffset length index + ordinal]? :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.lookup_byte parsed inWord

/-- Existing checked dictionary targets have a valid address and base
    word. This law leaves transform and output execution to their callers. -/
theorem resolved_lookup {bounds : Distance.Bounds} {ring after : Distance.Ring}
    {length code distance wordId : Nat}
    (resolved : Distance.Resolved bounds ring length code distance (.staticDictionary distance length wordId) after) :
    ∃ address word, splitAddress length wordId = .ok address ∧ lookup length address.index = .ok word :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.resolved_lookup resolved

end Silmaril.Formats.Compression.Brotli.StaticDictionary
