module

public import Silmaril.Formats.Compression.Brotli.Distance.Defs
public import Silmaril.Data.IncludeBytes.Types
import Silmaril.Data.IncludeBytes

/-! RFC 7932 §8 and Appendix A address decomposition and base-word lookup. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.StaticDictionary

def transformCount : Nat := 121

def WordLength (length : Nat) : Prop :=
  4 ≤ length ∧ length ≤ 24

instance (length : Nat) : Decidable (WordLength length) :=
  inferInstanceAs (Decidable (4 ≤ length ∧ length ≤ 24))

/-- Actual bucket size. Lengths below four have no words. -/
def wordCount (length : Nat) : Nat :=
  if length < 4 then 0 else Distance.dictionaryWordCount length

/-- RFC DOFFSET, including the end sentinel at 25. -/
def bucketOffset (length : Nat) : Nat :=
  (List.range (min length 25)).foldl (fun offset width => offset + width * wordCount width) 0

def wordOffset (length index : Nat) : Nat :=
  bucketOffset length + index * length

structure Address where
  length : Nat
  index : Nat
  transform : Nat
  deriving DecidableEq, Repr

inductive Error where
  | wordLength
  | wordId
  | wordIndex
  deriving DecidableEq, Repr

/-- Split the word ID from a static dictionary target into the base-word
    index and transform ordinal. Transform materialization is separate. -/
def splitAddress (length wordId : Nat) : Except Error Address :=
  if ¬WordLength length then .error .wordLength
  else
    let count := wordCount length
    if transformCount * count ≤ wordId then .error .wordId
    else .ok ⟨length, wordId % count, wordId / count⟩

/-- Appendix A DICT, pinned to libbrotli v1.2.0's matching dictionary.bin.
    SHA-256 20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70. -/
def canonicalBytes : ByteArray :=
  include_bytes "../../../../../data/brotli-static-dictionary/dictionary.bin"

/-- Select exactly one untransformed base word from its checked bucket. -/
def lookup (length index : Nat) : Except Error ByteArray :=
  if ¬WordLength length then .error .wordLength
  else if wordCount length ≤ index then .error .wordIndex
  else
    let offset := wordOffset length index
    .ok (canonicalBytes.extract offset (offset + length))

end Silmaril.Formats.Compression.Brotli.StaticDictionary
