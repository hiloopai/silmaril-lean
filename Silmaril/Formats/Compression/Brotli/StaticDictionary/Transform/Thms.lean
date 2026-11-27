module

public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform

/-- One RFC ferment step changes only its designated byte and retains the remaining suffix. -/
theorem fermentStep_sound (word : List UInt8) :
    StepWire word (fermentStep word).1 (fermentStep word).2 :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.fermentStep_sound word

/-- A step preserves total byte count and strictly shortens each nonempty remainder. -/
theorem StepWire.extent {word leading trailing : List UInt8}
    (step : StepWire word leading trailing) :
    leading.length + trailing.length = word.length ∧ (word ≠ [] → trailing.length < word.length) :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.StepWire.extent step

/-- FermentAll applies the RFC steps in order until the base word is exhausted. -/
theorem fermentAll_sound (word : List UInt8) : FermentAllWire word (fermentAll word) :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.fermentAll_sound word

theorem middle_sound (action : Action) (word : List UInt8) : MiddleWire action word (middle action word) :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.middle_sound action word

theorem MiddleWire.size {action : Action} {word result : List UInt8} (wire : MiddleWire action word result) :
    result.length = middleSize action word.length :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.MiddleWire.size wire

/-- Every Appendix B row contributes at most 13 affix bytes. -/
theorem entry_affix_bound {ordinal : Nat} {row : Entry} (chosen : table[ordinal]? = some row) :
    row.leading.length + row.trailing.length ≤ 13 :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.entry_affix_bound chosen

theorem table_total {ordinal : Nat} : (∃ row, table[ordinal]? = some row) ↔ ordinal < transformCount :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.table_total

theorem applyTransform_iff {ordinal : Nat} {word result : ByteArray} :
    applyTransform ordinal word = .ok result ↔
      WordLength word.size ∧ ∃ row, table[ordinal]? = some row ∧
        result = ⟨(row.leading ++ middle row.action word.data.toList ++ row.trailing).toArray⟩ :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.applyTransform_iff

theorem baseLength_iff {ordinal : Nat} {word : ByteArray} :
    applyTransform ordinal word = .error .baseLength ↔ ¬WordLength word.size :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.baseLength_iff

theorem transformOrdinal_iff {ordinal : Nat} {word : ByteArray} :
    applyTransform ordinal word = .error .transformOrdinal ↔ WordLength word.size ∧ transformCount ≤ ordinal :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.transformOrdinal_iff

/-- A successful transform writes the exact prefix, transformed middle and suffix. -/
theorem applyTransform_sound {ordinal : Nat} {word result : ByteArray}
    (parsed : applyTransform ordinal word = .ok result) : Wire ordinal word result :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.applyTransform_sound parsed

/-- The output extent is exact. Its growth over the base word is at most 13 bytes. -/
theorem Wire.size {ordinal : Nat} {word result : ByteArray} {row : Entry}
    (wire : Wire ordinal word result) (chosen : table[ordinal]? = some row) :
    result.size = outputSize row word.size ∧ result.size ≤ word.size + 13 :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.Wire.size wire chosen

/-- Every checked dictionary target yields the canonical base word and exact transformed bytes,
    with at most 37 output bytes. -/
theorem materialize_resolved {bounds : Distance.Bounds} {ring after : Distance.Ring}
    {length code distance wordId : Nat}
    (resolved : Distance.Resolved bounds ring length code distance (.staticDictionary distance length wordId) after) :
    ∃ address word row result,
      splitAddress length wordId = .ok address ∧ lookup length address.index = .ok word ∧
      table[address.transform]? = some row ∧ materialize length wordId = .ok result ∧
      Wire address.transform word result ∧ result.size = outputSize row length ∧ result.size ≤ 37 :=
  Proofs.Formats.Compression.Brotli.StaticDictionary.Transform.materialize_resolved resolved

end Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform
