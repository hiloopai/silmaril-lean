module

public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs
import Silmaril.Formats.Arrow.Binary.Stream.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.Binary.StreamWriter
open Silmaril.Formats.Arrow.MetadataWriter.Wire

private theorem appendLen (first second : KBytes) :
    (first ++ second).len = first.len + second.len := rfl

private theorem zerosLen (size : Nat) : (KBytes.zeros size).len = size := rfl

theorem schema_extent (field : Binary.Field) : (Wire.schema field).len = Wire.schemaSize field := by
  have nameSize : field.name.toByteArray.data.toList.length = field.name.utf8ByteSize := rfl
  simp only [Wire.schema, Wire.schemaSize, messagePrefix, schemaPayloadOf, fieldOffsets, fieldFragment,
    pad, words, longs, Writer.emitWords_length, appendLen, zerosLen, List.length_cons,
    List.length_nil, List.foldr_cons, List.foldr_nil, List.length_map, nameSize]
  have fragment : 4 * 7 + (4 * 5 + (4 * 1 + (1 * field.name.utf8ByteSize + 1))) =
      53 + field.name.utf8ByteSize := by omega
  rw [fragment]
  change 48 + (24 + (0 + (53 + field.name.utf8ByteSize +
    Writer.padding (53 + field.name.utf8ByteSize) + 0))) = _
  omega

theorem emit_readback {limits : Limits} {field : Binary.Field}
    {batches : List Binary.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, Binary.Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ Binary.Stream.StreamWire limits .modern wire decoded := by
  cases serialized : serialize limits field batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases decoded : Binary.Stream.read limits .modern actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases agrees : Agrees field batches result
      · have same : actual = wire := by
          simpa [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] using written
        subst wire
        exact ⟨result, decoded, agrees, Binary.Stream.read_sound decoded⟩
      · simp [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] at written

end Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter
