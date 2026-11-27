module

public import Silmaril.Formats.Arrow.DateStream.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.DateInterop.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream.Writer

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateStream.Writer
open Silmaril.Formats.Arrow.MetadataWriter.Wire
open Silmaril.Formats.DateInterop

private theorem append_length (a b : KBytes) : (a ++ b).len = a.len + b.len := rfl

private theorem zeros_length (n : Nat) : (KBytes.zeros n).len = n := rfl

theorem schemaMetadata_size (name : String) (nullable : Bool) :
    (Internal.schemaMetadata name nullable).len = Internal.schemaSize name := by
  have nameSize : name.toByteArray.data.toList.length = name.utf8ByteSize := rfl
  simp only [Internal.schemaMetadata, Internal.schemaSize, messagePrefix, schemaPayloadOf,
    fieldOffsets, fieldFragment, date32FieldBytes, pad, words, longs,
    Arrow.Writer.emitWords_length, append_length, zeros_length, List.length_cons, List.length_nil,
    List.foldr_cons, List.foldr_nil, List.length_map, nameSize]
  have fragment : 4 * 7 + (4 * 5 + (4 * 1 + (1 * name.utf8ByteSize + 1))) =
      53 + name.utf8ByteSize := by omega
  rw [fragment]
  change 48 + (24 + (0 + (53 + name.utf8ByteSize +
    Arrow.Writer.padding (53 + name.utf8ByteSize) + 0))) = _
  omega

theorem emit_readback {limits : ObservationLimits} {name : String} {nullable : Bool}
    {batches : List DateStream.Writer.Column} {wire : KBytes} (written : DateStream.Writer.emit limits name nullable batches = .ok wire) :
    DateStream.read limits.ipc wire = .ok (observation name nullable batches) := by
  cases serialized : Internal.serialize limits name nullable batches with
  | error => simp [DateStream.Writer.emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases observed : DateStream.read limits.ipc actual with
    | error =>
      simp [DateStream.Writer.emit, serialized, observed, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases exactRead : result = observation name nullable batches
      · have same : actual = wire := by
          simpa [DateStream.Writer.emit, serialized, observed, exactRead, Bind.bind, Except.bind,
            Except.mapError] using written
        simpa [← same, exactRead] using observed
      · simp [DateStream.Writer.emit, serialized, observed, exactRead, Bind.bind, Except.bind,
          Except.mapError] at written

private theorem civil_slot (slot : Option Date32.Payload) :
    ((slot.map Date32.toCivil).bind Date32.ofCivil?) = slot := by
  cases slot <;> simp

theorem observation_words (name : String) (nullable : Bool) (batches : List DateStream.Writer.Column) :
    (observation name nullable batches).batches.map
        (List.map (fun slot => slot.bind Date32.ofCivil?)) = batches := by
  simp [observation, List.map_map, Function.comp_def, civil_slot]

end Silmaril.Proofs.Formats.Arrow.DateStream.Writer
