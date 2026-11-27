module

public import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms
import Silmaril.Formats.Arrow.LargeUtf8.Stream.Thms
import Silmaril.Formats.Arrow.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeUtf8.StreamWriter

open Silmaril.Formats.Arrow
open LargeUtf8.StreamWriter

theorem encodeValue_octets (text : String) :
    (encodeValue text).toList = text.toByteArray.data.toList :=
  Writer.emitBytes_bytes _

theorem encodeValue_length (text : String) : (encodeValue text).len = text.utf8ByteSize := by
  rw [encodeValue, Writer.emitWords_length, List.length_map, Nat.one_mul]
  rfl

private theorem fold_sizes (values : LargeUtf8.Column) (start : Nat) :
    (encodeColumn values).foldl (fun pos value => pos + Binary.StreamWriter.valueSize value) start =
      start + Writer.utf8ByteCount values := by
  induction values generalizing start with
  | nil => simp [encodeColumn, Writer.utf8ByteCount]
  | cons slot rest ih =>
    simp only [encodeColumn, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih, Nat.add_assoc]
    cases slot with
    | none => simp [Binary.StreamWriter.valueSize, KBytes.empty, KBytes.len, Writer.utf8ByteCount]
    | some text =>
      simp [Binary.StreamWriter.valueSize, Writer.utf8ByteCount, encodeValue_length]

theorem encodeColumn_dataSize (values : LargeUtf8.Column) :
    Binary.StreamWriter.dataSize (encodeColumn values) = Writer.utf8ByteCount values := by
  simpa only [Binary.StreamWriter.dataSize, Nat.zero_add] using fold_sizes values 0

theorem serialize_exact {limits : Limits} {field : LargeUtf8.Field}
    {batches : List LargeUtf8.Column} {wire : KBytes}
    (written : serialize limits field batches = .ok wire) :
    Binary.StreamWriter.SerializedProfileWire .largeUtf8 limits field.name field.nullable
      (batches.map encodeColumn) wire := by
  cases checked : preflight limits field batches with
  | error => simp [serialize, checked, Bind.bind, Except.bind] at written
  | ok =>
    apply Binary.StreamWriter.serializeProfile_exact
    simpa [serialize, checked, Bind.bind, Except.bind] using written

theorem emit_readback {limits : Limits} {field : LargeUtf8.Field}
    {batches : List LargeUtf8.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, LargeUtf8.Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ LargeUtf8.Stream.StreamWire limits .modern wire decoded ∧
      Binary.StreamWriter.SerializedProfileWire .largeUtf8 limits field.name field.nullable
        (batches.map encodeColumn) wire := by
  cases serialized : serialize limits field batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind, Except.mapError] at written
  | ok actual =>
    cases decoded : LargeUtf8.Stream.read limits .modern actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases agrees : Agrees field batches result
      · have same : actual = wire := by
          simpa [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] using written
        subst wire
        exact ⟨result, decoded, agrees, LargeUtf8.Stream.read_sound decoded, serialize_exact serialized⟩
      · simp [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] at written

end Silmaril.Proofs.Formats.Arrow.LargeUtf8.StreamWriter
