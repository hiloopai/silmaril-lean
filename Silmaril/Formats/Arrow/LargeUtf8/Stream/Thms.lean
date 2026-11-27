module

public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream

theorem readRecord_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeUtf8.Field} {offset size : Nat} {record : Batch}
    (read : readRecord limits framing input field offset size = .ok record) :
    RecordWire limits framing input field offset size record :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.readRecord_sound read

/-- Success gives ordered original record windows through an exact EOS. -/
theorem read_sound {limits : Limits} {framing : Framing} {input : KBytes} {observed : Observed}
    (success : read limits framing input = .ok observed) : StreamWire limits framing input observed :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.read_sound success

/-- A failed read identifies the original attempted record and its precise
cause after the checked preceding record windows. -/
theorem read_failure {limits : Limits} {framing : Framing} {input : KBytes}
    {ordinal offset : Nat} {cause : Cause}
    (failed : read limits framing input = .error (.record ordinal offset cause)) :
    input.wf = true ∧ ∃ schemaSize field,
      framing.readEnvelope limits input 0 = .ok (.metadata schemaSize) ∧
      LargeUtf8.readSchema limits (input.slice framing.prefixSize schemaSize) = .ok field ∧
      BatchesFailure limits framing input field limits.batches 0 (framing.prefixSize + schemaSize)
        (.record ordinal offset cause) :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.read_failure failed

theorem record_octets {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeUtf8.Field} {offset size : Nat} {record : Batch}
    (wf : input.wf = true) (wire : RecordWire limits framing input field offset size record) :
    let range := record.range
    range.next ≤ input.len ∧
      (input.slice range.metadataStart range.metadataSize).toList =
        (input.toList.drop range.metadataStart).take range.metadataSize ∧
      (input.slice range.bodyStart range.bodyLength).toList =
        (input.toList.drop range.bodyStart).take range.bodyLength :=
  Proofs.Formats.Arrow.LargeUtf8.Stream.record_octets wf wire

end Silmaril.Formats.Arrow.LargeUtf8.Stream
