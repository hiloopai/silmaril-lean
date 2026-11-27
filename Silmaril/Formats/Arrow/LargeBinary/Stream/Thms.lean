module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.LargeBinary.Stream

theorem readRecord_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {offset size : Nat} {record : Batch}
    (read : readRecord limits framing input field offset size = .ok record) :
    RecordWire limits framing input field offset size record :=
  Proofs.Formats.Arrow.LargeBinary.Stream.readRecord_sound read

/-- Success gives ordered original record windows through an exact EOS. -/
theorem read_sound {limits : Limits} {framing : Framing} {input : KBytes} {observed : Observed}
    (success : read limits framing input = .ok observed) : StreamWire limits framing input observed :=
  Proofs.Formats.Arrow.LargeBinary.Stream.read_sound success

theorem record_octets {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {offset size : Nat} {record : Batch}
    (wf : input.wf = true) (wire : RecordWire limits framing input field offset size record) :
    let range := record.range
    range.next ≤ input.len ∧
      (input.slice range.metadataStart range.metadataSize).toList =
        (input.toList.drop range.metadataStart).take range.metadataSize ∧
      (input.slice range.bodyStart range.bodyLength).toList =
        (input.toList.drop range.bodyStart).take range.bodyLength :=
  Proofs.Formats.Arrow.LargeBinary.Stream.record_octets wf wire

end Silmaril.Formats.Arrow.LargeBinary.Stream
