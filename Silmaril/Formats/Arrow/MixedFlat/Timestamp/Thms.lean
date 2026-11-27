module

public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp.Read

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Timestamp

/-- Schema names, nullability and normalized type payloads come from the original metadata frame. -/
theorem readSchema_wire {limits : Arrow.Limits} {input : KBytes} {fields : List Field} {start : Nat}
    (read : readSchema limits input = .ok (fields, start)) :
    ∃ size original,
      readEnvelope limits input 0 = .ok (.metadata size) ∧
      SchemaReader.readMessage limits (input.slice 8 size) = .ok original ∧ original.endianness = .little ∧
      (original.fields.zipIdx.mapM fun (field, position) => bindField field position) = .ok fields ∧
      start = 8 + size :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.readSchema_wire read

/-- A checked batch preserves the exact descriptor assignment and values from the original body. -/
theorem readParsed_wire {limits : ObservationLimits} {fields : List Field} {record : RecordBatch}
    {length : Nat} {body : KBytes} {batch : Batch}
    (read : readParsed limits fields record length body = .ok batch) :
    BatchWire limits fields record length body batch :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.readParsed_wire read

/-- Successful native readback traverses the original ordered records through exact EOS. -/
theorem read_wire {limits : ObservationLimits} {input : KBytes} {stream : Stream}
    (read : Timestamp.read limits input = .ok stream) :
    ∃ start, readSchema limits.ipc input = .ok (stream.fields, start) ∧
      BatchesWire limits input stream.fields limits.ipc.batches 0 start stream.batches :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.read_wire read

end Silmaril.Formats.Arrow.MixedFlat.Timestamp
