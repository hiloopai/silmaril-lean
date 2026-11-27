module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Writer

public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream.Writer

/-- The independent reader recovers the exact nested schema and logical batches through EOS. -/
theorem emit_readback {limits : ObservationLimits} {field : StructInt32.Field} {batches : List (List Row)}
    {wire : KBytes} (written : emit limits field batches = .ok wire) :
    ∃ observed size,
      Stream.read limits wire = .ok observed ∧ Agrees field batches observed ∧
      wire.wf = true ∧ readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      StructInt32.readSchema limits.ipc (wire.slice 8 size) = .ok field ∧
      BatchesWire limits field wire limits.ipc.batches 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emit_readback written

/-- Output consists of the nested Schema, one ordered frame per batch, and the exact modern terminator. -/
theorem emit_frames {limits : ObservationLimits} {field : StructInt32.Field} {batches : List (List Row)}
    {wire : KBytes} (written : emit limits field batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) =>
        (emitRecord limits.ipc field rows).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emit_frames written

end Silmaril.Formats.Arrow.StructInt32.Stream.Writer
