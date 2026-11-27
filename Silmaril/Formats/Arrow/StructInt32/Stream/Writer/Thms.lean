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
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emitFor_readback (width := .int32) written

/-- Output consists of the nested Schema, one ordered frame per batch, and the exact modern terminator. -/
theorem emit_frames {limits : ObservationLimits} {field : StructInt32.Field} {batches : List (List Row)}
    {wire : KBytes} (written : emit limits field batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) =>
        (emitRecord limits.ipc field rows).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emitFor_frames (width := .int32) written

/-- The checked native reader recovers the selected signed widths, schemas
and logical batches through exact EOS. -/
theorem emitFor_readback {width : StructInt32.RightWidth} {limits : ObservationLimits}
    {field : StructInt32.Field} {batches : List (List (RowFor width.Value))}
    {wire : KBytes} (written : emitFor width limits field batches = .ok wire) :
    ∃ observed size,
      Stream.readFor width limits wire = .ok observed ∧ AgreesFor field batches observed ∧
      wire.wf = true ∧ readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      StructInt32.readSchemaFor width limits.ipc (wire.slice 8 size) = .ok field ∧
      BatchesWireFor width limits field wire limits.ipc.batches 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emitFor_readback written

/-- Either profile emits the selected schema, one ordered record per batch, and EOS. -/
theorem emitFor_frames {width : StructInt32.RightWidth} {limits : ObservationLimits}
    {field : StructInt32.Field} {batches : List (List (RowFor width.Value))}
    {wire : KBytes} (written : emitFor width limits field batches = .ok wire) :
    ∃ schema records, emitSchemaFor width limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) =>
        (emitRecordFor width limits.ipc field rows).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.StructInt32.Stream.Writer.emitFor_frames written

/-- Profile selection at Int32 is exactly the original checked writer. -/
theorem emitFor_int32 (limits : ObservationLimits) (field : StructInt32.Field) (batches : List (List Row)) :
    emitFor .int32 limits field batches = emit limits field batches := rfl

end Silmaril.Formats.Arrow.StructInt32.Stream.Writer
