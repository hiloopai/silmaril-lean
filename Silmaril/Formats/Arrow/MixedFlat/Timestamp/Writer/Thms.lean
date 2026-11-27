module

public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer.Readback

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer

/-- A successful record packs the compiled original fields in descriptor order. -/
theorem emitRecord_wire {limits : ObservationLimits} {fields : List Field} {batch : Batch}
    {wire : KBytes} (written : emitRecord limits fields batch = .ok wire) :
    ∃ columns,
      checkRecord limits fields batch = .ok () ∧
      ((fields.zip batch.columns).zipIdx.mapM fun ((field, column), position) =>
        compile limits batch.rowCount field column position) = .ok columns ∧
      let (buffers, body) := Arrow.Writer.packBuffers 0 (columns.flatMap Prod.snd)
      let record : RecordBatch := ⟨batch.rowCount, columns.map Prod.fst, buffers⟩
      StreamWriter.emitFrame limits.ipc ⟨.recordBatch record, body.len⟩ body = .ok wire :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer.emitRecord_wire written

/-- The checked reader recovers all positional fields, batches and typed values. -/
theorem emit_readback {limits : ObservationLimits} {stream : Stream} {wire : KBytes}
    (written : emit limits stream = .ok wire) : Timestamp.read limits wire = .ok stream :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer.emit_readback written

/-- The wire contains one ordered Schema, the original batch order and exact EOS. -/
theorem emit_wire {limits : ObservationLimits} {stream : Stream} {wire : KBytes}
    (written : emit limits stream = .ok wire) :
    ∃ schema records,
      emitSchema limits.ipc stream.fields = .ok schema ∧
      (stream.batches.zipIdx.mapM fun (batch, index) =>
        (emitRecord limits stream.fields batch).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer.emit_wire written

end Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer
