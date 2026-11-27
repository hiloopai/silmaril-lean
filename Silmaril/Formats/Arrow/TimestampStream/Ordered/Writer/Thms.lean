module

public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered.Writer.RoundTrip

public section

namespace Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer

/-- The same limits recover every ordered binding and exact signed nullable batch. -/
theorem emit_readback {limits : ObservationLimits} {fields : List Field} {batches : List Batch} {wire : KBytes}
    (written : emit limits fields batches = .ok wire) :
    TimestampStream.Ordered.read limits.ipc wire = .ok ⟨fields, batches⟩ :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.Writer.emit_readback written

/-- The emitted bytes are the Schema, the records in order, and the exact EOS marker. -/
theorem emit_wire {limits : ObservationLimits} {fields : List Field} {batches : List Batch} {wire : KBytes}
    (written : emit limits fields batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc fields = .ok schema ∧
      (batches.zipIdx.mapM fun (batch, index) =>
        (emitRecord limits.ipc fields batch).mapError (TimestampStream.Ordered.Writer.Error.record index)) =
          .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.Writer.emit_wire written

end Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer
