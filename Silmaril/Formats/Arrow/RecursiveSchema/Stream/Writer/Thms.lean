module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.Construction
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.Readback

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer

/-- Assembly preserves the exact consecutive byte regions and lengths. -/
theorem assemble_extent (schemaFrame : KBytes) (frames : List KBytes) :
    (assemble schemaFrame frames).len = schemaFrame.len + (frames.map KBytes.len).sum + 8 ∧
      (assemble schemaFrame frames).toList =
        schemaFrame.toList ++ frames.flatMap KBytes.toList ++ StreamWriter.eos.toList :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.assemble_extent schemaFrame frames

theorem serialize_over_batch_limit {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    (over : batches.length > limits.schema.ipc.batches) :
    serialize limits schema batches = .error (.batchLimit batches.length limits.schema.ipc.batches) := by
  simp [serialize, over]

theorem serialize_batch_error {limits : Batch.Limits} {schema : Schema}
    {batches : List Observation} {ordinal : Nat} {cause : Batch.Writer.Error}
    (failed : serialize limits schema batches = .error (.batch ordinal cause)) :
    RecordFailure limits schema 0 batches ordinal cause :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.serialize_batch_error failed

theorem emit_serialize_error {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    {cause : Error} (failed : serialize limits schema batches = .error cause) :
    emit limits schema batches = .error cause := by
  simp [emit, failed, bind, Except.bind]

/-- An indexed emission failure identifies the first refused input batch
and witnesses a complete serialized frame for each earlier observation. -/
theorem emit_batch_error {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    {ordinal : Nat} {cause : Batch.Writer.Error}
    (failed : emit limits schema batches = .error (.batch ordinal cause)) :
    RecordFailure limits schema 0 batches ordinal cause :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.emit_batch_error failed

theorem serialize_wire {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : serialize limits schema batches = .ok wire) :
    Construction limits schema batches wire :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.serialize_wire written

theorem emit_construction {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    Construction limits schema batches wire :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.emit_construction written

/-- Success certifies the original schema and ordered logical observations
through the exact modern EOS, with the independent reader cursor chain. -/
theorem emit_readback {limits : Batch.Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    Readback limits schema batches wire :=
  (Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.emit_serialized written).2

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer
