module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.Bridges

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.RoundTrip

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature signature eraseBatch ofTrace projectTrace)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (schemaOf)

public section

/-- Composing successful bridges recovers the existing positional Arrow
projection of the original IPC events, with every batch and exact EOS. -/
theorem ipc_projected {limits : Writer.FromIpc.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {input returned : KBytes} {checksum : Bool} {output : Writer.Output}
    {selection : (source : Signature) → Scan.Projection source}
    (imported : Writer.FromIpc.convert limits input checksum = .ok output)
    (exported : Rows.Events.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.reader
      ipc output.bytes selection = .ok returned) :
    ∃ (source : Arrow.RecursiveSchema.Stream.Trace)
      (original : Writer.FromIpc.SourceWire limits.ipc input source),
      let view := selection (signature source.schema.fields)
      Arrow.RecursiveSchema.Stream.Writer.Readback ipc (schemaOf view.schema)
        ((projectTrace view (ofTrace source original.wire)).batches.map eraseBatch) returned :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.ipc_projected imported exported

/-- The identity view recovers the exact recursive declaration and complete
ordered batch observations, including explicit counts and exact EOS. -/
theorem ipc_identity {limits : Writer.FromIpc.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {input returned : KBytes} {checksum : Bool} {output : Writer.Output}
    (imported : Writer.FromIpc.convert limits input checksum = .ok output)
    (exported : Rows.Events.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.reader
      ipc output.bytes = .ok returned) :
    ∃ source, Writer.FromIpc.SourceWire limits.ipc input source ∧
      Arrow.RecursiveSchema.Stream.Writer.Readback ipc source.schema
        (source.batches.map Arrow.RecursiveSchema.Stream.Completed.observed) returned :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.ipc_identity imported exported

/-- Full-field reimport preserves the ordered native groups and their
original signed slot traces, with both files checked at their own limits. -/
theorem parquet_identity {schemaLimits : Snapshot.Limits} {rows : Rows.Limits}
    {limits : Writer.FromIpc.Limits} {input : Bytes} {wire : KBytes} {checksum : Bool} {output : Writer.Output}
    (exported : Rows.Events.ToIpc.convert schemaLimits rows limits.ipc input = .ok wire)
    (imported : Writer.FromIpc.convert limits wire checksum = .ok output) :
    ∃ before after, Tree.openFile schemaLimits input = .ok before ∧
      Tree.openFile limits.parquet.schema.snapshot output.bytes = .ok after ∧
      after.schema.arrow = before.schema.arrow ∧ after.snapshot.groupCount = before.snapshot.groupCount ∧
      ∀ ordinal < before.snapshot.groupCount, ∃ left right,
        Rows.readGroupChecked before.schema rows ordinal = .ok left ∧
        Rows.readGroupChecked after.schema limits.parquet.reader ordinal = .ok right ∧
        left.observation = right.observation ∧
        left.inputs.map (·.original.atoms) = right.inputs.map (·.original.atoms) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.parquet_identity exported imported

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.RoundTrip
