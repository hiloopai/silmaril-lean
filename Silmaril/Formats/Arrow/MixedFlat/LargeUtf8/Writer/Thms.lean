module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Correctness

public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer

/-- A compiled LargeUtf8 field has three i64-offset column parts and
contributes no view count. The signed extent is checked before encoding. -/
theorem compile_largeUtf8 {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : Arrow.LargeUtf8.Column} {physical : OrderedWriter.PhysicalColumn}
    (written : Column.compile limits rows position (.largeUtf8 name nullable values) = .ok physical) :
    values.length = rows ∧ ∃ node,
      Binary.StreamWriter.checkRecordSize .i64 limits.observation.ipc nullable values Arrow.Writer.utf8ByteCount =
        .ok node ∧
      physical = ⟨node, none, Binary.StreamWriter.columnPartsFor .i64
        (Arrow.LargeUtf8.StreamWriter.encodeColumn values)⟩ :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer.compile_largeUtf8 written

/-- Read the exact packed record with its declared schema. This recovers
the ordered fields and nullable values, and binds the original body. -/
theorem Record.readBatch {limits : MixedFlat.Limits} {input : BatchInput}
    (record : Record limits input) {schemaBytes : KBytes}
    (schema : LargeUtf8.readSchema limits.observation.ipc schemaBytes = .ok input.fields) :
    ∃ decoded,
      LargeUtf8.readBatch limits schemaBytes record.output.metadataBytes record.output.body = .ok decoded ∧
      observeBatch decoded = input.observe ∧
      BatchWire limits input.fields record.output.metadata record.output.body decoded :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer.record_readBatch record schema

/-- The complete reader recovers every declared field, ordered nullable
cell and explicit batch count through exact modern EOS. -/
theorem emit_readback {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ decoded eos, Stream.read limits .modern wire = .ok decoded ∧
      Agrees fields batches decoded ∧ decoded.trace.termination = .eos eos ∧
      Stream.StreamWire limits .modern wire decoded ∧
      Arrow.readEnvelope limits.observation.ipc wire eos = .ok .eos ∧ eos + 8 = wire.len :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer.emit_readback written

/-- Every input batch contributes its explicit row count, including when
the ordered list of columns is empty. -/
theorem emit_batch_rows {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ decoded, Stream.read limits .modern wire = .ok decoded ∧
      decoded.trace.batches.map (·.observed.rowCount) = batches.map (·.rowCount) := by
  obtain ⟨decoded, _, read, agrees, _⟩ := emit_readback written
  refine ⟨decoded, read, ?_⟩
  simpa only [List.map_map, Function.comp_def, observeBatch, BatchInput.observe] using
    congrArg (List.map (fun batch : BatchObservation => batch.1)) agrees.2

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer
