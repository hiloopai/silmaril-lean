module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Record

public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8

theorem readParsed_sound {limits : MixedFlat.Limits} {fields : List Field}
    {metadata : Metadata} {body : KBytes} {observed : Observed}
    (read : readParsed limits fields metadata body = .ok observed) :
    BatchWire limits fields metadata body observed :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.readParsed_sound read

theorem readBatch_sound {limits : MixedFlat.Limits} {schemaBytes recordBytes body : KBytes}
    {observed : Observed} (read : readBatch limits schemaBytes recordBytes body = .ok observed) :
    ∃ fields metadata, readSchema limits.observation.ipc schemaBytes = .ok fields ∧
      readMetadata limits fields recordBytes = .ok metadata ∧ BatchWire limits fields metadata body observed :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.readBatch_sound read

theorem BatchWire.fields {limits : MixedFlat.Limits} {fields : List Field}
    {metadata : Metadata} {body : KBytes} {observed : Observed}
    (wire : BatchWire limits fields metadata body observed) :
    observed.rowCount = metadata.batch.rowCount ∧ observed.columns.map Prod.fst = fields :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.batch_fields wire

/-- LargeUtf8 consumes its original validity, offset and data slices. The
value witness checks signed i64 geometry and present UTF-8. -/
theorem readColumn_largeUtf8 {limits : MixedFlat.Limits} {body : KBytes} {field : Field} {rows : Nat}
    {group : MixedFlat.Group rows} {values : Arrow.LargeUtf8.Column}
    (kind : field.kind = .largeUtf8)
    (read : readColumn limits body field group = .ok (.largeUtf8 values)) :
    ∃ validity offsets data,
      group.buffers = [validity, offsets, data] ∧
      let buffers : Binary.Buffers :=
        ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets, Body.sliceBuffer body data⟩
      Binary.checkColumn limits.observation.ipc field.nullable group.node buffers = .ok () ∧
      Arrow.LargeUtf8.ColumnWire group.node buffers values :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.largeUtf8_column kind read

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8
