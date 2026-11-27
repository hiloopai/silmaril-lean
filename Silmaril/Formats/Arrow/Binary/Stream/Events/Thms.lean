module

public import Silmaril.Formats.Arrow.Binary.Stream.Events.Defs
import Silmaril.Proofs.Formats.Arrow.Binary.Stream.Events.Agreement

public section

namespace Silmaril.Formats.Arrow.Binary.Stream.Events

theorem schema_exact (field : Binary.Field) :
    (schema field).width = 1 ∧ ∀ i, (schema field).kind i = (field, .binary) :=
  ⟨rfl, fun _ => rfl⟩

theorem ofBatch_exact (field : Binary.Field) (record : Stream.Batch) :
    (ofBatch field record).rowCount = record.values.length ∧
      ∀ i, (ofBatch field record).values i = record.values :=
  ⟨rfl, fun _ => rfl⟩

theorem next_exact (limits : Limits) (framing : Stream.Framing) (field : Binary.Field)
    (source : Stream.Cursor) :
    (reader limits framing).next (.at field source) =
      (source.next.mapError .record).map
        (Option.map fun (record, after) => (ofBatch field record, .at field after)) :=
  rfl

/-- The standard driver's sufficient fuel follows the native cursor through
the same ordered record prefix and terminal reply. -/
theorem pull_exact (limits : Limits) (framing : Stream.Framing)
    (field : Binary.Field) (source : Stream.Cursor) :
    Arrow.Events.BatchReader.read.pull (reader limits framing) (schema field)
      (source.remaining + 1) (.at field source) [] = ofTrace field source.drain :=
  Proofs.Formats.Arrow.Binary.Stream.Events.pull_exact limits framing field source

/-- Exact agreement retains the original descriptor, every event boundary
including empty batches, and the terminal outcome. -/
theorem readAll_exact (limits : Limits) (framing : Stream.Framing) (input : KBytes) :
    readAll limits framing input =
      (((Stream.readAll limits framing input).mapError .schema).map fun (field, trace) =>
        ⟨schema field, ofTrace field trace⟩) :=
  Proofs.Formats.Arrow.Binary.Stream.Events.readAll_exact limits framing input

/-- The first failed pull preserves the completed native prefix, original
zero-based record ordinal, byte offset, and typed nested failure. -/
theorem readAll_failure {limits : Limits} {framing : Stream.Framing} {input : KBytes}
    {field : Binary.Field} {trace : Stream.Trace} {failure : Stream.Failure}
    (native : Stream.readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    ∃ start final, Stream.SchemaWire limits framing input start ∧ start.field = field ∧
      Stream.Prefix start trace.batches final ∧
      readAll limits framing input = .ok ⟨schema field,
        ⟨trace.batches.map (ofBatch field), .readError (.record failure)⟩⟩ ∧
      failure.ordinal = trace.batches.length ∧ failure.offset = final.offset ∧
      final.next = .error failure :=
  Proofs.Formats.Arrow.Binary.Stream.Events.readAll_failure native failed

end Silmaril.Formats.Arrow.Binary.Stream.Events
