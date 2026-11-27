module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs
public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs

/-! Independent intermediate and sink admission for the seconds round trip. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence

/-- The outer file, group, and row limits are independent of the matched
Snapshot and Leaf checks used to certify the intermediate file. -/
structure MiddleBounds (limits : ToIpc.Limits) (middle : Bytes)
    (original : Arrow.TimestampStream.Stream) : Prop where
  fileBytes : middle.length ≤ limits.maxFileBytes
  groups : original.batches.length ≤ limits.maxGroups
  rows : FromIpc.totalRows original ≤ limits.maxTotalRows

/-- The native writer's own serialization and normalized readback checks.
This witness can be obtained from the original Arrow stream independently
of the intermediate file and the inverse converter. -/
def SinkAdmits (limits : Arrow.ObservationLimits) (original : Arrow.TimestampStream.Stream)
    (wire : KBytes) : Prop :=
  Arrow.TimestampStream.Writer.Internal.serialize limits original.binding original.batches = .ok wire ∧
    ∃ result, Arrow.TimestampStream.read limits.ipc wire = .ok result ∧
      Arrow.TimestampStream.Writer.descriptor result.binding =
        Arrow.TimestampStream.Writer.descriptor original.binding ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        original.batches.map Arrow.TimestampBatch.Writer.tickCounts

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence
