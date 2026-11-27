module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Guarantee

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence

/-- The sink witness is exactly the native writer's admission relation. -/
theorem emit_iff_sink {limits : Arrow.ObservationLimits} {original : Arrow.TimestampStream.Stream}
    {wire : KBytes} :
    Arrow.TimestampStream.Writer.emit limits original.binding original.batches = .ok wire ↔
      SinkAdmits limits original wire :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.emit_iff_sink

/-- A successful exact numeric recovery yields a successful indexed inverse rescale. -/
theorem rescale_of_recovery {bound : Bound} {groups : List (Slots bound)}
    {counts : List (List (Option Int))}
    (fields : bound.snapshot.metadata.schema.length = 2)
    (unit : bound.binding.descriptor.unit = .millis)
    (recover : FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
      some counts) :
    ∃ batches, rescaleGroups bound groups = .ok batches ∧
      batches.map Arrow.TimestampBatch.Writer.tickCounts = counts :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.rescale_of_recovery fields unit recover

/-- Forward success and matching intermediate settings ensure exact inverse rescaling. -/
theorem rescale_writer_image {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle) :
    ∃ original bound groups batches,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      Leaf.openLeaf readLimits.snapshot middle 1 = .ok bound ∧
      readGroups readLimits.leaf bound = .ok groups ∧
      rescaleGroups bound groups = .ok batches ∧
      (⟨binding bound, batches⟩ : Arrow.TimestampStream.Stream) = original ∧
      bound.snapshot.groupCount = original.batches.length ∧
      bound.snapshot.metadata.numRows.toNat = FromIpc.totalRows original :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.rescale_writer_image sameSnapshot sameLeaf written

/-- For any independently admitted sink bytes, the inverse emits those bytes and recovers the full source stream. -/
theorem roundtrip_of_sink {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle) :
    ∃ original, Arrow.TimestampStream.read ipc input = .ok original ∧
      ∀ wire, MiddleBounds readLimits middle original → SinkAdmits outputLimits original wire →
        convert readLimits outputLimits middle = .ok wire ∧
        Arrow.TimestampStream.read outputLimits.ipc wire = .ok original :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.roundtrip_of_sink sameSnapshot sameLeaf written

/-- Outer read bounds and a separate sink witness suffice for a complete inverse round trip. -/
theorem roundtrip_exists {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle)
    (fits : ∀ original, Arrow.TimestampStream.read ipc input = .ok original →
      MiddleBounds readLimits middle original)
    (admitted : ∀ original, Arrow.TimestampStream.read ipc input = .ok original →
      ∃ output, SinkAdmits outputLimits original output) :
    ∃ original output, Arrow.TimestampStream.read ipc input = .ok original ∧
      convert readLimits outputLimits middle = .ok output ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok original :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.roundtrip_exists sameSnapshot sameLeaf written fits admitted

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence
