module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Delta.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Delta

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original selected codec, data offset, contiguous frames and declared row count. -/
theorem checkGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    Leaf.selectChunkWith .deltaBinaryPacked limits bound index = .ok group.chunk ∧
      bound.snapshot.groupAt index = some group.chunk.group ∧
      group.chunk.group.columns[bound.ordinal - 1]? = some group.chunk.column ∧
      (group.chunk.column.metadata.codec = 0 ∨ group.chunk.column.metadata.codec = 1) ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset ∧
      (group.chunk.span.stop : Int) =
        group.chunk.column.metadata.dataPageOffset + group.chunk.column.metadata.totalCompressedSize ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.checkGroup_wire checked

/-- Decoding retains the original CRC-covered slice and exact delta word stream. -/
theorem decodePage_wire {packed : DeltaBinaryPacked.Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {slots : List (Option Int64)} (read : decodePage packed limits bound codec frame ordinal = .ok slots) :
    PageWire packed limits bound codec frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.decodePage_wire read

/-- Both page versions bind the exact byte extents to the original header and reconstructed words. -/
theorem pageWire_extents {packed : DeltaBinaryPacked.Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire packed limits bound codec frame slots) :
    let stored := Leaf.Internal.body bound frame
    ∃ (prepared : ScalarPage.Prepared) (stream : DeltaBinaryPacked.Stream),
      prepared.scalars.toList = stream.wire ∧ slots.filterMap id = stream.reconstruct .int64 ∧
      match frame.value.kind with
      | .dataV1 header =>
        header.encoding = 5 ∧ ∃ expanded layout sections,
          ScalarPage.ExactPayload frame.value.compressedSize frame.value.uncompressedSize
            codec stored.toList expanded ∧
          FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
          FlatPage.readMask layout header.numValues limits.levels sections.definitions = .ok prepared.mask ∧
          sections.scalars = prepared.scalars
      | .dataV2 header =>
        header.encoding = 5 ∧ header.repetitionBytes = 0 ∧ header.numRows = header.numValues ∧
        header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
        ∃ (definitions : Bytes) (suffix : List UInt8) (layout : FlatPage.Layout),
          definitions.length = header.definitionBytes ∧ stored.toList = definitions.toList ++ suffix ∧
          FlatPage.readMask layout header.numValues limits.levels definitions = .ok prepared.mask ∧
          (slots.filterMap id).length = header.numValues - header.numNulls ∧
          ScalarPage.ExactPayload (frame.value.compressedSize - header.definitionBytes)
            (frame.value.uncompressedSize - header.definitionBytes)
            (ScalarPage.v2Codec codec (some header.isCompressed)) suffix prepared.scalars.toList
      | _ => False :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.pageWire_extents wire

/-- Each present word folds the preceding deltas in signed Int64 modular arithmetic. -/
theorem reconstruct_signed (stream : DeltaBinaryPacked.Stream) (index : Nat)
    (bounded : index < (stream.reconstruct .int64).length) :
    ((stream.reconstruct .int64)[index]).toInt =
      (stream.deltas.take index).foldl (fun previous delta => (previous + delta).bmod (2^64))
        (Int64.ofInt stream.header.first).toInt :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.reconstruct_signed stream index bounded

/-- The original frame sequence preserves exact footer rows and signed nullable ticks. -/
theorem readGroup_wire {packed : DeltaBinaryPacked.Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup packed limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire packed limits.page bound group.chunk.column.metadata.codec) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.readGroup_wire read

/-- After admission the first failing page retains its exact cause in frame order. -/
theorem readGroup_first_page_error {packed : DeltaBinaryPacked.Limits} {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage packed limits.page bound group.chunk.column.metadata.codec item i) = .ok outputs)
    (failed : decodePage packed limits.page bound group.chunk.column.metadata.codec frame ordinal = .error cause) :
    readGroup packed limits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.readGroup_first_page_error checked split earlier failed

/-- Native Arrow IPC retains the descriptor and original per-group ticks through EOS. -/
theorem convert_readback {packed : DeltaBinaryPacked.Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert packed inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        List.Forall₂ (fun index counts =>
          ∃ slots, readGroup packed inputLimits.leaf bound index = .ok slots ∧
            counts = slots.map (Option.map Ticks.ticks))
          (List.range bound.snapshot.groupCount)
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Delta.convert_readback written

/-- A failed CRC preempts delta preparation and retains the original offset. -/
theorem decodePage_checksum_error {packed : DeltaBinaryPacked.Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .error cause) :
    decodePage packed limits bound codec frame ordinal = .error (.pageChecksum ordinal frame.header.start cause) := by
  simp [decodePage, failed, Except.mapError, Bind.bind, Except.bind]

/-- A failed footer group retains precisely the earlier complete batches. -/
theorem readBound_first_error {packed : DeltaBinaryPacked.Limits} {limits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup packed limits bound) = .ok groups)
    (failed : readGroup packed limits bound index = .error cause) :
    readBound packed limits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The original source error is returned before native writer admission. -/
theorem convert_first_error {packed : DeltaBinaryPacked.Limits} {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup packed inputLimits.leaf bound) = .ok groups)
    (failed : readGroup packed inputLimits.leaf bound index = .error cause) :
    convert packed inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Delta
