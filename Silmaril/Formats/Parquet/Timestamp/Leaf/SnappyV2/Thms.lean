module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original selected chunk supplies all contiguous frames and the checked row
count. -/
theorem checkGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    selectChunk {limits with allowSnappy := true} bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.checkGroup_wire checked

/-- A successful decode uses the original V2 header and its verified stored payload. -/
theorem decodePage_wire {limits : ScalarPage.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)} (read : decodePage limits bound frame ordinal = .ok slots) :
    PageWire limits bound frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.decodePage_wire read

/-- The stored CRC covers the original level prefix and stored value suffix. V2
preparation retains the exact raw levels, codec-selected value bytes, mask and
signed words. -/
theorem pageWire_prepared {limits : ScalarPage.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {slots : List (Option Int64)} (wire : PageWire limits bound frame slots) :
    let stored := Leaf.Internal.body bound frame
    ∃ info status params layout prepared words,
      frame.value.kind = .dataV2 info ∧
      params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.snappy.id, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
          (some info.isCompressed)⟩ ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
      (match status with
       | Parquet.Page.Checksum.Status.absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      params.sizes.uncompressed ≤ limits.uncompressedBytes ∧
      ScalarPage.validate params limits stored = .ok layout ∧
      ScalarPage.PreparedWire params limits layout stored prepared ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.pageWire_prepared wire

/-- The group preserves frame order, nullable signed ticks and the checked footer row
count. -/
theorem readGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire limits.page bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.readGroup_wire read

/-- After successful framing and count admission, page decoding returns the first
failure in frame order. -/
theorem readGroup_first_page_error {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits.page bound item i) = .ok outputs)
    (failed : decodePage limits.page bound frame ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.readGroup_first_page_error checked split earlier failed

/-- Native IPC readback through EOS has the retained descriptor and one batch per
original footer ordinal, with the exact signed nullable counts. -/
theorem convert_readback {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        List.Forall₂ (fun index counts =>
          ∃ slots, readGroup inputLimits.leaf bound index = .ok slots ∧
            counts = slots.map (Option.map Ticks.ticks))
          (List.range bound.snapshot.groupCount)
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2.convert_readback written

/-- A refused stored checksum retains the original page ordinal and absolute
header offset before level or value decoding. -/
theorem decodePage_checksum_error {limits : ScalarPage.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {ordinal : Nat} {info : Parquet.Page.DataV2}
    {cause : Parquet.Page.Checksum.Error}
    (version : frame.value.kind = .dataV2 info)
    (failed : Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .error cause) :
    decodePage limits bound frame ordinal = .error (.pageChecksum ordinal frame.header.start cause) := by
  simp [decodePage, version, failed, Except.mapError, Bind.bind, Except.bind]

/-- A failed footer group retains precisely the earlier complete batches. -/
theorem readBound_first_error {limits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readBound limits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The original source error is returned before native writer admission. -/
theorem convert_first_error {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup inputLimits.leaf bound) = .ok groups)
    (failed : readGroup inputLimits.leaf bound index = .error cause) :
    convert inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2
