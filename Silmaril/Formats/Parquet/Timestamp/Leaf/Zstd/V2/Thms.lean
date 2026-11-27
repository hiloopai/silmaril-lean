module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The selected chunk retains its checked extent, original frame chain and both byte budgets. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits leafLimits bound index = .ok group) :
    selectChunkWith .zstdPlainV2 leafLimits bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      group.chunk.span.stop - group.chunk.span.start ≤ limits.maxStoredChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.checkGroup_wire checked

/-- The exact original CRC-covered page determines the mask, signed words and bounded suffix. -/
theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodePage limits leafLimits bound frame ordinal = .ok slots) :
    PageWire limits leafLimits bound frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.decodePage_wire read

/-- An original stored checksum failure precedes decode. -/
theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {ordinal : Nat} {header : Parquet.Page.DataV2}
    {cause : Parquet.Page.Checksum.Error} (v2 : frame.value.kind = .dataV2 header)
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame = .error cause) :
    decodePage limits leafLimits bound frame ordinal = .error (.checksum ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.decodePage_checksum_error v2 failed

/-- Group slots come from the original frames in order and have the declared row count. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ group pages, checkGroup limits leafLimits bound index = .ok group ∧
      List.Forall₂ (PageWire limits leafLimits bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.readGroup_wire read

/-- Once group admission succeeds, the first failing page retains its indexed cause. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (checked : checkGroup limits leafLimits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound frame ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.readGroup_first_page_error checked split earlier failed

/-- Events follow the original footer group order on the retained snapshot. -/
theorem readBound_reference (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Reader.denoteGroups (rowsAt limits leafLimits bound) (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.readBound_reference limits leafLimits bound

/-- A failed group retains the complete earlier groups and typed original cause. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.readBound_first_error split earlier failed

/-- The first original source error precedes native writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.convert_first_error opened split earlier failed

/-- Native IPC recovers the original descriptor and ordered signed nullable batches through EOS. -/
theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits inputLimits.leaf bound) = .ok groups ∧
      readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2
