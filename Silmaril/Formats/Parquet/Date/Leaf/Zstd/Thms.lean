module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd

open Silmaril.Relational
open Silmaril.Formats.Compression.Zstd

/-- Group admission retains the original selected chunk, ordered V1 frames, counts and caps. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : Date.Leaf.Gzip.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.checkGroup_wire accepted

/-- The checked codec sees the exact same stored bytes covered by the page checksum check. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits bound metadata page ordinal = .ok slots) :
    PageWire limits bound metadata page slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.decodePage_wire read

/-- One exact Zstandard frame expands the original whole V1 payload into its ordered nullable signed slots. -/
theorem pageWire_exact {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {slots : Slots} (planned : planData bound page.frame = .ok page)
    (read : PageWire limits bound metadata page slots) :
    let source := bound.snapshot.bytes
    let stored := Page.Checksum.payloadBytes source page.frame
    let frameLimits := FlatColumn.Zstd.frameLimits limits.compression
      (limits.pages.scalar.payloadBounds page.params.sizes 0)
    slots.length = page.params.numValues ∧
    ∃ status expanded frameHeader layout sections mask words,
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.pages.scalar.compressedBytes ∧
      (match status with
       | Page.Checksum.Status.absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      CheckedFrame.Huffman.FrameWire frameLimits stored.toList expanded frameHeader ∧
      frameHeader.windowSize ≤ limits.compression.window ∧
      expanded.length = page.frame.value.uncompressedSize ∧
      expanded.length ≤ limits.pages.scalar.uncompressedBytes ∧
      FlatPage.split layout limits.pages.scalar.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues limits.pages.scalar.levels sections.definitions = .ok mask ∧
      Plain.decodeInt32 (mask.count true) sections.scalars = .ok words ∧
      slots.map Option.isSome = mask ∧ slots.filterMap id = words :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.pageWire_exact planned read

/-- Decoded groups concatenate the original pages in order and match the footer row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound checked.selection.column.metadata) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.readGroup_wire read

/-- After header planning, the first failing page keeps its original offset and ordinal. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Date.Leaf.Gzip.CheckedGroup} {page : Date.Leaf.Gzip.DataPage}
    {before after : List (Date.Leaf.Gzip.DataPage × Nat)} {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.selection.column.metadata item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.selection.column.metadata page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.readGroup_firstPageError admitted split earlier failed

/-- The first indexed source failure retains the exact preceding complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.readAll_firstError opened split earlier failed

/-- The original source failure takes precedence over IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.toIpc_firstError opened split earlier failed

/-- Successful native IPC preserves the selected descriptor and each footer-order batch through EOS. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.toIpc_readback written

/-- A stored integrity error is returned before Zstandard decoding. -/
theorem decodePage_checksum_error {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.pages.scalar.compressedBytes bound.snapshot.bytes page.frame = .error cause) :
    decodePage limits bound metadata page ordinal = .error (.checksum ordinal page.frame.header.start cause) := by
  simp [decodePage, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Zstd
