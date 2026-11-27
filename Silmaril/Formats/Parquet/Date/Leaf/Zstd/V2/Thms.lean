module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Thms
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2

open Silmaril.Relational

/-- The original V2 header fixes the PLAIN slot parameters, level lengths and resolved flag. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {page : Date.Leaf.Gzip.DataPage}
    (planned : planData bound frame ordinal = .ok page) :
    page.frame = frame ∧ ∃ data, frame.value.kind = .dataV2 data ∧ data.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          (Date.Leaf.Zstd.columnLayout bound).levels, data.numValues, Payload.Codec.zstd.id,
          data.encoding, .v2 data.numNulls data.numRows data.repetitionBytes
            data.definitionBytes (some data.isCompressed)⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.planData_wire planned

/-- The selected original chunk bounds the frame chain and exact group count. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : Date.Leaf.Gzip.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.checkGroup_wire accepted

/-- The original level prefix supplies the mask and only the flag-selected suffix supplies values. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {ordinal plannedOrdinal : Nat} {slots : Slots}
    (planned : planData bound page.frame plannedOrdinal = .ok page)
    (read : decodePage limits bound metadata page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes page slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.decodePage_wire planned read

/-- The original checked frames supply all ordered signed nullable slots at the footer row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.readGroup_wire read

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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.readGroup_firstPageError admitted split earlier failed

/-- The first indexed source failure retains the exact preceding complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.readAll_firstError opened split earlier failed

/-- The original source failure takes precedence over IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.toIpc_firstError opened split earlier failed

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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2.toIpc_readback written

/-- The whole stored CRC failure takes precedence over level splitting and scalar decoding. -/
theorem decodePage_checksum_error {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Gzip.DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.pages.scalar.compressedBytes bound.snapshot.bytes page.frame = .error cause) :
    decodePage limits bound metadata page ordinal =
      .error (.zstd (.checksum ordinal page.frame.header.start cause)) := by
  simp [decodePage, Zstd.decodePage_checksum_error failed, Except.mapError]

end Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2
