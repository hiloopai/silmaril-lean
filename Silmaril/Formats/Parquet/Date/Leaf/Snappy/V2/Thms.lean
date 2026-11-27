module

public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2

open Silmaril.Relational

/-- The original V2 header supplies the PLAIN tag, level lengths, flag and slot count. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {page : DataPage}
    (planned : planData bound frame ordinal = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.snappy.id,
          header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.planData_wire planned

/-- An unsupported original V2 encoding retains its exact tag and coordinate. -/
theorem planData_badTag {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {header : Page.DataV2}
    (kind : frame.value.kind = .dataV2 header) (wrong : header.encoding ≠ 0) :
    planData bound frame ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal frame (.encoding header.encoding))) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.planData_badTag kind wrong

/-- The selected Snappy chunk retains its original frame chain and stored, expanded and row caps. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.checkGroup_wire accepted

/-- The original stored payload supplies the CRC, raw levels and exact Snappy or literal suffix. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {plannedAt readAt : Nat} {slots : Slots}
    (planned : planData bound page.frame plannedAt = .ok page)
    (read : decodePage limits source page readAt = .ok slots) : PageWire limits source page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.decodePage_wire planned read

/-- A stored checksum or extent failure prevents scalar preparation. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source page ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal page.frame (.checksum cause))) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.decodePage_checksum_error failed

/-- After the stored payload check, the scalar cause retains its original ordinal and offset. -/
theorem decodePage_scalar_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {status : Page.Checksum.Status} {cause : ScalarPage.Error}
    (admitted : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status)
    (failed : ScalarPage.decode .int32 page.params limits.scalar
      (Page.Checksum.payloadBytes source page.frame) = .error cause) :
    decodePage limits source page ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal page.frame (.scalar cause))) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.decodePage_scalar_error admitted failed

/-- Group slots concatenate the original pages in order and have the declared row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : SlotsWire limits bound index slots :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.readGroup_wire read

/-- After planning, the earliest failed page preserves its typed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.readGroup_firstPageError admitted split earlier failed

/-- The first indexed source error retains each earlier complete group. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.readAll_firstError opened split earlier failed

/-- The indexed source error takes precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the original descriptor and footer-order signed nullable batches through EOS. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      List.Forall₂ (SlotsWire limits bound) (List.range bound.snapshot.groupCount) groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.V2.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2
