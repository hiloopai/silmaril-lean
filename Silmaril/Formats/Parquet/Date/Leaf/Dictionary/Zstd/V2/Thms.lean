module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- The original tag-8 V2 header fixes the selected slot, level and flag parameters. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ page.params.encoding = 8 ∧
      ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
        page.params =
          ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
            (Date.Leaf.Zstd.columnLayout bound).levels, header.numValues, Payload.Codec.zstd.id,
            header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
              header.definitionBytes (some header.isCompressed)⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.planData_wire planned

/-- Planning retains the original page order. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.planPages_wire planned

/-- Planning returns the first inadmissible original header at its original offset. -/
theorem planPages_firstError {bound : Bound} {frames : List Page.Frame}
    {before after : List (Page.Frame × Nat)} {frame : Page.Frame} {ordinal : Nat}
    {pages : List DataPage} {cause : HeaderError}
    (split : frames.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (GroupError.header i item.header.start)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    planPages bound frames = .error (.header ordinal frame.header.start cause) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.planPages_firstError split earlier failed

/-- The original selected frames contain one leading dictionary and a nonempty strict reference phase. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      ∀ page ∈ checked.data, page.params.encoding = 8 :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.checkGroup_wire accepted

/-- The whole stored dictionary yields one bounded Zstandard frame and exact signed entries. -/
theorem readEntries_wire {limits : Limits} {source : Bytes} {frame : Page.Frame} {entries : List Int32}
    (read : readEntries limits source frame = .ok entries) : DictionaryWire limits source frame entries :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.readEntries_wire read

/-- The dictionary witness is tied to the original selected chunk and its decoded entries. -/
theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.checkGroup_dictionary accepted

/-- The original raw levels and flag-selected Hybrid references yield exact ordered nullable slots. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.decodePage_wire planned decoded

/-- The original ordered pages account for the exact footer row-group count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ (∀ page ∈ checked.data, page.params.encoding = 8) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.readGroup_wire read

/-- After planning, the first failed page retains its original indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.readGroup_firstPageError admitted split earlier failed

/-- The first indexed source failure retains the exact preceding complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.readAll_firstError opened split earlier failed

/-- The original source failure takes precedence over IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.toIpc_firstError opened split earlier failed

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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.toIpc_readback written

/-- With an admitted dictionary header, the stored CRC error precedes payload expansion. -/
theorem readEntries_checksum_error {limits : Limits} {source : Bytes} {frame : Page.Frame}
    {data : Page.Dictionary} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary data) (encoding : data.encoding = 0)
    (cap : data.numValues ≤ limits.maxEntries)
    (failed : Page.Checksum.verify (Snappy.dictionaryBounds limits.toChunkLimits frame).compressedLimit
      source frame = .error cause) : readEntries limits source frame = .error (.checksum cause) := by
  simp [readEntries, kind, encoding, Nat.not_lt_of_ge cap, failed, Except.mapError, Bind.bind, Except.bind]

/-- A stored data CRC error precedes level interpretation and scalar expansion. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source entries page ordinal =
      .error (.chunk (Snappy.atFrame ordinal page.frame (.checksum cause))) := by
  simp [decodePage, Snappy.verifyData, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2
