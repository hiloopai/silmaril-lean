module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- Only original V2 frames with an admitted encoding supply the plan parameters. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧
      (header.encoding = 8 ∨ header.encoding = 0) ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
          header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.planData_wire planned

/-- Planning preserves the original ordered frames and both nonempty phases. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.planPages_wire planned

/-- The checked group retains the original selection, frame chain, and declared offsets. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (Date.Leaf.Fallback.Gzip.readEntries limits)
      (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.checkGroup_wire accepted

/-- The dictionary and both data phases share one expansion cap.
Both data phases contribute to the declared group row count. -/
theorem transition_totals {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    ∃ references plain, checked.data = references ++ plain ∧ references ≠ [] ∧ plain ≠ [] ∧
      (∀ page ∈ references, page.params.encoding = 8) ∧
      (∀ page ∈ plain, page.params.encoding = 0) ∧
      (references.map (·.params.numValues)).sum + (plain.map (·.params.numValues)).sum =
        checked.selection.group.numRows.toNat ∧
      checked.dictionary.value.uncompressedSize +
        ((references.map (·.frame.value.uncompressedSize)).sum +
          (plain.map (·.frame.value.uncompressedSize)).sum) ≤ limits.maxExpandedChunkBytes :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.transition_totals accepted

/-- The original checksummed dictionary frame supplies the bounded GZIP member
and the signed dictionary entries used by the reference prefix. -/
theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    let frame := checked.dictionary
    let source := bound.snapshot.bytes
    let bounds := Date.Leaf.Dictionary.Snappy.dictionaryBounds limits.toDictionaryLimits frame
    ∃ header expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Date.Leaf.Fallback.Gzip.StoredMember source frame bounds.compressedLimit bounds.outputLimit expanded ∧
      Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok checked.entries ∧
      checked.entries.length = header.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.checkGroup_dictionary accepted

/-- Both data phases retain the original raw levels, exact suffix,
and ordered signed nullable slots. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.decodePage_wire planned decoded

/-- The admitted frames account for every ordered slot at the declared row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (Date.Leaf.Fallback.Gzip.readEntries limits)
        (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.readGroup_wire read

/-- After planning, the first original body failure retains its indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.readGroup_firstPageError admitted split earlier failed

/-- The trace keeps earlier complete batches and the original group index and cause. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.readAll_firstError opened split earlier failed

/-- A source failure takes precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the descriptor and one ordered batch per
original footer group through EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.toIpc_readback written

/-- An original stored CRC error precedes V2 level splitting and suffix decoding. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source entries page ordinal = .error (.chunk (.page ordinal page.frame.header.start
      (.checksum cause))) := by
  simp [decodePage, Gzip.decodePageWith, Date.Leaf.Dictionary.Snappy.verifyData, Date.Leaf.Dictionary.Snappy.atFrame,
    failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2
