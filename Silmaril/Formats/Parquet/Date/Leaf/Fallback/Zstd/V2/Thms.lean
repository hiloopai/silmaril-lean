module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- The original V2 header fixes the encoding, level extents and resolved compression flag. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧
      (header.encoding = 8 ∨ header.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
        (Date.Leaf.Zstd.columnLayout bound).levels, header.numValues, Payload.Codec.zstd.id,
        header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.planData_wire planned

/-- The original frame order has nonempty reference and PLAIN phases. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.planPages_wire planned

/-- The first return to dictionary encoding after PLAIN is rejected at its original coordinate. -/
theorem planPages_reentry {bound : Bound} {frames : List Page.Frame} {references plain after : List DataPage}
    {reentry : DataPage} {failure : Option GroupError}
    (scanned : Date.Leaf.Fallback.planPrefixWith (planData bound)
      (fun ordinal frame => GroupError.header ordinal frame.header.start) (frames.zipIdx 1) =
      (references ++ plain ++ reentry :: after, failure))
    (hasReferences : references ≠ []) (hasPlain : plain ≠ [])
    (referencesOnly : ∀ page ∈ references, page.params.encoding = 8)
    (plainOnly : ∀ page ∈ plain, page.params.encoding = 0) (tag : reentry.params.encoding = 8) :
    planPages bound frames =
      .error (.sequence (.suffixEncoding (references.length + plain.length + 1) reentry.frame.header.start 8)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.planPages_reentry scanned hasReferences hasPlain referencesOnly plainOnly tag

/-- The selected original chunk supplies the dictionary and both phases. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ Date.Leaf.Fallback.Ordered checked.data :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.checkGroup_wire accepted

/-- The footer slot count and expanded byte cap apply cumulatively across the transition. -/
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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.transition_totals accepted

/-- The selected existing reader supplies the original stored and expanded evidence for its phase. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits bound metadata entries page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes entries page slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.decodePage_wire planned decoded

/-- The original ordered pages account for the exact footer row-group count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.readGroup_wire read

/-- After planning, the first failed page retains its original indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.selection.column.metadata checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.selection.column.metadata checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.readGroup_firstPageError admitted split earlier failed

/-- The first indexed source failure retains the exact preceding complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.readAll_firstError opened split earlier failed

/-- The original source failure takes precedence over IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.toIpc_firstError opened split earlier failed

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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.toIpc_readback written

/-- The original leading dictionary retains its exact stored and regenerated bytes. -/
theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Dictionary.Zstd.V2.DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries :=
  Dictionary.Zstd.V2.readEntries_wire (checkGroup_wire accepted).1.dictionary

/-- Either planned phase returns the whole stored CRC error before body decoding. -/
theorem decodePage_checksum_error {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes bound.snapshot.bytes page.frame = .error cause) :
    decodePage limits bound metadata entries page ordinal =
      .error (if page.params.encoding = 0 then .plain (.checksum ordinal page.frame.header.start cause)
        else .dictionary (.chunk (Dictionary.Snappy.atFrame ordinal page.frame (.checksum cause)))) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.decodePage_checksum_error failed

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2
