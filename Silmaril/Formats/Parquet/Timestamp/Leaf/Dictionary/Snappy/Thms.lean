module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats

/-- The CRC status describes exactly the stored source slice, including its
bounded extent and the digest when a CRC is present. -/
theorem stored_verified {cap : Nat} {bound : Bound} {frame : Parquet.Page.Frame}
    {status : Parquet.Page.Checksum.Status}
    (verified : Parquet.Page.Checksum.verify cap bound.snapshot.bytes frame = .ok status) :
    let stored := Leaf.Internal.body bound frame
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.stored_verified verified

/-- The original dictionary page tag selects the bounded Snappy PLAIN-word decoder. -/
theorem readEntriesWith_wire {tag : DictionaryTag} {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntriesWith tag limits leafLimits bound frame = .ok entries) :
    ∃ header status expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = tag.id ∧
      header.numValues ≤ limits.maxEntries ∧
      Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
        bound.snapshot.bytes frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Leaf.Internal.body bound frame).toList expanded ∧
      expanded.length = frame.value.uncompressedSize ∧
      expanded.length ≤ (dictionaryBounds limits leafLimits frame).outputLimit ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readEntriesWith_wire read

/-- The original stored dictionary is verified before expansion into exact
bounded PLAIN signed words. -/
theorem readEntries_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntries limits leafLimits bound frame = .ok entries) :
    ∃ header status expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
        bound.snapshot.bytes frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Leaf.Internal.body bound frame).toList expanded ∧
      expanded.length = frame.value.uncompressedSize ∧
      expanded.length ≤ (dictionaryBounds limits leafLimits frame).outputLimit ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readEntries_wire read

/-- Admitted codec-1 header parameters stay tied to their original frame. -/
theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
        .ok page.params ∧ admits page.params.encoding = true :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.planDataWith_wire planned

/-- The original data header supplies its Snappy scalar parameters and
RLE_DICTIONARY tag. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
        .ok page.params ∧ page.params.encoding = 8 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.planData_wire planned

/-- The selected codec-1 chunk preserves the original contiguous frames,
footer offsets and declared slot count. -/
theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = 1 ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.checkGroup_wire accepted

/-- The original stored data payload passes its extent and CRC check before
the index decoder observes the nullable slots. -/
theorem decodePage_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    DataWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.decodePage_wire read

/-- Scalar admission bounds the advertised expanded size. -/
theorem expanded_bound {encoding : Int} {params : ScalarPage.Parameters}
    {limits : ScalarPage.Limits} {source : Bytes} {layout : FlatPage.Layout}
    (checked : ScalarPage.validateFor encoding params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.expanded_bound checked

/-- The checked V1/V2 preparation supplies the exact expanded or raw index
slice, its mask and the same dictionary lookups within the output budget. -/
theorem data_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (read : DataWire limits leafLimits bound entries.toArray page slots) :
    ∃ status layout prepared width runs indices,
      Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ leafLimits.page.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.data_decodes read

/-- Decode an admitted chunk against its dictionary in its original page order. -/
theorem readGroupUsing_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {admission : Except Leaf.Error CheckedChunk} {slots : Slots bound}
    (read : readGroupUsing limits leafLimits bound admission = .ok slots) :
    ∃ checked pages, admission = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = (checked.data.map (·.params.numValues)).sum :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readGroupUsing_wire read

/-- The group preserves all physical page slots in frame order and interprets
them under the retained descriptor. -/
theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readGroup_wire read

/-- Return the first failed data page in an admitted chunk. -/
theorem readGroupUsing_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {ordinal : Nat} {admission : Except Leaf.Error CheckedChunk} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : admission = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroupUsing limits leafLimits bound admission = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readGroupUsing_first_page_error admitted split earlier failed

/-- After successful planning, the first failed data page returns its
original typed error. -/
theorem readGroup_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.readGroup_first_page_error admitted split earlier failed

/-- A refused dictionary checksum precludes Snappy expansion. -/
theorem readEntries_checksum_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {header : Parquet.Page.Dictionary}
    {cause : Parquet.Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary header) (encoding : header.encoding = 0)
    (count : header.numValues ≤ limits.maxEntries)
    (size : (dictionaryBounds limits leafLimits frame).expectedSize ≤
      (dictionaryBounds limits leafLimits frame).outputLimit)
    (failed : Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
      bound.snapshot.bytes frame = .error cause) :
    readEntries limits leafLimits bound frame = .error (.checksumFailure cause) := by
  simp [readEntries, readEntriesWith, DictionaryTag.id, kind, encoding, Nat.not_lt.mpr count, Nat.not_lt.mpr size, failed,
    Except.mapError, Bind.bind, Except.bind]

/-- A refused data checksum keeps its wire ordinal and original header offset. -/
theorem decodePage_checksum_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat}
    {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.checksumFailure cause)) := by
  simp [decodePage, verifyData, failed, Except.mapError, Bind.bind, Except.bind, atFrame]

/-- The event trace observes the same checked group reads in footer order. -/
theorem readBound_reference (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Events.referenceGroupsWith (readGroup limits leafLimits bound)
      (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Events.rows bound), reference.2⟩⟩ :=
  Events.readBoundWith_reference bound (readGroup limits leafLimits bound)

/-- A group error retains exactly the earlier complete footer groups. -/
theorem readBound_first_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The native IPC reader recovers the retained descriptor and ordered
nullable signed ticks of all complete footer groups. -/
theorem convert_readback {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert profile limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroups_readback written

/-- The first failed footer group carries the same original typed error
before any IPC writer admission. -/
theorem convert_first_error {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert profile limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy
