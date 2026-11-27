module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy

open Silmaril.Relational
open Silmaril.Formats
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- The leading dictionary and both data segments use the original contiguous
frames and the original footer offsets and counts. -/
theorem checkGroup_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = 1 ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Dictionary.Snappy.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, Dictionary.Snappy.planDataWith Fallback.admits bound page.frame = .ok page) ∧
      Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.checkGroup_wire accepted

/-- The checked header selects the exact physical decoder for that payload. -/
theorem decodePage_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : Fallback.admits page.params.encoding = true)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    DataWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.decodePage_wire admitted read

/-- The dictionary branch supplies the same checked index-decoder input as
the Snappy dictionary-only reader. -/
theorem dictionary_decodes {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (tag : page.params.encoding = 8) (read : DataWire limits leafLimits bound entries page slots) :
    Dictionary.Snappy.DataWire limits leafLimits bound entries page slots := by
  obtain ⟨status, verified, _, references | plain⟩ := read
  · exact ⟨status, verified, references.2⟩
  · exact (by decide : ¬ (8 : Int) = 0) (tag.symm.trans plain.1) |>.elim

/-- The PLAIN branch supplies the exact bounded V1 or V2 scalar layout and
decodes one signed word for every present slot. -/
theorem plain_decodes {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (plain : page.params.encoding = 0) (read : DataWire limits leafLimits bound entries page slots) :
    ∃ status layout prepared words,
      Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ leafLimits.page.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.plain_decodes plain read

/-- The group concatenates the two data segments in wire order, retaining the
selected descriptor and the declared number of nullable signed slots. -/
theorem readGroup_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.readGroup_wire read

/-- Once planning succeeds, the original error at the first failing
data page is returned after the preceding pages decode. -/
theorem readGroup_first_page_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {referencePages : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok referencePages)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.readGroup_first_page_error admitted split earlier failed

/-- A stored data checksum error keeps its wire ordinal and header offset. -/
theorem decodePage_checksum_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat}
    {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.checksumFailure cause)) := by
  simp [decodePage, Dictionary.Snappy.verifyData, failed, Except.mapError, Bind.bind, Except.bind,
    Dictionary.atFrame]

/-- After stored verification, a dictionary data error retains its original
reference cause, wire ordinal and absolute header offset. -/
theorem decodePage_dictionary_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat}
    {status : Parquet.Page.Checksum.Status} {cause : DictionaryIndex.Error}
    (verified : Dictionary.Snappy.verifyData leafLimits bound page ordinal = .ok status)
    (tag : page.params.encoding = 8)
    (failed : DictionaryIndex.decode entries page.params leafLimits.page limits.indices
      (Leaf.Internal.body bound page.frame) = .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.references cause)) := by
  simp [decodePage, verified, Bind.bind, Except.bind, Fallback.decodePage, tag,
    Dictionary.decodePage, failed, Except.mapError, Dictionary.atFrame]

/-- After stored verification, a PLAIN suffix error retains its payload cause,
wire ordinal and absolute header offset. -/
theorem decodePage_plain_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat}
    {status : Parquet.Page.Checksum.Status} {cause : ScalarPage.Error}
    (verified : Dictionary.Snappy.verifyData leafLimits bound page ordinal = .ok status)
    (plain : page.params.encoding = 0)
    (failed : ScalarPage.decode .int64 page.params leafLimits.page (Leaf.Internal.body bound page.frame) =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.plain cause)) := by
  simp [decodePage, verified, Bind.bind, Except.bind, Fallback.decodePage_plain_error plain failed]

/-- The trace uses the same checked fallback reads in footer order. -/
theorem readBound_reference (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Events.referenceGroupsWith (readGroup limits leafLimits bound)
      (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Events.rows bound), reference.2⟩⟩ :=
  Events.readBoundWith_reference bound (readGroup limits leafLimits bound)

/-- A group error retains precisely the earlier complete footer groups. -/
theorem readBound_first_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The native Arrow stream reads back to the retained descriptor and the
ordered nullable counts of every complete footer group. -/
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

/-- The first failing footer group forwards the same cause before the IPC
writer attempts admission. -/
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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy
