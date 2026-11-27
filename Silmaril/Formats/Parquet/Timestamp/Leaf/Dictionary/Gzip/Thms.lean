module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original V1 header supplies the chosen encoding and checked GZIP parameters. -/
theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ admits info.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, info.encoding, .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.planDataWith_wire planned

/-- The original V1 data header fixes the codec, level tags and reference count. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ info.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, 8, .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.planData_wire planned

/-- The original PLAIN dictionary expands to exact signed INT64 words from one GZIP member. -/
theorem readEntries_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {entries : List Int64} (read : readEntries limits leafLimits bound frame = .ok entries) :
    let bounds := Leaf.Dictionary.Snappy.dictionaryBounds limits.dictionary (limits.withFuel leafLimits) frame
    ∃ header expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.dictionary.maxEntries ∧
      StoredMember bound frame bounds.compressedLimit bounds.outputLimit expanded ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = header.numValues :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.readEntries_wire read

/-- The checked selected chunk retains the original frames, offsets and declared row count. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.checkGroup_wire admitted

/-- The V1 prepared body comes from the exact original stored GZIP member. -/
theorem prepared_member {admits : Int → Bool} {leafLimits : Leaf.Limits} {bound : Bound}
    {page : DataPage} {encoding : Int} {status : Parquet.Page.Checksum.Status}
    {prepared : ScalarPage.Prepared}
    (planned : planDataWith admits bound page.frame = .ok page)
    (verified : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .ok status)
    (preparedOk : ScalarPage.prepareFor encoding page.params leafLimits.page
      (Leaf.Internal.body bound page.frame) = .ok prepared) :
    ∃ expanded layout sections,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.prepared_member planned verified preparedOk

/-- A decoded reference page retains its exact GZIP member, levels and index stream. -/
theorem data_decodesWith {admits : Int → Bool} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planDataWith admits bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars ∧ prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.data_decodesWith planned read

/-- The original V1 member expands to the checked levels and ordered signed dictionary lookups. -/
theorem data_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars ∧ prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.data_decodes planned read

/-- Original page order recovers exact signed nullable slots and the footer row count. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
        bound checked.entries.toArray) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.readGroup_wire read

/-- An original stored data CRC error preempts GZIP expansion. -/
theorem data_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    Snappy.decodePage limits.dictionary (limits.withFuel leafLimits) bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.checksumFailure cause)) :=
  Snappy.decodePage_checksum_error failed

/-- A typed page error retains its original context after successful planning. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      Snappy.decodePage limits.dictionary (limits.withFuel leafLimits) bound checked.entries.toArray item i) = .ok outputs)
    (failed : Snappy.decodePage limits.dictionary (limits.withFuel leafLimits) bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Snappy.readGroupUsing_first_page_error admitted split earlier failed

/-- The event trace retains precisely the complete groups preceding the failure. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- Complete native IPC reads back through EOS with the same descriptor and
ordered nullable signed ticks from the original footer groups. -/
theorem convert_readback {limits : Limits} {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroups_readback written

/-- The first failed original group is reported before writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip
