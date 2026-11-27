module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The planner retains every original V2 parameter under its selected tag policy. -/
theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.uncompressed.id frame.value =
        .ok page.params ∧
      ∃ header, frame.value.kind = .dataV2 header ∧ admits header.encoding = true ∧
        page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
          header.numValues, Payload.Codec.uncompressed.id, header.encoding, .v2 header.numNulls header.numRows
            header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.planDataWith_wire planned

/-- A stricter policy that accepts the original tag yields the same planned frame. -/
theorem planDataWith_restrict {admits accepts : Int → Bool} {bound : Bound}
    {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page)
    (admitted : accepts page.params.encoding = true) :
    planDataWith accepts bound frame = .ok page :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.planDataWith_restrict planned admitted

/-- The selected original data frame is V2 with the RLE_DICTIONARY tag and unchanged parameters. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.uncompressed.id, 8, .v2 header.numNulls header.numRows
          header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.planData_wire planned

/-- The original CRC-covered dictionary contains the exact bounded literal PLAIN words. -/
theorem readEntries_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntries limits leafLimits bound frame = .ok entries) :
    let stored := Leaf.Internal.body bound frame
    let bounds := Leaf.Dictionary.Snappy.dictionaryBounds limits leafLimits frame
    ∃ header, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
      (frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
        Compression.crc32Spec stored.toList = crc) ∧
      stored.length = frame.value.uncompressedSize ∧ stored.length ≤ bounds.outputLimit ∧
      Plain.decodeInt64 header.numValues stored = .ok entries ∧
      entries.length = header.numValues :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.readEntries_wire read

/-- The original chunk supplies one leading dictionary, its continuation frames, and the declared row count. -/
theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.uncompressed.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.checkGroup_wire admitted

/-- The original CRC-covered V2 body contains exact raw definitions and a literal index suffix with both declared extents. -/
theorem data_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits leafLimits bound entries.toArray page slots) :
    let frame := page.frame
    let stored := Leaf.Internal.body bound frame
    ∃ header layout definitions suffix, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ leafLimits.page.compressedBytes ∧
      (frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
        Compression.crc32Spec stored.toList = crc) ∧
      frame.value.uncompressedSize ≤ leafLimits.page.uncompressedBytes ∧
      header.numNulls ≤ header.numValues ∧ header.numRows = header.numValues ∧
      header.repetitionBytes = 0 ∧
      header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
      definitions.length = header.definitionBytes ∧ definitions.length ≤ leafLimits.page.levels.bytes ∧
      stored.toList = definitions.toList ++ suffix ∧
      suffix.length = frame.value.compressedSize - header.definitionBytes ∧
      suffix.length = frame.value.uncompressedSize - header.definitionBytes ∧
      suffix = prepared.scalars.toList ∧ suffix = width :: runs ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.data_decodes planned read

/-- The first failed header keeps its original page ordinal and absolute header offset. -/
theorem readGroup_first_header_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .ok framed)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    readGroup limits leafLimits bound index = .error (.dictionaryPage ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.readGroup_first_header_error framedOk split earlier failed

/-- The group reconstructs signed nullable ticks in original frame order at the original row count. -/
theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Dictionary.Snappy.DataWire limits leafLimits
        bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.readGroup_wire read

/-- A failed stored dictionary CRC prevents the literal word decoder from running. -/
theorem dictionary_checksum_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {header : Parquet.Page.Dictionary}
    {cause : Parquet.Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary header) (encoding : header.encoding = 0)
    (count : header.numValues ≤ limits.maxEntries)
    (size : (Snappy.dictionaryBounds limits leafLimits frame).expectedSize ≤
      (Snappy.dictionaryBounds limits leafLimits frame).outputLimit)
    (failed : Parquet.Page.Checksum.verify (Snappy.dictionaryBounds limits leafLimits frame).compressedLimit
      bound.snapshot.bytes frame = .error cause) :
    readEntries limits leafLimits bound frame = .error (.checksumFailure cause) := by
  simp [readEntries, Snappy.readEntriesWithCodec, Snappy.DictionaryTag.id, kind, encoding,
    Nat.not_lt.mpr count, Nat.not_lt.mpr size, failed, Except.mapError, Bind.bind, Except.bind]

/-- An original stored data CRC error preempts decoding of the stored reference suffix. -/
theorem data_checksum_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    Snappy.decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.checksumFailure cause)) :=
  Snappy.decodePage_checksum_error failed

/-- A typed page error retains its original context after successful planning. -/
theorem readGroup_first_page_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      Snappy.decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : Snappy.decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Snappy.readGroupUsing_first_page_error admitted split earlier failed

/-- The event trace retains precisely the complete groups preceding the failure. -/
theorem readBound_first_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- Complete native IPC reads back through EOS with the same descriptor and
ordered nullable signed ticks from the original footer groups. -/
theorem convert_readback {limits : Dictionary.Limits} {inputLimits : Events.ToIpc.Limits}
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
theorem convert_first_error {limits : Dictionary.Limits} {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2
