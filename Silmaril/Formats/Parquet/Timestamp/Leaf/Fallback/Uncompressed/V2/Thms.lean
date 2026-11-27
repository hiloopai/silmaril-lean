module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- The original V2 header fixes the tag, both extents and all flat page parameters. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV2 info ∧ (info.encoding = 8 ∨ info.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.uncompressed.id, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.planData_wire planned

/-- One scan retains the original bounded chunk, dictionary offsets, ordered phases and declared rows. -/
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
      Leaf.Dictionary.Uncompressed.V2.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.checkGroup_wire admitted

/-- Every admitted page after the first PLAIN page is PLAIN. -/
theorem checkGroup_no_reentry {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk} {i j : Nat} {a b : DataPage}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (earlier : checked.data[i]? = some a) (later : checked.data[j]? = some b)
    (before : i < j) (plain : a.params.encoding = 0) : b.params.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.checkGroup_no_reentry admitted earlier later before plain

/-- The first failed header retains its original page ordinal and absolute offset. -/
theorem readGroup_first_header_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .ok framed)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    readGroup limits leafLimits bound index = .error (.dictionaryPage ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.readGroup_first_header_error framedOk split earlier failed

/-- A failed phase check is returned before decoding the original bodies. -/
theorem readGroup_phase_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Leaf.Dictionary.FramedChunk} {pages : List DataPage} {cause : Leaf.Error}
    (framedOk : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .ok framed)
    (planned : (framed.data.zipIdx 1).mapM (fun (frame, ordinal) =>
      (planData bound frame).mapError (Leaf.Dictionary.atFrame ordinal frame)) = .ok pages)
    (failed : Leaf.Fallback.checkSequence pages = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.readGroup_phase_error framedOk planned failed

/-- The reference branch supplies the literal V2 dictionary law with its original checked frame. -/
theorem references_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (tag : page.params.encoding = 8)
    (read : Leaf.Fallback.Snappy.DataWire limits leafLimits bound entries page slots) :
    Leaf.Dictionary.Uncompressed.V2.planData bound page.frame = .ok page ∧
      Leaf.Dictionary.Snappy.DataWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.references_wire planned tag read

/-- The PLAIN branch supplies the literal V2 PLAIN law with its original checked frame. -/
theorem plain_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (tag : page.params.encoding = 0)
    (read : Leaf.Fallback.Snappy.DataWire limits leafLimits bound entries page slots) :
    Leaf.Uncompressed.V2.PageWire leafLimits.page bound page.frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.plain_wire planned tag read

/-- Both branches use the original CRC-covered body and one literal suffix with both extents. -/
theorem page_extents {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Fallback.Snappy.DataWire limits leafLimits bound entries.toArray page slots) :
    let frame := page.frame
    let stored := Leaf.Internal.body bound frame
    ∃ (info : Parquet.Page.DataV2) (definitions : Bytes) (suffix : List UInt8),
      frame.value.kind = .dataV2 info ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧
      (frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
        Compression.crc32Spec stored.toList = crc) ∧
      info.repetitionBytes = 0 ∧ definitions.length = info.definitionBytes ∧
      stored.toList = definitions.toList ++ suffix ∧
      suffix.length = frame.value.compressedSize - info.definitionBytes ∧
      suffix.length = frame.value.uncompressedSize - info.definitionBytes :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.page_extents planned read

/-- The output preserves frame order, signed nullable ticks and the checked row count. -/
theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Fallback.Snappy.DataWire limits leafLimits
        bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.readGroup_wire read

/-- An original stored data CRC error preempts decoding either branch. -/
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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2
