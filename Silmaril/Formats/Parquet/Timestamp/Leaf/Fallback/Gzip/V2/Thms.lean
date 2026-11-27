module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- The original V2 header fixes the encoding, sizes, counts and storage flag. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV2 info ∧ (info.encoding = 8 ∨ info.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.planData_wire planned

/-- The original selected frame chain has a nonempty dictionary prefix and PLAIN suffix. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .gzipDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.checkGroup_wire admitted

/-- Every page after a PLAIN page is also PLAIN. -/
theorem checkGroup_no_reentry {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk} {i j : Nat} {a b : DataPage}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (earlier : checked.data[i]? = some a) (later : checked.data[j]? = some b)
    (before : i < j) (plain : a.params.encoding = 0) : b.params.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.checkGroup_no_reentry admitted earlier later before plain

/-- The original PLAIN suffix yields the exact nullable mask and signed words. -/
theorem plain_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (plain : page.params.encoding = 0)
    (read : Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits) bound entries page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ words,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      Dictionary.Gzip.V2.BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.plain_decodes planned plain read

/-- Read the CRC-checked pages in original order with exact signed slots and row count. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
        bound checked.entries.toArray) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.readGroup_wire read

/-- A reference page preserves the stored suffix, raw levels and ordered lookups into its chunk's dictionary. -/
theorem references_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (tag : page.params.encoding = 8)
    (read : Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      Dictionary.Gzip.V2.BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  Dictionary.Gzip.V2.data_decodesWith (admits := Fallback.admits) planned (Snappy.dictionary_decodes tag read)

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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2
