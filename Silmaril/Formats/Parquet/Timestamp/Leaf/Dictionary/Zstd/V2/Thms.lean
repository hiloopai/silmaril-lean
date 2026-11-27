module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original data frame fixes the V2 flag, extents and RLE_DICTIONARY tag. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, 8,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.planData_wire read

/-- The whole group retains the original offsets, frame chain, byte caps and row total. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .zstdDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.checkGroup_wire accepted

/-- Every signed entry comes from the original CRC-checked PLAIN dictionary frame. -/
theorem readEntries_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {entries : List Int64} (read : readEntries limits leafLimits bound frame = .ok entries) :
    DictionaryWire limits leafLimits bound frame entries :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.readEntries_wire read

/-- Raw definitions and the exact stored reference suffix preserve the ordered signed lookups. -/
theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.decodePage_wire planned read

/-- An original stored CRC error precedes the flag-selected decoder. -/
theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.decodePage_checksum_error failed

/-- After group planning, the first data failure retains its original indexed cause. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.readGroup_first_page_error admitted split earlier failed

/-- Group slots retain the original chunk-local dictionary and original ordered pages. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      DictionaryWire limits leafLimits bound checked.dictionary checked.entries ∧
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.readGroup_wire read

/-- The event trace keeps exactly the completed earlier footer groups. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Leaf.Zstd.V2.readBoundWith_first_error (read := readGroup limits leafLimits bound) split earlier failed

/-- The earliest source fault precedes IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Leaf.Zstd.V2.convertWith_first_error (read := readGroup limits inputLimits.leaf) opened split earlier failed

/-- Native IPC recovers the original descriptor and every grouped signed slot through EOS. -/
theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits inputLimits.leaf bound) = .ok groups ∧
      readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) :=
  Leaf.Zstd.V2.convertWith_readback (read := readGroup limits inputLimits.leaf) written

/-- The chosen data tag predicate retains the exact original V2 header. -/
theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ admits header.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.planDataWith_wire read

/-- The admitted phase policy and budgets apply to the original selected frame chain. -/
theorem checkGroupWith_wire {admits : Int → Bool} {validate : List DataPage → Except Leaf.Error Unit}
    {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroupWith admits validate limits leafLimits bound index = .ok checked) :
    selectChunkWith .zstdDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planDataWith admits bound page.frame = .ok page) ∧
      validate checked.data = .ok () ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.checkGroupWith_wire accepted

/-- A tag-8 page retains the original reference wire evidence under an admitted V2 plan. -/
theorem decodePage_wireWith {admits : Int → Bool} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planDataWith admits bound page.frame = .ok page) (reference : page.params.encoding = 8)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.decodePage_wireWith planned reference read

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2
