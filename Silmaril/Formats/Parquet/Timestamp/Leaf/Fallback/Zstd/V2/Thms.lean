module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- The original page header fixes both the encoding and V2 storage flag. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ (header.encoding = 8 ∨ header.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.planData_wire read

/-- Store the original ordered frames, offsets, both budgets, and one-way phase. -/
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
      Leaf.Dictionary.Zstd.V2.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.checkGroup_wire accepted

/-- Every original page after a PLAIN page is also PLAIN. -/
theorem checkGroup_no_reentry {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk} {i j : Nat} {a b : DataPage}
    (accepted : checkGroup limits leafLimits bound index = .ok checked)
    (earlier : checked.data[i]? = some a) (later : checked.data[j]? = some b)
    (before : i < j) (plain : a.params.encoding = 0) : b.params.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.checkGroup_no_reentry accepted earlier later before plain

/-- A first failed header plan keeps the original ordinal and absolute offset. -/
theorem checkGroup_first_header_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .ok framed)
    (cap : (framed.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => (planData bound item).mapError
      (Leaf.Zstd.V2.GroupError.selection ∘ Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    checkGroup limits leafLimits bound index =
      .error (.selection (.dictionaryPage ordinal frame.header.start cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.checkGroup_first_header_error
    framedOk cap split earlier failed

/-- Phase refusal occurs before any dictionary or reference payload is decoded. -/
theorem checkGroup_phase_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {framed : Leaf.Dictionary.FramedChunk} {pages : List DataPage} {cause : Leaf.Error}
    (framedOk : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .ok framed)
    (cap : (framed.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes)
    (planned : Leaf.Dictionary.Zstd.V2.planPagesWith Leaf.Fallback.admits bound framed.data = .ok pages)
    (failed : Leaf.Fallback.checkSequence pages = .error cause) :
    checkGroup limits leafLimits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.checkGroup_phase_error framedOk cap planned failed

/-- The admitted leading dictionary's original CRC precedes Zstandard expansion. -/
theorem dictionary_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {header : Parquet.Page.Dictionary} {cause : Parquet.Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary header) (plain : header.encoding = 0)
    (entries : header.numValues ≤ limits.dictionary.maxEntries)
    (failed : Parquet.Page.Checksum.verify
      (Leaf.Dictionary.Snappy.dictionaryBounds limits.dictionary leafLimits frame).compressedLimit
      bound.snapshot.bytes frame = .error cause) :
    Leaf.Dictionary.Zstd.V2.readEntries limits leafLimits bound frame =
      .error (.checksum 0 frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.dictionary_checksum_error kind plain entries failed

/-- Every admitted page supplies the exact wire evidence of its selected strict decoder. -/
theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.decodePage_wire planned read

/-- Either admitted data phase reports a stored CRC failure before preparation. -/
theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (planned : planData bound page.frame = .ok page)
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.decodePage_checksum_error planned failed

/-- The first failed data page after planning preserves its original cause. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.readGroup_first_page_error admitted split earlier failed

/-- The original dictionary and ordered phases yield the exact signed nullable slots. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      Leaf.Dictionary.Zstd.V2.DictionaryWire limits leafLimits bound checked.dictionary checked.entries ∧
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.readGroup_wire read

/-- A failed group retains exactly the preceding complete footer groups. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Leaf.Zstd.V2.readBoundWith_first_error (read := readGroup limits leafLimits bound) split earlier failed

/-- The typed first source error precedes native writer checks. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Leaf.Zstd.V2.convertWith_first_error (read := readGroup limits inputLimits.leaf) opened split earlier failed

/-- Native IPC recovers the original descriptor and footer groups through EOS. -/
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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2
