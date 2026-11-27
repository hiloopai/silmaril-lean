module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Defs
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2

open Arrow.BinaryView
open Plain.ByteArray

/-- The leading dictionary CRC is checked before its Zstandard expansion. -/
theorem readDictionary_checksum_error {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {data : Page.Dictionary} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary data) (encoding : data.encoding = 0)
    (advertised : 0 ∈ metadata.encodings) (cap : data.numValues ≤ limits.maxDictionaryEntries)
    (failed : Page.Checksum.verify (limits.toPhysical.dictionaryBounds frame).compressedLimit
      source frame = .error cause) :
    readDictionary limits metadata source frame = .error (.checksum cause) := by
  simp [readDictionary, kind, encoding, advertised, Nat.not_lt_of_ge cap, failed, Except.mapError, Bind.bind, Except.bind]

/-- The full stored dictionary supplies one exact Zstandard frame and the original entry octets. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {entries : Array Bytes}
    (read : readDictionary limits metadata source frame = .ok entries) :
    DictionaryWire limits source frame entries :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.readDictionary_wire read

/-- The stored data CRC is checked before levels or indices are interpreted. -/
theorem decodePage_checksum_error {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {data : Page.DataV2} {entries : Array Bytes} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 data) (encoding : data.encoding = 8)
    (advertised : 8 ∈ metadata.encodings)
    (failed : Page.Checksum.verify limits.file.column.maxPageBytes source frame = .error cause) :
    decodePage limits metadata source (some entries) frame = .error (.checksum cause) := by
  simp [decodePage, kind, encoding, advertised, failed, Except.mapError, Bind.bind, Except.bind]

/-- The original frame records tag 8 and its checked indices resolve to the exact opaque slots. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.decodePage_wire read

/-- A V2 PLAIN fallback is refused at its original page coordinate. -/
theorem decodePage_plain {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {header : Page.DataV2}
    (kind : frame.value.kind = .dataV2 header) (encoding : header.encoding = 0) :
    decodePage limits metadata source dictionary frame = .error (.encoding 0) := by
  simp [decodePage, kind, encoding, Bind.bind, Except.bind]
  rfl

/-- A flagged suffix retains one admitted frame; a literal suffix retains its exact bytes. -/
theorem suffix_profile {limits : FlatColumn.Zstd.CompressionLimits} {bounds : Payload.Bounds}
    {flag : Bool} {stored decoded : List UInt8}
    (wire : FlatColumn.Zstd.PayloadWire limits bounds (ScalarPage.v2Codec Payload.Codec.zstd.id (some flag))
      stored decoded) :
    if flag then ∃ header, Compression.Zstd.CheckedFrame.Huffman.FrameWire
      (FlatColumn.Zstd.frameLimits limits bounds) stored decoded header ∧ header.windowSize ≤ limits.window
    else decoded = stored := by
  cases flag <;> simpa [ScalarPage.v2Codec, Payload.Codec.id] using wire.2.2.2.2

/-- The strict callback keeps its exact frame and ordered slot relation. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.readFrames_wire read

/-- A failed index page after a successful prefix keeps its original group, column, ordinal and offset. -/
theorem readFrames_first_page_error {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows ordinal : Nat} {name : String} {dictionary frame : Page.Frame}
    {data : List Page.Frame} {header : Page.Dictionary} {entries : Array Bytes}
    {before after : List (Page.Frame × Nat)} {prefixSlots : List (List (Option Bytes))}
    {cause : FlatColumn.PageError DecodeError}
    (kind : dictionary.value.kind = .dictionary header)
    (expanded : Utf8.Dictionary.Snappy.checkExpandedChunk (ε := DecodeError)
      limits.toPhysical metadata group column name (dictionary :: data) = .ok ())
    (dictionaryAt : metadata.dictionaryPageOffset = some (dictionary.header.start : Int))
    (dataAt : data.head?.map (fun page : Page.Frame => (page.header.start : Int)) = some metadata.dataPageOffset)
    (count : (data.map ByteArrayFallback.declaredSlots).sum = rows)
    (opened : readDictionary limits metadata source dictionary = .ok entries)
    (split : data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, page) => (decodePage limits metadata source (some entries) item).mapError
      (FlatColumn.Error.page group column name page item.header.start)) = .ok prefixSlots)
    (failed : decodePage limits metadata source (some entries) frame = .error cause) :
    readFrames limits metadata source group column name rows (dictionary :: data) =
      .error (.page group column name ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.readFrames_first_page_error
    kind expanded dictionaryAt dataAt count opened split earlier failed

/-- The selected chunk preserves exact byte totals, dictionary, and original data-page order. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.readGroup_wire read

/-- The same checked unannotated binding gives exact opaque group slots through BinaryView EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toPhysical input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.convert_readback written

/-- The first indexed source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : GroupError}
    (opened : Snappy.openFile parquet.toPhysical input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2
