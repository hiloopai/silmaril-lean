module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Defs
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2

open Arrow.BinaryView
open Plain.ByteArray
open Silmaril.Relational

/-- The PLAIN branch uses exactly the same page and Zstandard caps. -/
theorem page_limits_agree (limits : Limits) : (plainLimits limits).page = limits.page := rfl

/-- The original V2 tag selects the strict dictionary or PLAIN wire witness. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.decodePage_wire read

/-- Both strict phases retain the original complete stored body and CRC. -/
theorem data_checksum {limits : Limits} {source : Bytes} {entries : Array Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source entries frame slots) :
    Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.data_checksum wire

/-- Original data frames have nonempty dictionary and PLAIN phases in that order. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.readFrames_wire read

/-- A dictionary tag in the PLAIN suffix is refused at its original frame coordinate. -/
theorem readFrames_revival {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows ordinal : Nat} {name : String} {dictionary frame : Page.Frame}
    {data : List Page.Frame} {header : Page.Dictionary} {before after : List (Page.Frame × Nat)}
    (leading : dictionary.value.kind = .dictionary header)
    (expanded : Utf8.Dictionary.Snappy.checkExpandedChunk (ε := DecodeError)
      limits.toPhysical metadata group column name (dictionary :: data) = .ok ())
    (prefixPresent : (data.takeWhile Utf8.Fallback.isDictionaryData).isEmpty = false)
    (positions : (data.dropWhile Utf8.Fallback.isDictionaryData).zipIdx
      (1 + (data.takeWhile Utf8.Fallback.isDictionaryData).length) = before ++ (frame, ordinal) :: after)
    (earlier : before.forM (fun (item, page) => Utf8.Fallback.checkPlainTagWith.{0}
      DecodeError.dictionaryAfterPlain group column name page item) = .ok ⟨⟩)
    (revived : Utf8.Fallback.dataEncoding frame = some 8) :
    readFrames limits metadata source group column name rows (dictionary :: data) =
      .error (.page group column name ordinal frame.header.start (.decode .dictionaryAfterPlain)) :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.readFrames_revival leading expanded prefixPresent positions earlier revived

/-- The selected chunk retains its original bytes, dictionary, page order and slots. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.readGroup_wire read

/-- The checked source emits each successful group, in footer order, through EOS. -/
theorem readAll_success {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {groups : List (List (Option Bytes))}
    (decoded : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots)
      (List.range checked.physical.snapshot.groupCount) groups) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.readAll_success decoded

/-- The checked source retains exactly the completed group prefix and original terminal error. -/
theorem readAll_first_error {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.readAll_first_error split earlier failed

/-- Native BinaryView preserves the checked source descriptor and exact group slots through EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toPhysical input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      readAll parquet checked = .ok ⟨schema name,
        ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.convert_readback written

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

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2
