module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Relational

/-- For an admitted header, the original stored CRC is checked before level or payload decoding. -/
theorem decodePage_checksum_error {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {header : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 header) (encoding : header.encoding = 0)
    (advertised : 0 ∈ metadata.encodings) (expanded : frame.value.uncompressedSize ≤ limits.maxExpandedPageBytes)
    (failed : Page.Checksum.verify limits.file.column.maxPageBytes source frame = .error cause) :
    decodePage limits metadata source frame = .error (.decode (.plain (.decode (.checksum cause)))) := by
  simp [decodePage, kind, encoding, Utf8.Fallback.Snappy.decodePlainBytes,
    Utf8.Fallback.Snappy.decodePlainBytesWith, FlatColumn.pageParameters, advertised,
    Nat.not_lt_of_ge expanded, failed, Except.mapError, Bind.bind, Except.bind]

/-- The callback uses the original V2 header, body and exact opaque slots. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source frame = .ok slots) : PageWire limits source frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.decodePage_wire read

/-- The original stored checksum covers the raw definitions and exact flag-selected suffix. -/
theorem data_suffix {limits : Limits} {source : Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source frame slots) :
    Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame ∧ SuffixWire limits source frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.data_suffix wire

/-- The original chunk has no dictionary and each original frame supplies ordered PLAIN V2 slots. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.readFrames_wire read

/-- The original checked selected chunk retains both byte totals and ordered slots. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.readGroup_wire read

/-- The checked Events source preserves exact completed footer batches through EOS. -/
theorem readAll_success {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {groups : List (List (Option Bytes))}
    (decoded : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots)
      (List.range checked.physical.snapshot.groupCount) groups) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.readAll_success decoded

/-- Events retains exactly the completed group prefix and original first cause. -/
theorem readAll_first_error {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.readAll_first_error split earlier failed

/-- Native BinaryView preserves the checked Events groups and opaque bytes through EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet input name = .ok checked ∧
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
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.convert_readback written

/-- The first indexed source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (opened : Snappy.openFile parquet input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) :=
  Snappy.convertWith_first_error (readGroupAt := readGroup parquet) opened indices prefixRead failed

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2
