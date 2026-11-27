module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

/-- A bad CRC takes precedence over level splitting and Zstandard decoding. -/
theorem decodePage_checksum_error {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {data : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 data) (encoding : data.encoding = 0)
    (advertised : 0 ∈ metadata.encodings)
    (failed : Page.Checksum.verify limits.file.column.maxPageBytes source frame = .error cause) :
    decodePage limits metadata source frame = .error (.checksum cause) := by
  simp [decodePage, kind, encoding, advertised, failed, Except.mapError, Bind.bind, Except.bind]

/-- The entire original stored body supplies the raw levels and the exact flagged value suffix. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source frame = .ok slots) : PageWire limits source frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.decodePage_wire read

/-- A flagged suffix retains one admitted frame; a literal suffix retains its exact bytes. -/
theorem suffix_profile {limits : FlatColumn.Zstd.CompressionLimits} {bounds : Payload.Bounds}
    {flag : Bool} {stored decoded : List UInt8}
    (wire : FlatColumn.Zstd.PayloadWire limits bounds (ScalarPage.v2Codec Payload.Codec.zstd.id (some flag))
      stored decoded) :
    if flag then ∃ header, Compression.Zstd.CheckedFrame.Huffman.FrameWire
      (FlatColumn.Zstd.frameLimits limits bounds) stored decoded header ∧ header.windowSize ≤ limits.window
    else decoded = stored := by
  cases flag <;> simpa [ScalarPage.v2Codec, Payload.Codec.id] using wire.2.2.2.2

/-- Every original frame supplies ordered PLAIN V2 slots, with no dictionary offset. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.readFrames_wire read

/-- The original checked frames retain their byte limits and ordered PLAIN slots. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.readGroup_wire read

/-- The same checked unannotated binding gives exact opaque group slots through BinaryView EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.physical input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.convert_readback written

/-- The first indexed source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : GroupError}
    (opened : Snappy.openFile parquet.physical input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2
