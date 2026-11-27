module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback

open Arrow.BinaryView
open Plain.ByteArray

/-- The original V1 frame selects the dictionary index or PLAIN wire witness. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.decodePage_wire read

/-- Either admitted encoding consumes the complete original V1 GZIP member. -/
theorem data_member {limits : Limits} {source : Bytes} {entries : Array Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source entries frame slots) :
    ∃ expanded,
      Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, []) ∧
      expanded.length = frame.value.uncompressedSize :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.data_member wire

/-- Every original frame in the selected chunk accounts for exactly one complete member. -/
theorem frames_members {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {rows : Nat} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (wire : FramesWire limits metadata source rows frames slots) (frame : Page.Frame) (present : frame ∈ frames) :
    ∃ expanded,
      Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, []) ∧
      expanded.length = frame.value.uncompressedSize :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.frames_members wire frame present

/-- Exact byte totals and complete ordered pages with a nonempty dictionary prefix and PLAIN suffix. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.readGroup_wire read

/-- The same checked unannotated binding gives exact opaque group slots through BinaryView EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toSnappyLimits input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.convert_readback written

/-- The first indexed fallback source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (opened : Snappy.openFile parquet.toSnappyLimits input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) :=
  Snappy.convertWith_first_error (readGroupAt := readGroup parquet) opened indices prefixRead failed

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback
