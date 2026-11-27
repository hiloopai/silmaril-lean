module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary

open Arrow.BinaryView

/-- The original frame records tag 8 and its checked indices resolve to the exact opaque slots. -/
theorem decodePage_wire {limits : Snappy.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.decodePage_wire read

/-- A recorded PLAIN tag gives an encoding refusal before body decoding. -/
theorem decodePage_plain {limits : Snappy.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame}
    (encoding : Plain.ByteArray.Utf8.Fallback.dataEncoding frame = some 0) :
    decodePage limits metadata source dictionary frame = .error (.encoding 0) := by
  simp [decodePage, encoding]

/-- The selected chunk preserves exact byte totals, dictionary, and original data-page order. -/
theorem readGroup_wire {parquet : Snappy.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.readGroup_wire read

/-- The same checked unannotated binding gives exact opaque group slots through BinaryView EOS. -/
theorem convert_readback {parquet : Snappy.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.convert_readback written

/-- The first indexed dictionary-only source error precedes IPC admission. -/
theorem convert_first_error {parquet : Snappy.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (opened : Snappy.openFile parquet input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) :=
  Snappy.convertWith_first_error (readGroupAt := readGroup parquet) opened indices prefixRead failed

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary
