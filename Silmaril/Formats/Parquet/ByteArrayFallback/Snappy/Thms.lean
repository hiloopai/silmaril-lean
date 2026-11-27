module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy

open Arrow.BinaryView
open Footer.ColumnOrder (FlatLeaf field?)
open Plain.ByteArray

/-- The original leaf has neither a logical nor a converted annotation. -/
theorem checkUnannotated_wire {leaf : FlatLeaf} (checked : checkUnannotated leaf = .ok ()) :
    field? leaf.selection.leaf.item.fields 10 = .ok none ∧
    field? leaf.selection.leaf.item.fields 6 = .ok none :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.checkUnannotated_wire checked

/-- The original checked snapshot and column ordinal determine the unannotated physical leaf. -/
theorem openFile_wire {limits : Limits} {input : Bytes} {name : String}
    {checked : Checked name} (opened : openFile limits input name = .ok checked) :
    File.openFile limits.file input name .optional = .ok checked.physical ∧
    ∃ selected, Footer.ColumnOrder.FlatWire limits.file.snapshot.footer checked.physical.snapshot
        checked.physical.binding.columnOrdinal selected ∧ selected.leaf = checked.physical.binding.leaf ∧
      field? selected.selection.leaf.item.fields 10 = .ok none ∧
      field? selected.selection.leaf.item.fields 6 = .ok none :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.openFile_wire opened

/-- The original dictionary expands exactly to ordered opaque entries. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : Array Bytes}
    (read : readDictionary limits metadata source frame = .ok entries) :
    Utf8.Dictionary.Snappy.DictionaryBytesWire limits source frame entries.toList :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.readDictionary_wire read

/-- The original tag selects the exact nullable byte relation for each page. -/
theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodeData limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.decodeData_wire read

/-- The selected chunk preserves exact byte totals and both original encoding phases. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.readGroup_wire read

/-- Exact BinaryView batches carry the original nullable group slots through EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Snappy.convert_readback written

/-- The first indexed source error takes precedence over any IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : GroupError}
    (opened : openFile parquet input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy
