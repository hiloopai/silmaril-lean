module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy

open Arrow.MixedFlat

variable {parquet : File.Limits} {input : Bytes} {name : String} {layout : FlatColumn.Layout}
variable {checked : Utf8.Checked name layout}

/-- Each callback keeps its original CRC-checked payload, bounded expansion and ordered text octets. -/
theorem page_wire {limits : File.Limits} {layout : FlatColumn.Layout} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {frame : Page.Frame} {text : List (Option String)}
    (wire : FlatColumn.CheckedCallbackWire .snappy limits.column (decodePage limits layout)
      leaf metadata source frame text) : PageWire limits layout metadata source frame text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.page_wire wire

/-- The matched Snappy column and its original frames determine the ordered nullable strings. -/
theorem readGroup_wire {index : Nat} {text : List (Option String)}
    (read : readGroup parquet checked index = .ok text) :
    ∃ group, GroupWire parquet checked index group text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.readGroup_wire read

/-- Exact native batches preserve every original checked source group through EOS. -/
theorem convert_readback {ipc : Arrow.MixedFlat.Limits} {wire : KBytes}
    (written : convert parquet ipc input name layout = .ok wire) :
    ∃ (checked : Utf8.Checked name layout) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Utf8.openFile parquet input name layout = .ok checked ∧
      List.Forall₂ (fun index text => ∃ group, GroupWire parquet checked index group text)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name layout ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, layout == .optional, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.convert_readback written

/-- The earlier successful groups determine the position of the first
source error, whose complete indexed cause precedes all IPC limits. -/
theorem convert_first_error {ipc : Arrow.MixedFlat.Limits} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option String))} {cause : FlatColumn.Error PageError}
    (opened : Utf8.openFile parquet input name layout = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc input name layout = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy
