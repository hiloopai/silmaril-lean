module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy

open Arrow.MixedFlat

/-- The CRC-checked original frame determines the exact PLAIN nullable octets. -/
theorem decodePlain_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option String)}
    (read : decodePlain limits metadata source frame = .ok slots) : PlainPageWire limits source frame slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.decodePlain_wire read

/-- The original page tag determines which wire relation accounts for its slots. -/
theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array String)} {frame : Page.Frame} {slots : List (Option String)}
    (read : decodeData limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.decodeData_wire read

/-- The original chunk retains exact byte totals, the strict dictionary and both ordered phases. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.readGroup_wire read

/-- The native Utf8View stream preserves the selected source groups through exact EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Dictionary.openFile parquet.toLimits input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.convert_readback written

/-- The first failed source group keeps its complete indexed cause before IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {checked : Checked name} {before after : List Nat} {index : Nat} {earlier : List (List (Option String))}
    {cause : GroupError} (opened : Dictionary.openFile parquet.toLimits input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy
