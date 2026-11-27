module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback

open Arrow.MixedFlat

/-- Both phases are nonempty and their exact original order is dictionary then PLAIN. -/
theorem checkPhases_wire {group column firstOrdinal : Nat} {name : String} {data : List Page.Frame}
    (passed : checkPhases group column name firstOrdinal data = .ok ⟨⟩) : Phases data :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.checkPhases_wire passed

/-- Each original frame determines the dictionary or PLAIN wire relation for the exact text slots. -/
theorem decodeData_wire {limits : Limits} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {dictionary : Option (Array String)}
    {frame : Page.Frame} {slots : List (Option String)}
    (read : decodeData limits leaf metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits metadata source entries frame slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.decodeData_wire read

/-- The selected original chunk retains the strictly checked dictionary and both ordered data phases. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Checked name} {index : Nat}
    {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.readGroup_wire read

/-- The native Utf8View stream preserves the checked source groups through exact EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Utf8.Dictionary.openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.convert_readback written

/-- The first failed source group keeps its complete indexed cause before IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {checked : Checked name} {before after : List Nat} {index : Nat} {earlier : List (List (Option String))}
    {cause : GroupError} (opened : Dictionary.openFile parquet input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback
