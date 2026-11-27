module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy

open Arrow.MixedFlat

/-- The verified CRC status and stored size concern the original bounded body slice. -/
theorem stored_wire {cap : Nat} {source : Bytes} {frame : Page.Frame} {status : Page.Checksum.Status}
    (verified : Page.Checksum.verify cap source frame = .ok status) : StoredWire cap source frame :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.stored_wire verified

/-- The original stored dictionary expands exactly to the ordered strict UTF-8 entries. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : Array String}
    (read : readDictionary limits metadata source frame = .ok entries) : DictionaryWire limits source frame entries :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.readDictionary_wire read

/-- The original V1 or V2 header determines the exact dictionary indices and nullable octets. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array String)} {frame : Page.Frame} {text : List (Option String)}
    (read : decodePage limits metadata source dictionary frame = .ok text) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.decodePage_wire read

/-- Header and stored-body byte counts sum to the exact framed extent. -/
theorem storedBytes_chain {chunk : Footer.Span} {start stop : Nat} {frames : List Page.Frame}
    (chain : Page.Chain chunk start stop frames) : start ≤ stop ∧ storedBytes frames = stop - start :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.storedBytes_chain chain

/-- The selected chunk retains exact byte totals, the original dictionary and ordered pages. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.readGroup_wire read

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
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.convert_readback written

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

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy
