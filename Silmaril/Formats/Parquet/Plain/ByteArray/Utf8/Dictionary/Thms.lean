module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary

open Arrow.MixedFlat

/-- A malformed entry reports its original ordinal without any index lookup. -/
theorem decodeEntry_invalid {entry : Bytes} {ordinal : Nat} (invalid : ¬entry.data.IsValidUTF8) :
    decodeEntry (entry, ordinal) = .error (.invalidEntry ordinal) := by
  simp [decodeEntry, String.fromUTF8?, invalid]

/-- Strict traversal of the complete dictionary preserves every original octet. -/
theorem decodeEntries_exact {raw : List Bytes} {text : List String}
    (decoded : raw.zipIdx.mapM decodeEntry = .ok text) : text.map octets = raw :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.decodeEntries_exact decoded

/-- Every typed entry round-trips to the original PLAIN dictionary, even when unused. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {text : Array String}
    (read : readDictionary limits metadata source frame = .ok text) : DictionaryWire limits source frame text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.readDictionary_wire read

/-- The original data frame preserves the exact levels, index stream and nullable octets. -/
theorem decodePage_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array String)} {frame : Page.Frame} {text : List (Option String)}
    (read : decodePage limits metadata source dictionary frame = .ok text) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.decodePage_wire read

/-- The same snapshot determines the original selected chunk, dictionary, pages and slot order. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Checked name} {index : Nat}
    {text : List (Option String)} (read : readGroup parquet checked index = .ok text) :
    ∃ group, GroupWire parquet checked index group text :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.readGroup_wire read

/-- Native Utf8View batches preserve the checked groups and reach exact EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.convert_readback written

/-- The first failed source group keeps its complete indexed cause before IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {checked : Checked name} {before after : List Nat} {index : Nat} {earlier : List (List (Option String))}
    {cause : GroupError} (opened : openFile parquet input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary
