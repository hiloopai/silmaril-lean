module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and provenance coordinates")
  let some [capHeader, cap, crcHeader, textHeader, declared, computed] := fields.mapM String.toNat? |
    throw (IO.userError "invalid page provenance")
  let directory := System.FilePath.mk path
  for file in ["v1-absent", "v1-crc", "v2-absent", "v2-crc", "required"] do
    let bytes ← load directory file
    let layout : FlatColumn.Layout := if file == "required" then .required else .optional
    let .ok wire := Utf8.Snappy.convert {} {} bytes "label" layout |
      throw (IO.userError s!"Snappy STRING conversion failed for {file}")
    let .ok decoded := Arrow.MixedFlat.Stream.read {} wire | throw (IO.userError "ordered readback failed")
    unless decoded.fields == [⟨"label", layout == .optional, .view .utf8⟩] &&
        decoded.batches.map (·.observed.rowCount) == [8, 1, 5] do
      throw (IO.userError "wrong source group or native descriptor")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let tightIpc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  let clean ← load directory "v2-crc"
  let .error (.physical (.column 0 1 "label" (.codec 1))) := Utf8.convert {} {} clean "label" .optional |
    throw (IO.userError "the default STRING profile must reject Snappy")
  let .error (.column (.page 2 1 "label" 0 offset .byteLimit)) :=
    Utf8.Snappy.convert { column.maxPageBytes := cap } tightIpc clean "label" .optional |
    throw (IO.userError "expected the original expansion cap before IPC limits")
  unless offset == capHeader do throw (IO.userError "wrong capped frame")
  let badCRC ← load directory "bad-crc"
  let .error (.column (.page 2 1 "label" 1 offset (.checksum (.mismatch expected actual)))) :=
    Utf8.Snappy.convert {} tightIpc badCRC "label" .optional |
    throw (IO.userError "expected the original CRC failure before text and IPC")
  unless offset == crcHeader && expected.toNat == declared && actual.toNat == computed do
    throw (IO.userError "wrong CRC origin or bit patterns")
  let badText ← load directory "bad-text"
  let .ok checked := Utf8.openFile {} badText "label" .optional |
    throw (IO.userError "length-preserving text damage should preserve the annotation")
  let .ok previous := Utf8.Snappy.readGroup {} checked 0 | throw (IO.userError "first group rejected")
  let .ok [some ""] := Utf8.Snappy.readGroup {} checked 1 | throw (IO.userError "second group rejected")
  unless previous == [none, some "", some "é", some "é", some "雪🙂",
      some ("a".push (Char.ofNat 0) ++ "b"), some "k", none] do
    throw (IO.userError "earlier checked slot order changed")
  let .error (.column (.page 2 1 "label" 1 offset (.decode (.invalidText 0)))) :=
    Utf8.Snappy.convert {} tightIpc badText "label" .optional |
    throw (IO.userError "expected strict text error before IPC limits")
  unless offset == textHeader do throw (IO.userError "wrong frame for malformed UTF-8")
  let plain ← load directory "plain"
  let .error (.column (.column 0 1 "label" (.codec 0))) :=
    Utf8.Snappy.convert {} {} plain "label" .optional |
    throw (IO.userError "the Snappy profile must require codec 1")
  let dictionary ← load directory "dictionary"
  let .error (.column (.column 0 1 "label" .encodings)) :=
    Utf8.Snappy.convert {} {} dictionary "label" .optional |
    throw (IO.userError "dictionary encoding must stay outside this profile")
  IO.println "Lean matched ordered Snappy STRING batches and original capped, CRC and invalid-text coordinates"
