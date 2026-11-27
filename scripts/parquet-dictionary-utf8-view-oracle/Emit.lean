module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def first : List (Option String) :=
  [some "é", none, some "é", some "é", some "", some "雪", some "é", some "é", none]

private def second : List (Option String) :=
  [some "雪", none, some "é", some "雪", some "", some "é", some "雪", some "é", none]

public def main (args : List String) : IO Unit := do
  let [path, dictionaryArg, indexArg] := args | throw (IO.userError "expected fixture path and original offsets")
  let (some dictOffset, some indexOffset) := (dictionaryArg.toNat?, indexArg.toNat?) |
    throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  for file in ["v1", "v2"] do
    let bytes ← load directory file
    let .ok wire := Utf8.Dictionary.convert {} {} bytes "label" |
      throw (IO.userError s!"dictionary STRING conversion failed for {file}")
    let .ok decoded := Arrow.MixedFlat.Stream.read {} wire | throw (IO.userError "ordered IPC readback failed")
    let field : Arrow.MixedFlat.Field := ⟨"label", true, .view .utf8⟩
    unless decoded.fields == [field] && decoded.batches.map Arrow.MixedFlat.StreamWriter.observeBatch ==
        [(9, some [(field, .utf8View first)]), (9, some [(field, .utf8View second)])] do
      throw (IO.userError "wrong slot order or descriptor")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2"
  let .error (.writer _) := Utf8.Dictionary.convert {} tightIpc clean "label" |
    throw (IO.userError "expected ordinary IPC limit on clean input")
  let .error (.physical (.column 0 1 "label" .encodings)) := Utf8.convert {} {} clean "label" .optional |
    throw (IO.userError "default PLAIN reader admitted dictionary encoding")
  for (file, expectedEntry) in [("bad-used-text", 0), ("bad-unused-text", 4)] do
    let bytes ← load directory file
    let .error (.column (.page 1 1 "label" 0 offset (.decode (.invalidEntry entry)))) :=
      Utf8.Dictionary.convert {} tightIpc bytes "label" |
      throw (IO.userError s!"expected strict original dictionary error for {file}")
    unless offset == dictOffset && entry == expectedEntry do throw (IO.userError "wrong dictionary entry provenance")
  let original ← load directory "bad-unused-text"
  let .ok opaqueBound := ByteArrayFallback.openFile {} original "label" |
    throw (IO.userError "opaque binding rejected optional BYTE_ARRAY")
  let .ok opaqueSlots := ByteArrayFallback.readGroup opaqueBound {} 1 |
    throw (IO.userError "opaque reader should retain its byte semantics")
  unless opaqueSlots == second.map (Option.map Utf8.Dictionary.octets) do
    throw (IO.userError "opaque bytes changed")
  let broken ← load directory "bad-index"
  let .ok checked := Utf8.Dictionary.openFile {} broken "label" |
    throw (IO.userError "index damage should preserve the checked annotation")
  let .ok earlier := Utf8.Dictionary.readGroup {} checked 0 |
    throw (IO.userError "first group should succeed before the late index failure")
  unless earlier == first do
    throw (IO.userError "first group changed before the late index failure")
  let .error (.column (.page 1 1 "label" 2 offset (.decode (.indices (.outOfBounds 7))))) :=
    Utf8.Dictionary.convert {} tightIpc broken "label" |
    throw (IO.userError "expected exact late out-of-range index before IPC limits")
  unless offset == indexOffset do throw (IO.userError "wrong index page provenance")
  let plain ← load directory "plain"
  let .error (.column (.page 0 1 "label" 0 _ (.encoding 0))) := Utf8.Dictionary.convert {} {} plain "label" |
    throw (IO.userError "PLAIN data page should be outside this profile")
  let binary ← load directory "opaque"
  let .error (.openFile .missingAnnotation) := Utf8.Dictionary.convert {} tightIpc binary "label" |
    throw (IO.userError "BYTE_ARRAY without STRING/UTF8 annotation admitted")
  IO.println "Lean matched tag-8 dictionary text and strict unused-entry and indexed source refusals"
