module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original coordinates")
  let some [dictionaryOffset, entry, plainPage, plainOffset, plainSlot, transitionOffset] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original coordinates")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  for file in ["v1", "v2"] do
    let bytes ← load directory file
    let .ok wire := Utf8.Fallback.convert {} {} bytes "label" |
      throw (IO.userError s!"STRING fallback conversion failed for {file}")
    let .ok decoded := Arrow.MixedFlat.Stream.read {} wire | throw (IO.userError "ordered IPC readback failed")
    unless decoded.fields == [⟨"label", true, .view .utf8⟩] &&
        decoded.batches.map (·.observed.rowCount) == [64, 64] do
      throw (IO.userError "wrong original group rows or descriptor")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2"
  let .error (.writer _) := Utf8.Fallback.convert {} tightIpc clean "label" |
    throw (IO.userError "expected IPC writer limit on a successful source")
  let .error (.column (.page 0 1 "label" 6 _ (.encoding 0))) := Utf8.Dictionary.convert {} {} clean "label" |
    throw (IO.userError "fixed dictionary profile admitted a PLAIN fallback page")
  let .ok checked := Utf8.Dictionary.openFile {} clean "label" | throw (IO.userError "STRING binding failed")
  let .ok first := Utf8.Fallback.readGroup {} checked 0 | throw (IO.userError "first source group failed")
  for file in ["bad-unused-text", "bad-plain-text", "dictionary-after-plain"] do
    let bytes ← load directory file
    let .ok bound := Utf8.Dictionary.openFile {} bytes "label" |
      throw (IO.userError "late damage should retain the original checked annotation")
    let .ok earlier := Utf8.Fallback.readGroup {} bound 0 | throw (IO.userError "earlier group failed")
    unless earlier == first do throw (IO.userError "earlier group slots changed")
  let badDictionary ← load directory "bad-unused-text"
  let .error (.column (.page 1 1 "label" 0 offset (.decode (.dictionary (.decode (.invalidEntry actual)))))) :=
    Utf8.Fallback.convert {} tightIpc badDictionary "label" |
    throw (IO.userError "expected original strict unused dictionary entry failure before IPC")
  unless offset == dictionaryOffset && actual == entry do throw (IO.userError "wrong dictionary entry coordinates")
  let badPlain ← load directory "bad-plain-text"
  let .error (.column (.page 1 1 "label" ordinal offset (.decode (.invalidPlainText slot)))) :=
    Utf8.Fallback.convert {} tightIpc badPlain "label" |
    throw (IO.userError "expected original indexed PLAIN UTF-8 failure before IPC")
  unless ordinal == plainPage && offset == plainOffset && slot == plainSlot do
    throw (IO.userError "wrong PLAIN logical slot coordinates")
  let illegal ← load directory "dictionary-after-plain"
  let .error (.column (.page 1 1 "label" 6 offset (.decode .dictionaryAfterPlain))) :=
    Utf8.Fallback.convert {} tightIpc illegal "label" |
    throw (IO.userError "expected dictionary reentry rejection before IPC")
  unless offset == transitionOffset do throw (IO.userError "wrong transition coordinates")
  for file in ["plain-only", "dictionary-only"] do
    let bytes ← load directory file
    let .error (.column (.column 0 1 "label" .encodings)) := Utf8.Fallback.convert {} tightIpc bytes "label" |
      throw (IO.userError s!"expected both nonempty phases for {file}")
  IO.println "Lean matched both ordered passes and late dictionary, PLAIN slot and transition refusals"
