module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray
open Parquet.Plain.ByteArray.Utf8.Fallback

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original coordinates")
  let some [dictionaryHeader, unused, latePage, plainHeader, crcHeader, transitionHeader,
    cap, capPage, capHeader, expectedCRC, actualCRC] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original coordinates and limits")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  for file in ["v1-absent", "v1-crc", "v2-absent", "v2-crc"] do
    let bytes ← load directory file
    let .ok wire := Snappy.convert {} {} bytes "label" |
      throw (IO.userError s!"Snappy fallback conversion failed for {file}")
    let .ok decoded := Arrow.MixedFlat.Stream.read {} wire | throw (IO.userError "ordered IPC readback failed")
    unless decoded.fields == [⟨"label", true, .view .utf8⟩] &&
        decoded.batches.map (·.observed.rowCount) == [66, 66] do
      throw (IO.userError "wrong source group counts or descriptor")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2-crc"
  let .error (.writer _) := Snappy.convert {} tightIpc clean "label" |
    throw (IO.userError "expected the IPC limit after a complete successful source")
  let .error (.column (.page 0 1 "label" 6 _ (.encoding 0))) :=
    Utf8.Dictionary.Snappy.convert {} {} clean "label" |
    throw (IO.userError "fixed dictionary profile admitted a PLAIN fallback page")
  let .error (.column (.column 0 1 "label" (.codec 1))) := Utf8.Fallback.convert {} {} clean "label" |
    throw (IO.userError "uncompressed fallback admitted Snappy")
  let .error (.column (.page 1 1 "label" ordinal offset (.decode .expandedPageLimit))) :=
    Snappy.convert { maxExpandedPageBytes := cap } tightIpc clean "label" |
    throw (IO.userError "expected original PLAIN expansion cap before IPC")
  unless ordinal == capPage && offset == capHeader do throw (IO.userError "wrong expansion frame")
  let .ok bound := Utf8.Dictionary.openFile {} clean "label" | throw (IO.userError "original annotation failed")
  let .ok first := Snappy.readGroup {} bound 0 | throw (IO.userError "first group failed")
  for file in ["bad-unused-text", "bad-late-plain", "bad-late-crc", "dictionary-after-plain", "bad-expanded-total"] do
    let bytes ← load directory file
    let .ok checked := Utf8.Dictionary.openFile {} bytes "label" |
      throw (IO.userError "late damage changed the checked annotation")
    let .ok prefixSlots := Snappy.readGroup {} checked 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == first do throw (IO.userError "earlier group slots changed")
  let badDictionary ← load directory "bad-unused-text"
  let .error (.column (.page 1 1 "label" 0 offset (.decode (.dictionary (.decode (.text (.invalidEntry entry))))))) :=
    Snappy.convert {} tightIpc badDictionary "label" | throw (IO.userError "expected strict unused-entry error")
  unless offset == dictionaryHeader && entry == unused do throw (IO.userError "wrong dictionary entry coordinates")
  let badText ← load directory "bad-late-plain"
  let .error (.column (.page 1 1 "label" ordinal offset (.decode (.invalidPlainText 1)))) :=
    Snappy.convert {} tightIpc badText "label" | throw (IO.userError "expected indexed late PLAIN text failure")
  unless offset == plainHeader && ordinal == latePage do throw (IO.userError "wrong original PLAIN frame")
  let badCRC ← load directory "bad-late-crc"
  let .error (.column (.page 1 1 "label" ordinal offset (.decode (.checksum (.mismatch wanted actual))))) :=
    Snappy.convert {} tightIpc badCRC "label" | throw (IO.userError "expected the original CRC before text admission")
  unless offset == crcHeader && ordinal == latePage && wanted.toNat == expectedCRC && actual.toNat == actualCRC do
    throw (IO.userError "wrong original CRC coordinates or bit pattern")
  let transition ← load directory "dictionary-after-plain"
  let .error (.column (.page 1 1 "label" 6 offset (.decode .dictionaryAfterPlain))) :=
    Snappy.convert {} tightIpc transition "label" | throw (IO.userError "expected the original transition error")
  unless offset == transitionHeader do throw (IO.userError "wrong dictionary transition header")
  let badTotal ← load directory "bad-expanded-total"
  let .error (.column (.column 1 1 "label" .bounds)) := Snappy.convert {} tightIpc badTotal "label" |
    throw (IO.userError "expected exact expanded footer extent mismatch")
  for file in ["plain-only", "dictionary-only"] do
    let bytes ← load directory file
    let .error (.column (.column 0 1 "label" .encodings)) := Snappy.convert {} tightIpc bytes "label" |
      throw (IO.userError s!"expected both nonempty phases for {file}")
  IO.println "Lean checked source batches, strict dictionary and PLAIN slots, CRC precedence, frame order and expansion limits"
