module

import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original coordinates")
  let some [latePage, lengthHeader, indexHeader, indexValue, crcHeader, transitionHeader,
    cap, capPage, capHeader, expectedCRC, actualCRC] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original coordinates and caps")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for file in ["v1-absent", "v1-crc", "v2-absent", "v2-crc"] do
    let input ← load directory file
    let .ok wire := Snappy.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque Snappy fallback conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == [66, 66] do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2-crc"
  let .error (.writer _) := Snappy.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC limit after successful source exhaustion")
  let .ok previous := ByteArrayFallback.openFile {} clean "blob" |
    throw (IO.userError "uncompressed opaque binding rejected the footer")
  let .error (.column 0 1 "blob" (.codec 1)) := ByteArrayFallback.readGroup previous {} 0 |
    throw (IO.userError "uncompressed opaque profile admitted Snappy")
  let .error (.column (.page 1 1 "blob" ordinal offset (.decode (.plain (.decode .expandedPageLimit))))) :=
    Snappy.convert { maxExpandedPageBytes := cap } tightIpc {} clean "blob" |
    throw (IO.userError "expected the original PLAIN expansion cap before IPC")
  unless ordinal == capPage && offset == capHeader do throw (IO.userError "wrong PLAIN expansion frame")
  let .ok bound := Snappy.openFile {} clean "blob" | throw (IO.userError "opaque physical binding failed")
  let .ok first := Snappy.readGroup {} bound 0 | throw (IO.userError "first group failed")
  for file in ["bad-plain-length", "bad-index", "bad-late-crc", "dictionary-after-plain", "bad-expanded-total"] do
    let input ← load directory file
    let .ok checked := Snappy.openFile {} input "blob" |
      throw (IO.userError "late damage changed the original leaf binding")
    let .ok prefixSlots := Snappy.readGroup {} checked 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == first do throw (IO.userError "earlier opaque slots changed")
  let badLength ← load directory "bad-plain-length"
  let .error (.column (.page 1 1 "blob" ordinal offset (.decode (.plain (.decode (.plain (.plain .integerOverflow))))))) :=
    Snappy.convert {} tightIpc {} badLength "blob" | throw (IO.userError "expected late indexed PLAIN length error")
  unless offset == lengthHeader && ordinal == latePage do throw (IO.userError "wrong PLAIN length frame")
  let badIndex ← load directory "bad-index"
  let .error (.column (.page 1 1 "blob" 5 offset (.decode (.dictionary (.decode (.indices (.outOfBounds actual))))))) :=
    Snappy.convert {} tightIpc {} badIndex "blob" | throw (IO.userError "expected an out-of-range dictionary index")
  unless offset == indexHeader && actual == indexValue do throw (IO.userError "wrong original index frame")
  let badCRC ← load directory "bad-late-crc"
  let .error (.column (.page 1 1 "blob" ordinal offset (.decode (.plain (.decode (.checksum (.mismatch wanted actual))))))) :=
    Snappy.convert {} tightIpc {} badCRC "blob" | throw (IO.userError "expected original PLAIN CRC before output")
  unless offset == crcHeader && ordinal == latePage && wanted.toNat == expectedCRC && actual.toNat == actualCRC do
    throw (IO.userError "wrong original CRC coordinates or bit patterns")
  let transition ← load directory "dictionary-after-plain"
  let .error (.column (.page 1 1 "blob" 6 offset (.decode .dictionaryAfterPlain))) :=
    Snappy.convert {} tightIpc {} transition "blob" | throw (IO.userError "expected dictionary reentry refusal")
  unless offset == transitionHeader do throw (IO.userError "wrong original dictionary transition header")
  let badTotal ← load directory "bad-expanded-total"
  let .error (.column (.column 1 1 "blob" .bounds)) := Snappy.convert {} tightIpc {} badTotal "blob" |
    throw (IO.userError "expected exact expanded footer extent mismatch")
  for (file, field) in [("annotated-string", (10 : Int)), ("annotated-converted", 6)] do
    let input ← load directory file
    let .error (.openFile (.annotation actual)) := Snappy.convert {} tightIpc {} input "blob" |
      throw (IO.userError "expected original annotation refusal")
    unless actual == field do throw (IO.userError "wrong serialized annotation field")
  IO.println "Lean checked opaque BinaryView batches, original annotation refusals and indexed source-error precedence"
