module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray
open Parquet.Plain.ByteArray.Utf8.Dictionary

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original coordinates")
  let some [dictionaryHeader, dataHeader, lastOrdinal, dictionaryCRCHeader, dataCRCHeader,
    firstHeader, storedChunkCap, expandedChunkCap, storedPageCap, expandedPageCap,
    expectedDictionaryCRC, actualDictionaryCRC, expectedDataCRC, actualDataCRC] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original coordinates and cap values")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  for file in ["v1-absent", "v1-crc", "v2-absent", "v2-crc"] do
    let bytes ← load directory file
    let .ok wire := Snappy.convert {} {} bytes "label" |
      throw (IO.userError s!"Snappy dictionary conversion failed for {file}")
    let .ok decoded := Arrow.MixedFlat.Stream.read {} wire | throw (IO.userError "ordered IPC readback failed")
    unless decoded.fields == [⟨"label", true, .view .utf8⟩] &&
        decoded.batches.map (·.observed.rowCount) == [257, 129] do
      throw (IO.userError "wrong source group counts or descriptor")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2-crc"
  let .error (.writer _) := Snappy.convert {} tightIpc clean "label" |
    throw (IO.userError "expected the IPC limit for a complete successful source")
  let .error (.column (.column 0 1 "label" (.codec 1))) := Utf8.Dictionary.convert {} {} clean "label" |
    throw (IO.userError "default dictionary-only profile admitted Snappy")
  let .error (.column (.column 0 1 "label" .chunkLimit)) :=
    Snappy.convert { file.column.maxChunkBytes := storedChunkCap } tightIpc clean "label" |
    throw (IO.userError "expected the original stored chunk cap")
  let .error (.column (.column 0 1 "label" .chunkLimit)) :=
    Snappy.convert { maxExpandedChunkBytes := expandedChunkCap } tightIpc clean "label" |
    throw (IO.userError "expected the original expanded chunk cap")
  let .error (.column (.page 0 1 "label" 0 offset (.decode (.checksum .byteLimit)))) :=
    Snappy.convert { file.column.maxPageBytes := storedPageCap } tightIpc clean "label" |
    throw (IO.userError "expected the original stored dictionary cap")
  unless offset == firstHeader do throw (IO.userError "wrong stored dictionary frame")
  let .error (.column (.page 1 1 "label" 0 offset (.decode (.payload .outputLimit)))) :=
    Snappy.convert { maxExpandedPageBytes := expandedPageCap } tightIpc clean "label" |
    throw (IO.userError "expected the late expanded dictionary cap")
  unless offset == dictionaryCRCHeader do throw (IO.userError "wrong expanded dictionary frame")
  let .ok bound := Utf8.Dictionary.openFile {} clean "label" | throw (IO.userError "original annotation failed")
  let .ok first := Snappy.readGroup {} bound 0 | throw (IO.userError "first group failed")
  for file in ["bad-unused", "bad-index", "bad-dictionary-crc", "bad-data-crc", "bad-expanded-count"] do
    let bytes ← load directory file
    let .ok checked := Utf8.Dictionary.openFile {} bytes "label" |
      throw (IO.userError "late damage should retain the source descriptor")
    let .ok prefixSlots := Snappy.readGroup {} checked 0 | throw (IO.userError "earlier group failed")
    unless prefixSlots == first do throw (IO.userError "earlier group slots changed")
  let unused ← load directory "bad-unused"
  let .error (.column (.page 1 1 "label" 0 offset (.decode (.text (.invalidEntry 4))))) :=
    Snappy.convert {} tightIpc unused "label" | throw (IO.userError "expected strict unused UTF-8 failure")
  unless offset == dictionaryHeader do throw (IO.userError "wrong original dictionary text offset")
  let index ← load directory "bad-index"
  let .error (.column (.page 1 1 "label" ordinal offset (.decode (.indices (.outOfBounds 7))))) :=
    Snappy.convert {} tightIpc index "label" | throw (IO.userError "expected original out-of-range index")
  unless offset == dataHeader && ordinal == lastOrdinal do throw (IO.userError "wrong original index frame")
  for (file, expectedPage, expectedHeader, wantedCRC, actualCRC) in
      [("bad-dictionary-crc", 0, dictionaryCRCHeader, expectedDictionaryCRC, actualDictionaryCRC),
        ("bad-data-crc", lastOrdinal, dataCRCHeader, expectedDataCRC, actualDataCRC)] do
    let bytes ← load directory file
    let .error (.column (.page 1 1 "label" ordinal offset (.decode (.checksum (.mismatch wanted actual))))) :=
      Snappy.convert {} tightIpc bytes "label" | throw (IO.userError s!"expected stored CRC to precede {file} decode")
    unless ordinal == expectedPage && offset == expectedHeader && wanted.toNat == wantedCRC &&
        actual.toNat == actualCRC do throw (IO.userError "wrong stored CRC origin or bit pattern")
  let badTotal ← load directory "bad-expanded-count"
  let .error (.column (.column 1 1 "label" .bounds)) := Snappy.convert {} tightIpc badTotal "label" |
    throw (IO.userError "expected exact expanded footer extent mismatch")
  let uncompressed ← load directory "uncompressed"
  let .error (.column (.column 0 1 "label" (.codec 0))) := Snappy.convert {} tightIpc uncompressed "label" |
    throw (IO.userError "Snappy profile admitted codec 0")
  let plain ← load directory "plain"
  let .error (.column (.page 0 1 "label" 0 _ (.encoding 0))) := Snappy.convert {} tightIpc plain "label" |
    throw (IO.userError "Snappy dictionary profile admitted a PLAIN data page")
  IO.println "Lean checked native batches, exact stored and expanded limits, strict text, indices and both original CRC errors"
