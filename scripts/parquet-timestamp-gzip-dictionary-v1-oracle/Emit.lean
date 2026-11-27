module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertGzip := Leaf.Dictionary.Gzip.convert

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def expectError (label : String) (expected : Leaf.Events.ToIpc.Error)
    (result : Except Leaf.Events.ToIpc.Error KBytes) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private def readCounts (directory : System.FilePath) (index : Nat) : IO (List (Option Int)) := do
  let text ← IO.FS.readFile (directory / s!"rows-{index}.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkLate (label : String) (wire : Bytes) (earlierRows : List (List (Option Int)))
    (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.Gzip.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == earlierRows do
      throw (IO.userError s!"{label}: lost an original completed batch")
  else throw (IO.userError "expected selected field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure 2 cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure 2 cause))
    (convertGzip {} {} {ipc.batches := 0} wire 2)

private def checkCaps (wire : Bytes) : IO Unit := do
  let inputLimits : Leaf.Events.ToIpc.Limits := {}
  let bound ← require (openBound inputLimits wire 2)
  let group ← require (Leaf.Dictionary.Gzip.checkGroup {} inputLimits.leaf bound 0)
  let dictionary := group.dictionary
  let atDictionary := fun cause => Leaf.Events.ToIpc.Error.source
    (.groupFailure 0 (.dictionaryPage 0 dictionary.header.start cause))
  expectError "per-member controller cap" (atDictionary (.payload .gzipIncomplete))
    (convertGzip {gzipCalls := 0} inputLimits {} wire 2)
  expectError "dictionary entry cap" (atDictionary .entryLimit)
    (convertGzip {dictionary.maxEntries := 2} inputLimits {} wire 2)
  expectError "stored dictionary cap" (atDictionary (.checksumFailure .byteLimit))
    (convertGzip {} {inputLimits with leaf.page.compressedBytes := dictionary.value.compressedSize - 1} {} wire 2)
  expectError "expanded dictionary cap" (atDictionary (.payload .outputLimit))
    (convertGzip {} {inputLimits with leaf.page.uncompressedBytes := dictionary.value.uncompressedSize - 1} {} wire 2)
  expectError "file row cap" (.rowLimit 127 128)
    (convertGzip {} {inputLimits with maxTotalRows := 127} {} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: raw := args | throw (IO.userError "expected fixture directory and Thrift observations")
  let [some crcOrdinal, some crcOffset, some declared, some computed, some gzipOrdinal,
       some gzipOffset, some dictionaryOffset, some plainOrdinal, some plainOffset, some v2Offset] :=
    raw.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros", "outer_crc_absent"] do
    let ipc ← require (convertGzip {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) ipc.toByteArray
  let good ← input directory "utc_nanos"
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "Snappy dictionary default" (.source (.groupFailure 0 (.chunkCodec 2)))
    (Leaf.Dictionary.Snappy.convert .modernOnly {} {} {} good 2)
  expectError "wrong codec" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convertGzip {} {} {} (← input directory "snappy") 2)
  expectError "V2 data" (.source (.groupFailure 0 (.dictionaryPage 1 v2Offset (.parameters .unsupportedPage))))
    (convertGzip {} {} {} (← input directory "v2") 2)
  expectError "PLAIN fallback" (.source (.groupFailure 0 (.dictionaryPage plainOrdinal plainOffset (.encoding 0))))
    (convertGzip {} {} {} (← input directory "fallback") 2)
  checkCaps good
  let earlier ← [0, 1].mapM (readCounts directory)
  let pageCrc : Leaf.Error :=
    .dictionaryPage crcOrdinal crcOffset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))
  checkLate "outer CRC" (← input directory "bad_page_crc") earlier pageCrc
  checkLate "first indexed data error" (← input directory "double_fault") earlier pageCrc
  checkLate "GZIP data trailer CRC" (← input directory "bad_data_member") earlier
    (.dictionaryPage gzipOrdinal gzipOffset (.references (.page (.payload (.malformed .gzip)))))
  checkLate "GZIP dictionary trailer CRC" (← input directory "bad_dict_member") earlier
    (.dictionaryPage 0 dictionaryOffset (.payload (.malformed .gzip)))
  IO.println "Fourteen typed refusal controls and four exact earlier-group prefixes passed"
