module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (expected : Leaf.Events.ToIpc.Error)
    (result : Except Leaf.Events.ToIpc.Error KBytes) : IO Unit := do
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private abbrev convert := Leaf.Fallback.Snappy.convert

private def parseSlot (line : String) : Option (Option Int) :=
  if line == "null" then some none else line.toInt?.map some

private def checkLate (expectedPrefix : List (Option Int)) (profile : AnnotationProfile)
    (wire : Bytes) (error : Leaf.Error) : IO Unit := do
  let cause : Leaf.Events.Error := .groupFailure 1 error
  let bound ← require (Leaf.openLeafWith profile {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Snappy.readBound {} {} bound)
  if column : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, column⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == [expectedPrefix] do
      throw (IO.userError "late fallback failure lost its complete group prefix")
  else throw (IO.userError "missing TIMESTAMP field")
  match trace.termination with
  | .readError actual => unless actual == cause do throw (IO.userError s!"unexpected {repr actual}")
  | _ => throw (IO.userError "expected original indexed Snappy fallback error")
  expectError "source error precedes IPC admission" (.source cause)
    (convert profile {} {} {ipc.batches := 0} wire 2)

private def checkAdmission (wire dictionaryOnly uncompressed : Bytes) : IO Unit := do
  let bound ← require (Leaf.openLeaf {} wire 2)
  let first ← require (Leaf.Fallback.Snappy.checkGroup {} {} bound 0)
  let dictionaryData :: plain :: _ := first.data | throw (IO.userError "expected both data segments")
  let settings : Leaf.Events.ToIpc.Limits := {}
  expectError "default PLAIN codec" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Events.ToIpc.convert {} {} wire 2)
  expectError "PLAIN Snappy ignores mixed encoding" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {leaf.allowSnappy := true} {} wire 2)
  expectError "uncompressed dictionary profile" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Dictionary.convert .modernOnly {} {leaf.allowSnappy := true} {} wire 2)
  expectError "uncompressed fallback profile" (.source (.groupFailure 0 (.chunkCodec 1)))
    (Leaf.Fallback.convert .modernOnly {} {leaf.allowSnappy := true} {} wire 2)
  expectError "Snappy dictionary-only profile"
    (.source (.groupFailure 0 (.dictionaryPage 2 plain.frame.header.start (.encoding 0))))
    (Leaf.Dictionary.Snappy.convert .modernOnly {} {} {} wire 2)
  expectError "fallback requires codec 1" (.source (.groupFailure 0 (.chunkCodec 0)))
    (convert .modernOnly {} {leaf.allowSnappy := true} {} uncompressed 2)
  expectError "fallback requires a PLAIN suffix" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (convert .modernOnly {} {} {} dictionaryOnly 2)
  expectError "group row limit" (.source (.groupFailure 0 .rowLimit))
    (convert .modernOnly {} {leaf.maxRows := 767} {} wire 2)
  expectError "total row limit" (.rowLimit 1535 1536)
    (convert .modernOnly {} {maxTotalRows := 1535} {} wire 2)
  expectError "selected chunk byte limit" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (convert .modernOnly {maxChunkBytes := 1} {} {} wire 2)
  expectError "stored dictionary byte limit"
    (.source (.groupFailure 0 (.dictionaryPage 0 first.dictionary.header.start (.checksumFailure .byteLimit))))
    (convert .modernOnly {} {settings with leaf.page.compressedBytes := 0} {} wire 2)
  expectError "expanded PLAIN page size limit"
    (.source (.groupFailure 0 (.dictionaryPage 2 plain.frame.header.start (.plain (.payload .outputLimit)))))
    (convert .modernOnly {} {settings with leaf.page.uncompressedBytes :=
      dictionaryData.params.sizes.uncompressed} {} wire 2)

private def mismatch (offset expected actual : Nat) (ordinal : Nat) : Leaf.Error :=
  .dictionaryPage ordinal offset (.checksumFailure (.mismatch (UInt32.ofNat expected) (UInt32.ofNat actual)))

public def main (args : List String) : IO Unit := do
  let folder :: rest := args | throw (IO.userError "expected directory and indexed error evidence")
  let some [dictOffset, dictCRC, dictActual, plainOffset, plainCRC, plainActual,
    levelOffset, levelCRC, levelActual, suffixOffset] := rest.mapM String.toNat?
    | throw (IO.userError "invalid error evidence")
  let directory : System.FilePath := folder
  let cases : List (String × AnnotationProfile) :=
    [("v1", .modernOnly), ("v2", .modernOnly), ("legacy", .allowConvertedOnly)]
  for (name, profile) in cases do
    let output ← require (convert profile {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  checkAdmission (← input directory "v1") (← input directory "dictionary_only") (← input directory "uncompressed")
  let text ← IO.FS.readFile (directory / "prefix.txt")
  let some expectedPrefix := (text.splitOn "\n").mapM parseSlot | throw (IO.userError "invalid slot golden")
  unless expectedPrefix.length == 768 do throw (IO.userError "incomplete slot golden")
  checkLate expectedPrefix .modernOnly (← input directory "bad_dictionary") (mismatch dictOffset dictCRC dictActual 0)
  checkLate expectedPrefix .modernOnly (← input directory "bad_v1_plain") (mismatch plainOffset plainCRC plainActual 3)
  checkLate expectedPrefix .modernOnly (← input directory "bad_levels") (mismatch levelOffset levelCRC levelActual 3)
  checkLate expectedPrefix .allowConvertedOnly (← input directory "bad_suffix")
    (.dictionaryPage 3 suffixOffset (.plain (.payload .outputSizeMismatch)))
  IO.println "Twelve typed admission and budget refusals and four exact late-error prefixes passed"
