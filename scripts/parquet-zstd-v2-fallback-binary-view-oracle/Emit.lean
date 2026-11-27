module

import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

private def traceSlots (checked : Snappy.Checked "blob") (expected : Option Zstd.Fallback.V2.GroupError) :
    IO (List (List (Option Bytes))) := do
  let .ok ⟨selected, trace⟩ := Zstd.Fallback.V2.readAll {} checked |
    throw (IO.userError "expected a checked source trace")
  unless selected.width == 1 && List.ofFn selected.kind == [("blob", .optional)] do
    throw (IO.userError "wrong selected descriptor")
  match trace.termination, expected with
  | .eos, none => pure ()
  | .readError cause, some wanted =>
    unless cause == wanted do throw (IO.userError s!"wrong original source termination {repr cause}")
  | _, _ => throw (IO.userError "unexpected checked source termination")
  if valid : 0 < selected.width then
    return trace.batches.map (·.values ⟨0, valid⟩)
  else
    throw (IO.userError "missing selected column")

private def rejectLate (directory : System.FilePath) (file : String)
    (earlier : List (Option Bytes)) (expected : Zstd.Fallback.V2.GroupError) : IO Unit := do
  let input ← load directory file
  let bound ← bindBlob input
  let rows ← traceSlots bound (some expected)
  unless rows == [earlier] do throw (IO.userError s!"wrong complete source prefix for {file}")
  let .error (.column actual) := Zstd.Fallback.V2.convert {} { fields := 0 } {} input "blob" |
    throw (IO.userError s!"expected source refusal before IPC admission for {file}")
  unless actual == expected do throw (IO.userError s!"wrong indexed cause for {file}: {repr actual}")

private def checkPlainBudget (checked : Snappy.Checked "blob") : IO Unit := do
  let snapshot := checked.physical.snapshot
  let some group := snapshot.groupAt 0 | throw (IO.userError "first group missing")
  let some chunk := group.columns[checked.physical.binding.columnOrdinal]? | throw (IO.userError "blob chunk missing")
  let some span := Page.columnSpan snapshot.footer.start chunk.metadata | throw (IO.userError "blob span missing")
  let .ok [dictionary, _, _, _, compressed, raw] := Page.readChunk {} snapshot.bytes span |
    throw (IO.userError "wrong V2 frame structure")
  let .ok entries := Zstd.Dictionary.V2.readDictionary {} chunk.metadata snapshot.bytes dictionary |
    throw (IO.userError "expected checked dictionary entries")
  let capped : Zstd.Fallback.V2.Limits := { compression := ⟨0, 43690⟩ }
  let .ok [some value] := Zstd.Fallback.V2.decodePage capped chunk.metadata snapshot.bytes (some entries) raw |
    throw (IO.userError "literal V2 PLAIN suffix unexpectedly needed a Zstandard window")
  unless value.toList == [255] do throw (IO.userError "wrong original literal bytes")
  let .error (.decode (.plain (.decode (.zstd (.frame (.frame .windowLimit)))))) :=
    Zstd.Fallback.V2.decodePage capped chunk.metadata snapshot.bytes (some entries) compressed |
    throw (IO.userError "compressed V2 PLAIN suffix failed to enforce the window cap")

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [dictionaryOffset, indexOffset, plainCRCOffset, rawOffset, extraOffset, reentryOffset,
      v1Offset, firstDictionary, firstPlain, dictionaryExpected, dictionaryActual, indexExpected, indexActual,
      plainExpected, plainActual] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [1025, 1026]), ("v2-absent", [1025, 1026]), ("compressed-tail", [1025, 1024])] do
    let input ← load directory file
    let checked ← bindBlob input
    let observed ← traceSlots checked none
    let .ok wire := Zstd.Fallback.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque Zstandard V2 fallback conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts &&
        batches.map (List.map (Option.map KBytes.toList)) == observed.map (List.map (Option.map Bytes.toList)) do
      throw (IO.userError "source trace and native batch slots differ")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  checkPlainBudget checked
  let .error (.writer _) := Zstd.Fallback.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Zstd.Fallback.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")

  let crcError (expected actual : Nat) : Page.Checksum.Error := .mismatch (UInt32.ofNat expected) (UInt32.ofNat actual)
  rejectLate directory "bad-dictionary-crc" earlier
    (.page 1 1 "blob" 0 dictionaryOffset (.decode (.dictionary (.checksum (crcError dictionaryExpected dictionaryActual)))))
  rejectLate directory "bad-index-crc" earlier
    (.page 1 1 "blob" 1 indexOffset (.decode (.dictionary (.checksum (crcError indexExpected indexActual)))))
  rejectLate directory "bad-plain-crc" earlier
    (.page 1 1 "blob" 4 plainCRCOffset (.decode (.plain (.checksum (crcError plainExpected plainActual)))))
  rejectLate directory "bad-raw-length" earlier
    (.page 1 1 "blob" 5 rawOffset (.decode (.plain (.decode (.zstd (.scalar (.plain .integerOverflow)))))))
  rejectLate directory "extra-frame" earlier
    (.page 1 1 "blob" 4 extraOffset (.decode (.plain (.decode (.zstd (.frame (.frame .trailingInput)))))))
  rejectLate directory "reentry" earlier
    (.page 1 1 "blob" 4 reentryOffset (.decode .dictionaryAfterPlain))

  let v1 ← load directory "v1"
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Zstd.Fallback.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame")
  let .error (.column (.page 0 1 "blob" 4 header (.encoding 0))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "strict V2 dictionary admitted PLAIN")
  unless header == firstPlain do throw (IO.userError "wrong first PLAIN frame")
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedKind)) :=
    Zstd.Plain.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "strict V2 PLAIN admitted a dictionary")
  unless header == firstDictionary do throw (IO.userError "wrong leading dictionary frame")
  let dictionaryOnly ← load directory "dictionary-only"
  let .error (.column (.column 0 1 "blob" .encodings)) :=
    Zstd.Fallback.V2.convert {} tightIpc {} dictionaryOnly "blob" |
    throw (IO.userError "fallback accepted a missing PLAIN phase")
  IO.println "Lean checked native fallback, exact completed source prefixes, both flags, CRCs, and indexed revival"
