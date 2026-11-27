module

import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

private def traceSlots (checked : Snappy.Checked "blob") (expected : Option Snappy.GroupError) :
    IO (List (List (Option Bytes))) := do
  let .ok ⟨selected, trace⟩ := Snappy.Plain.V2.readAll {} checked |
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
    (earlier : List (Option Bytes)) (expected : Snappy.GroupError) : IO Unit := do
  let input ← load directory file
  let bound ← bindBlob input
  let rows ← traceSlots bound (some expected)
  unless rows == [earlier] do throw (IO.userError s!"wrong complete source prefix for {file}")
  let .error (.column actual) := Snappy.Plain.V2.convert {} { fields := 0 } {} input "blob" |
    throw (IO.userError s!"expected source refusal before IPC admission for {file}")
  unless actual == expected do throw (IO.userError s!"wrong indexed cause for {file}: {repr actual}")

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [crcOffset, rawOffset, extraOffset, v1Offset, dictionaryOffset, firstOffset, expectedCRC, actualCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [65, 33, 32]), ("v2-absent", [65, 33, 32]), ("compressed-tail", [65, 32])] do
    let input ← load directory file
    let checked ← bindBlob input
    let observed ← traceSlots checked none
    let .ok wire := Snappy.Plain.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque Snappy V2 PLAIN conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts &&
        batches.map (List.map (Option.map KBytes.toList)) == observed.map (List.map (Option.map Bytes.toList)) do
      throw (IO.userError "source Events and BinaryView batch slots differ")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  let .error (.writer _) := Snappy.Plain.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected IPC cap after successful source exhaustion")
  let .ok earlier := Snappy.Plain.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  let crcError := Page.Checksum.Error.mismatch (UInt32.ofNat expectedCRC) (UInt32.ofNat actualCRC)
  rejectLate directory "bad-level-crc" earlier
    (.page 1 1 "blob" 0 crcOffset (.decode (.plain (.decode (.checksum crcError)))))
  rejectLate directory "bad-raw-length" earlier
    (.page 1 1 "blob" 1 rawOffset (.decode (.plain (.decode (.plain (.plain .integerOverflow))))))
  rejectLate directory "extra-block" earlier
    (.page 1 1 "blob" 0 extraOffset (.decode (.plain (.decode (.plain (.payload (.trailingInput .snappy)))))))

  let capped : Snappy.Limits := { maxExpandedPageBytes := 0 }
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.plain (.decode .expandedPageLimit))))) :=
    Snappy.Plain.V2.convert capped tightIpc {} clean "blob" |
    throw (IO.userError "expected indexed expansion refusal before IPC admission")
  unless header == firstOffset do throw (IO.userError "wrong capped frame coordinate")

  let v1 ← load directory "v1"
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedVersion)) :=
    Snappy.Plain.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame coordinate")
  let dictionary ← load directory "dictionary"
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedKind)) :=
    Snappy.Plain.V2.convert {} tightIpc {} dictionary "blob" |
    throw (IO.userError "expected strict leading dictionary refusal")
  unless header == dictionaryOffset do throw (IO.userError "wrong leading dictionary coordinate")
  let text ← load directory "string"
  let .error (.openFile (.annotation 10)) := Snappy.Plain.V2.convert {} tightIpc {} text "blob" |
    throw (IO.userError "expected original STRING annotation refusal")
  IO.println "Lean checked exact Snappy PLAIN V2 Events and EOS, indexed CRC, suffix, cap and profile refusals"
