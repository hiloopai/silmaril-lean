module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback hiding Profile
open Gzip.Dispatch.V2.WithPlain (Profile)
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return bound

private def selectedProfile (bound : Snappy.Checked "blob") (index : Nat) : IO Profile := do
  let snapshot := bound.physical.snapshot
  let some group := snapshot.groupAt index | throw (IO.userError "missing original group")
  let some column := group.columns[bound.physical.binding.columnOrdinal]? | throw (IO.userError "missing original column")
  let some span := Page.columnSpan snapshot.footer.start column.metadata | throw (IO.userError "missing original span")
  let .ok frames := Page.readChunk {} snapshot.bytes span | throw (IO.userError "original framing failed")
  return Gzip.Dispatch.V2.WithPlain.profile frames

private def strict (profile : Profile) (bound : Snappy.Checked "blob") (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  match profile with
  | .plain => Gzip.Plain.V2.readGroup {} bound index
  | .dictionary => Gzip.Dictionary.V2.readGroup {} bound index
  | .fallback => Gzip.Fallback.V2.readGroup {} bound index

private def sameResult (actual expected : Except Snappy.GroupError (List (Option Bytes))) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
    unless actual == expected do throw (IO.userError "selected branch changed ordered slots")
  | .error actual, .error expected =>
    unless actual = expected do throw (IO.userError "selected branch changed the original typed error")
  | _, _ => throw (IO.userError "selected branch changed acceptance")

private def checkFailure (directory : System.FilePath) (file : String) (index : Nat) (profile : Profile)
    (clean : Snappy.Checked "blob") : IO Snappy.GroupError := do
  let input ← load directory file
  let bound ← bindBlob input
  for earlier in List.range index do
    let earlierResult := Gzip.Dispatch.V2.WithPlain.readGroup {} bound earlier
    let .ok _ := earlierResult | throw (IO.userError "earlier assembled group failed")
    sameResult earlierResult (Gzip.Dispatch.V2.WithPlain.readGroup {} clean earlier)
  unless (← selectedProfile bound index) = profile do throw (IO.userError "damaged group changed branch")
  let result := Gzip.Dispatch.V2.WithPlain.readGroup {} bound index
  sameResult result (strict profile bound index)
  let .error cause := result | throw (IO.userError "damaged selected group succeeded")
  let .error (.column reported) := Gzip.Dispatch.V2.WithPlain.convert {} { fields := 0 } {} input "blob" |
    throw (IO.userError "expected original source error ahead of IPC admission")
  unless reported = cause do throw (IO.userError "first indexed source failure changed")
  return cause

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [plainCRC, dictionaryCRC, reentryOffset] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let sources : List (String × List (Profile × Nat)) :=
    [("native-plain", [(.plain, 65)]), ("native-dictionary", [(.dictionary, 40)]),
      ("native-fallback", [(.fallback, 64)]), ("assembled-mixed", [(.dictionary, 40), (.plain, 65),
        (.fallback, 64), (.dictionary, 40)])]
  for (file, expected) in sources do
    let input ← load directory file
    let bound ← bindBlob input
    for ((profile, _), index) in expected.zipIdx do
      unless (← selectedProfile bound index) = profile do throw (IO.userError "wrong original header profile")
      let result := Gzip.Dispatch.V2.WithPlain.readGroup {} bound index
      let .ok _ := result | throw (IO.userError "positive three-way group failed")
      sameResult result (strict profile bound index)
    let .ok wire := Gzip.Dispatch.V2.WithPlain.convert {} {} {} input "blob" |
      throw (IO.userError s!"three-way GZIP V2 conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == expected.map Prod.snd do throw (IO.userError "wrong footer group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "assembled-mixed"
  let bound ← bindBlob clean
  let .error (.writer _) := Gzip.Dispatch.V2.WithPlain.convert {} { fields := 0 } {} clean "blob" |
    throw (IO.userError "expected IPC cap after successful source exhaustion")
  let capped : Gzip.Dispatch.V2.WithPlain.Limits := { maxExpandedChunkBytes := 0 }
  let cappedRead := Gzip.Dispatch.V2.WithPlain.readGroup capped bound 0
  sameResult cappedRead (.error (.column 0 1 "blob" .chunkLimit))
  sameResult cappedRead (Gzip.Plain.V2.readGroup capped bound 0)
  sameResult cappedRead (Gzip.Dictionary.V2.readGroup capped bound 0)
  sameResult cappedRead (Gzip.Fallback.V2.readGroup capped bound 0)

  for file in ["assembled-bad-plain-crc", "assembled-double-crc"] do
    let .page 1 1 "blob" 0 header (.decode (.plain (.decode (.checksum (.mismatch _ _))))) ←
      checkFailure directory file 1 .plain bound | throw (IO.userError "expected the first PLAIN CRC failure")
    unless header == plainCRC do throw (IO.userError "wrong original PLAIN CRC offset")
  let .page 3 1 "blob" 5 header (.decode (.dictionary (.decode (.checksum (.mismatch _ _))))) ←
    checkFailure directory "assembled-bad-dictionary-crc" 3 .dictionary bound |
    throw (IO.userError "expected the original dictionary CRC failure")
  unless header == dictionaryCRC do throw (IO.userError "wrong original dictionary CRC offset")
  let .page 2 1 "blob" 6 header (.decode .dictionaryAfterPlain) ←
    checkFailure directory "assembled-reentry" 2 .fallback bound |
    throw (IO.userError "expected the original fallback reentry failure")
  unless header == reentryOffset do throw (IO.userError "wrong original reentry offset")

  let plain ← load directory "native-plain"
  let .error (.column (.column 0 1 "blob" .encodings)) := Gzip.Dispatch.V2.convert {} {} {} plain "blob" |
    throw (IO.userError "existing two-way default admitted a PLAIN-only chunk")
  IO.println "Lean checked the three strict results, original indexed failures, common cap and BinaryView EOS"
