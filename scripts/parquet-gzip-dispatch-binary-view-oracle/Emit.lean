module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return bound

private def sameResult (actual expected : Except Snappy.GroupError (List (Option Bytes))) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
    unless actual == expected do throw (IO.userError "selected branch changed the ordered slots")
  | .error actual, .error expected =>
    unless actual = expected do throw (IO.userError "selected branch changed the original typed failure")
  | _, _ => throw (IO.userError "selected branch changed acceptance")

private def checkFailure (directory : System.FilePath) (file : String) (index : Nat) (fallback : Bool)
    (clean : Snappy.Checked "blob") : IO Snappy.GroupError := do
  let input ← load directory file
  let bound ← bindBlob input
  for earlier in List.range index do
    let earlierResult := Gzip.Dispatch.readGroup {} bound earlier
    let .ok _ := earlierResult | throw (IO.userError "earlier mixed source group failed")
    sameResult earlierResult (Gzip.Dispatch.readGroup {} clean earlier)
  let actual := Gzip.Dispatch.readGroup {} bound index
  let expected := if fallback then Gzip.Fallback.readGroup {} bound index
    else Gzip.Dictionary.readGroup {} bound index
  sameResult actual expected
  let .error cause := actual | throw (IO.userError "damaged selected group succeeded")
  let .error (.column reported) := Gzip.Dispatch.convert {} { fields := 0 } {} input "blob" |
    throw (IO.userError "expected original source error before the IPC limit")
  unless cause = reported do throw (IO.userError "first source failure changed")
  return cause

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and indexed offsets")
  let some [dictionaryCRC, plainCRC, memberOffset, reentryOffset, plainOffset] := fields.mapM String.toNat? |
    throw (IO.userError "invalid indexed offsets")
  let directory := System.FilePath.mk path
  for (file, counts) in [("mixed-crc", [40, 64, 48]), ("mixed-absent", [40, 64])] do
    let input ← load directory file
    let bound ← bindBlob input
    for index in List.range counts.length do
      let actual := Gzip.Dispatch.readGroup {} bound index
      let .ok _ := actual | throw (IO.userError "native mixed group failed")
      sameResult actual (if index == 1 then Gzip.Fallback.readGroup {} bound index
        else Gzip.Dictionary.readGroup {} bound index)
    let .ok wire := Gzip.Dispatch.convert {} {} {} input "blob" |
      throw (IO.userError s!"mixed GZIP conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "mixed-crc"
  let bound ← bindBlob clean
  let .error (.writer _) := Gzip.Dispatch.convert {} { fields := 0 } {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .error (.column 0 1 "blob" .encodings) := Gzip.Fallback.readGroup {} bound 0 |
    throw (IO.userError "strict fallback admitted a dictionary-only group")
  let .error (.page 1 1 "blob" 6 header (.encoding 0)) := Gzip.Dictionary.readGroup {} bound 1 |
    throw (IO.userError "strict dictionary reader admitted fallback")
  unless header == plainOffset do throw (IO.userError "strict dictionary changed the first PLAIN offset")
  sameResult (Gzip.Dispatch.readGroup {} bound 3) (.error (.groupIndex 3))
  let capped : Gzip.Dispatch.Limits := { maxExpandedChunkBytes := 0 }
  sameResult (Gzip.Dispatch.readGroup capped bound 0) (Gzip.Dictionary.readGroup capped bound 0)
  sameResult (Gzip.Dispatch.readGroup capped bound 1) (Gzip.Fallback.readGroup capped bound 1)
  let .error (.column (.column 0 1 "blob" .chunkLimit)) :=
    Gzip.Dispatch.convert capped { fields := 0 } {} clean "blob" |
    throw (IO.userError "expected the original selected chunk cap before IPC admission")

  let .page 2 1 "blob" 6 header (.decode (.dictionary (.decode (.checksum (.mismatch _ _))))) ←
    checkFailure directory "late-dictionary-crc" 2 false bound |
    throw (IO.userError "expected the original dictionary branch CRC failure")
  unless header == dictionaryCRC do throw (IO.userError "wrong dictionary CRC offset")
  let .page 1 1 "blob" 8 header (.decode (.plain (.decode (.checksum (.mismatch _ _))))) ←
    checkFailure directory "double-crc" 1 true bound |
    throw (IO.userError "expected the first original CRC failure across branches")
  unless header == plainCRC do throw (IO.userError "wrong first CRC offset")
  let .page 1 1 "blob" 8 header (.decode (.plain (.decode (.plain (.payload (.trailingInput .gzip)))))) ←
    checkFailure directory "late-fallback-member" 1 true bound |
    throw (IO.userError "expected the original fallback branch member refusal")
  unless header == memberOffset do throw (IO.userError "wrong member error offset")
  let .page 1 1 "blob" 6 header (.decode .dictionaryAfterPlain) ←
    checkFailure directory "reentry" 1 true bound |
    throw (IO.userError "expected the fallback branch reentry refusal")
  unless header == reentryOffset do throw (IO.userError "wrong reentry offset")
  IO.println "Lean checked exact branch results and errors, first source failure, strict admissions and BinaryView EOS"
