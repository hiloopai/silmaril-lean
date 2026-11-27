module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [crcOffset, rawOffset, memberOffset, v1Offset, dictOffset, budgetOffset, expectedCRC, actualCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [65, 33]), ("v2-absent", [65, 33]), ("compressed-tail", [65, 32])] do
    let input ← load directory file
    let .ok wire := Gzip.Plain.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque GZIP V2 PLAIN conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  let .error (.writer _) := Gzip.Plain.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Gzip.Plain.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-level-crc", "bad-raw-length", "extra-member"] do
    let input ← load directory file
    let bound ← bindBlob input
    let .ok prefixSlots := Gzip.Plain.V2.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")

  let badCRC ← load directory "bad-level-crc"
  let .error (.column (.page 1 1 "blob" 0 header (.decode (.plain (.decode (.checksum (.mismatch want got))))))) :=
    Gzip.Plain.V2.convert {} tightIpc {} badCRC "blob" | throw (IO.userError "expected original raw-level CRC failure")
  unless header == crcOffset && want.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong CRC offset or bits")
  let raw ← load directory "bad-raw-length"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.plain (.decode (.plain (.plain .integerOverflow))))))) :=
    Gzip.Plain.V2.convert {} tightIpc {} raw "blob" | throw (IO.userError "expected original raw length failure")
  unless header == rawOffset do throw (IO.userError "wrong raw PLAIN offset")
  let extra ← load directory "extra-member"
  let .error (.column (.page 1 1 "blob" 0 header (.decode (.plain (.decode (.plain
      (.payload (.trailingInput .gzip)))))))) := Gzip.Plain.V2.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected original PLAIN trailing-member refusal")
  unless header == memberOffset do throw (IO.userError "wrong trailing-member offset")
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.plain (.decode (.plain (.payload .gzipIncomplete))))))) :=
    Gzip.Plain.V2.convert { gzipCalls := 0 } tightIpc {} clean "blob" |
    throw (IO.userError "expected indexed GZIP call cap ahead of IPC admission")
  unless header == budgetOffset do throw (IO.userError "wrong capped suffix offset")

  let v1 ← load directory "v1"
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedVersion)) :=
    Gzip.Plain.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame")
  let dictionary ← load directory "dictionary"
  let .ok _ := Gzip.Dictionary.V2.convert {} {} {} dictionary "blob" |
    throw (IO.userError "strict dictionary reader refused its original profile")
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedKind)) :=
    Gzip.Plain.V2.convert { gzipCalls := 0 } tightIpc {} dictionary "blob" |
    throw (IO.userError "expected original leading dictionary refusal before expansion")
  unless header == dictOffset do throw (IO.userError "wrong original dictionary frame")
  let .error (.column (.column 0 1 "blob" .encodings)) :=
    Gzip.Dispatch.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "existing two-way dispatcher admitted PLAIN-only input")
  IO.println "Lean checked PLAIN-only EOS, both flags, indexed CRC, extent, cap and strict profile errors"
