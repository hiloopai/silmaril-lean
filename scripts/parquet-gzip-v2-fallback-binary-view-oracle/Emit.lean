module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

private def checkPlainBudget (checked : Snappy.Checked "blob") : IO Unit := do
  let snapshot := checked.physical.snapshot
  let some group := snapshot.groupAt 0 | throw (IO.userError "first group missing")
  let some chunk := group.columns[checked.physical.binding.columnOrdinal]? | throw (IO.userError "blob chunk missing")
  let some span := Page.columnSpan snapshot.footer.start chunk.metadata | throw (IO.userError "blob span missing")
  let .ok [_, _, _, _, compressed, raw] := Page.readChunk {} snapshot.bytes span |
    throw (IO.userError "wrong V2 frame structure")
  let capped : Gzip.Fallback.V2.Limits := { gzipCalls := 0 }
  let .ok [some value] := Gzip.Fallback.V2.decodePlainPage capped chunk.metadata snapshot.bytes raw |
    throw (IO.userError "raw V2 PLAIN suffix unexpectedly needed GZIP calls")
  unless value.toList == [255] do throw (IO.userError "wrong original raw bytes")
  let .error (.decode (.plain (.decode (.plain (.payload .gzipIncomplete))))) :=
    Gzip.Fallback.V2.decodePlainPage capped chunk.metadata snapshot.bytes compressed |
    throw (IO.userError "compressed V2 PLAIN suffix failed to enforce GZIP call cap")

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [dictOffset, crcOffset, rawOffset, memberOffset, reentryOffset, v1Offset, v2Offset, plainOffset,
      dictExpected, dictActual, plainExpected, plainActual] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [1025, 1026]), ("v2-absent", [1025, 1026]), ("compressed-tail", [1025, 1024])] do
    let input ← load directory file
    let .ok wire := Gzip.Fallback.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque GZIP V2 fallback conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  checkPlainBudget checked
  let .error (.writer _) := Gzip.Fallback.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Gzip.Fallback.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-dict-crc", "bad-plain-crc", "bad-raw-length", "extra-member", "reentry"] do
    let input ← load directory file
    let bound ← bindBlob input
    let .ok prefixSlots := Gzip.Fallback.V2.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")

  let dictCRC ← load directory "bad-dict-crc"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.dictionary (.decode (.checksum (.mismatch want got))))))) :=
    Gzip.Fallback.V2.convert {} tightIpc {} dictCRC "blob" | throw (IO.userError "expected dictionary CRC failure")
  unless header == dictOffset && want.toNat == dictExpected && got.toNat == dictActual do
    throw (IO.userError "wrong dictionary CRC offset or bits")
  let plainCRC ← load directory "bad-plain-crc"
  let .error (.column (.page 1 1 "blob" 4 header (.decode (.plain (.decode (.checksum (.mismatch want got))))))) :=
    Gzip.Fallback.V2.convert {} tightIpc {} plainCRC "blob" | throw (IO.userError "expected PLAIN CRC failure")
  unless header == crcOffset && want.toNat == plainExpected && got.toNat == plainActual do
    throw (IO.userError "wrong PLAIN CRC offset or bits")
  let raw ← load directory "bad-raw-length"
  let .error (.column (.page 1 1 "blob" 5 header (.decode (.plain (.decode (.plain (.plain .integerOverflow))))))) :=
    Gzip.Fallback.V2.convert {} tightIpc {} raw "blob" | throw (IO.userError "expected original raw length failure")
  unless header == rawOffset do throw (IO.userError "wrong raw PLAIN offset")
  let extra ← load directory "extra-member"
  let .error (.column (.page 1 1 "blob" 4 header (.decode (.plain (.decode (.plain
      (.payload (.trailingInput .gzip)))))))) := Gzip.Fallback.V2.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected original V2 PLAIN trailing-member refusal")
  unless header == memberOffset do throw (IO.userError "wrong trailing-member offset")
  let reentry ← load directory "reentry"
  let .error (.column (.page 1 1 "blob" 4 header (.decode .dictionaryAfterPlain))) :=
    Gzip.Fallback.V2.convert {} tightIpc {} reentry "blob" | throw (IO.userError "expected dictionary reentry refusal")
  unless header == reentryOffset do throw (IO.userError "wrong dictionary reentry offset")

  let v1 ← load directory "v1"
  let .ok _ := Gzip.Fallback.convert {} {} {} v1 "blob" | throw (IO.userError "strict V1 fallback failed")
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Fallback.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame")
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Fallback.convert {} tightIpc {} clean "blob" | throw (IO.userError "strict V1 fallback admitted V2")
  unless header == v2Offset do throw (IO.userError "wrong V2 frame")
  let .error (.column (.page 0 1 "blob" 4 header (.encoding 0))) :=
    Gzip.Dictionary.V2.convert {} tightIpc {} clean "blob" | throw (IO.userError "strict V2 dictionary admitted PLAIN")
  unless header == plainOffset do throw (IO.userError "wrong first PLAIN frame")
  IO.println "Lean checked V2 fallback EOS, both flags, original CRCs, member, malformed length and reentry errors"
