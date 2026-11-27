module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

private def checkSuffixBudget (checked : Snappy.Checked "blob") : IO Unit := do
  let snapshot := checked.physical.snapshot
  let some group := snapshot.groupAt 0 | throw (IO.userError "first group missing")
  let some chunk := group.columns[checked.physical.binding.columnOrdinal]? | throw (IO.userError "blob chunk missing")
  let some span := Page.columnSpan snapshot.footer.start chunk.metadata | throw (IO.userError "blob span missing")
  let .ok [dictionary, compressed, _, raw] := Page.readChunk {} snapshot.bytes span |
    throw (IO.userError "wrong V2 frame structure")
  let .ok entries := Gzip.Dictionary.readDictionary {} chunk.metadata snapshot.bytes dictionary |
    throw (IO.userError "dictionary frame did not decode")
  let capped : Gzip.Dictionary.Limits := { gzipCalls := 0 }
  let .ok [some empty] := Gzip.Dictionary.V2.decodePage capped chunk.metadata snapshot.bytes (some entries) raw |
    throw (IO.userError "raw V2 index suffix unexpectedly needed GZIP calls")
  unless empty.length == 0 do throw (IO.userError "wrong original raw index")
  let .error (.decode (.dictionary (.decode (.indices (.page (.payload .gzipIncomplete)))))) :=
    Gzip.Dictionary.V2.decodePage capped chunk.metadata snapshot.bytes (some entries) compressed |
    throw (IO.userError "compressed V2 suffix failed to enforce GZIP call cap")

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [indexOffset, crcOffset, memberOffset, plainOffset, v1Offset, v2Offset, expectedCRC, actualCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [257, 129, 128]), ("v2-absent", [257, 129, 128]), ("compressed-tail", [257, 128])] do
    let input ← load directory file
    let .ok wire := Gzip.Dictionary.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque GZIP V2 dictionary conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  checkSuffixBudget checked
  let .error (.writer _) := Gzip.Dictionary.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Gzip.Dictionary.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-raw-index", "bad-level-crc", "extra-member"] do
    let input ← load directory file
    let bound ← bindBlob input
    let .ok prefixSlots := Gzip.Dictionary.V2.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")

  let badIndex ← load directory "bad-raw-index"
  let .error (.column (.page 1 1 "blob" 2 header (.decode (.dictionary (.decode (.indices (.outOfBounds 7))))))) :=
    Gzip.Dictionary.V2.convert {} tightIpc {} badIndex "blob" |
    throw (IO.userError "expected the original raw index failure before IPC")
  unless header == indexOffset do throw (IO.userError "wrong raw index offset")
  let badCRC ← load directory "bad-level-crc"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.dictionary (.decode (.checksum (.mismatch wanted got))))))) :=
    Gzip.Dictionary.V2.convert {} tightIpc {} badCRC "blob" |
    throw (IO.userError "expected CRC failure over original raw levels")
  unless header == crcOffset && wanted.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong CRC offset or value")
  let extra ← load directory "extra-member"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.dictionary (.decode (.indices (.page
      (.payload (.trailingInput .gzip))))))))) := Gzip.Dictionary.V2.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected GZIP trailing-member refusal on the compressed V2 suffix")
  unless header == memberOffset do throw (IO.userError "wrong trailing-member offset")

  let fallback ← load directory "fallback"
  let .error (.column (.page 0 1 "blob" 6 header (.encoding 0))) :=
    Gzip.Dictionary.V2.convert {} tightIpc {} fallback "blob" | throw (IO.userError "expected original V2 PLAIN refusal")
  unless header == plainOffset do throw (IO.userError "wrong first PLAIN offset")
  let v1 ← load directory "v1"
  let .ok _ := Gzip.Dictionary.convert {} {} {} v1 "blob" | throw (IO.userError "strict V1 source failed")
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Dictionary.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame")
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Dictionary.convert {} tightIpc {} clean "blob" | throw (IO.userError "strict V1 reader admitted V2")
  unless header == v2Offset do throw (IO.userError "wrong V2 frame")
  IO.println "Lean checked native opaque batches and original V2 index, CRC, member, cap and profile causes"
