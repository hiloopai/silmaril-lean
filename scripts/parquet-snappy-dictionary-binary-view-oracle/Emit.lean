module

import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original coordinates")
  let some [latePage, indexHeader, crcHeader, expectedCRC, actualCRC, mixedV1Header, mixedV2Header] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original coordinates")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for file in ["v1-absent", "v1-crc", "v2-absent", "v2-crc"] do
    let input ← load directory file
    let .ok wire := Snappy.Dictionary.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque Snappy dictionary conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == [257, 129] do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v2-crc"
  let .error (.writer _) := Snappy.Dictionary.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC limit after successful source exhaustion")
  let .ok checked := Snappy.openFile {} clean "blob" | throw (IO.userError "opaque leaf binding failed")
  let .ok earlier := Snappy.Dictionary.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-index", "bad-crc"] do
    let input ← load directory file
    let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "late damage changed the footer binding")
    let .ok prefixSlots := Snappy.Dictionary.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")
  let badIndex ← load directory "bad-index"
  let .error (.column (.page 1 1 "blob" ordinal header (.decode (.dictionary (.decode (.indices (.outOfBounds 7))))))) :=
    Snappy.Dictionary.convert {} tightIpc {} badIndex "blob" |
    throw (IO.userError "expected the original indexed out-of-range error")
  unless ordinal == latePage && header == indexHeader do throw (IO.userError "wrong index frame")
  let badCRC ← load directory "bad-crc"
  let .error (.column (.page 1 1 "blob" ordinal header (.decode (.dictionary (.decode (.checksum (.mismatch wanted got))))))) :=
    Snappy.Dictionary.convert {} tightIpc {} badCRC "blob" |
    throw (IO.userError "expected the original CRC failure before index decoding")
  unless ordinal == latePage && header == crcHeader && wanted.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong original CRC coordinates or bit patterns")
  for (file, plainHeader) in [("mixed-v1", mixedV1Header), ("mixed-v2", mixedV2Header)] do
    let input ← load directory file
    let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "mixed producer file did not bind")
    let .ok first := Snappy.Dictionary.readGroup {} bound 0 | throw (IO.userError "dictionary-only prefix group rejected")
    let .ok second := Snappy.readGroup {} bound 1 | throw (IO.userError "genuine later fallback group rejected")
    unless first.length == 64 && second.length == 64 do throw (IO.userError "wrong producer group lengths")
    let .error (.column 0 1 "blob" .encodings) := Snappy.readGroup {} bound 0 |
      throw (IO.userError "fallback should require a PLAIN phase")
    let .error (.column (.page 1 1 "blob" 6 header (.encoding 0))) :=
      Snappy.Dictionary.convert {} tightIpc {} input "blob" |
      throw (IO.userError "expected dictionary-only refusal at the first original PLAIN page")
    unless header == plainHeader do throw (IO.userError "wrong original PLAIN refusal offset")
  let text ← load directory "annotated-string"
  let .error (.openFile (.annotation 10)) := Snappy.Dictionary.convert {} tightIpc {} text "blob" |
    throw (IO.userError "STRING annotation admitted to opaque export")
  IO.println "Lean checked opaque dictionary batches and original indexed CRC, out-of-range and PLAIN refusals"
