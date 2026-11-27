module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [crcOffset, memberOffset, v2Offset, budgetOffset, fallbackOffset, expectedCRC, actualCRC] := fields.mapM String.toNat? |
    throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for file in ["v1-absent", "v1-crc"] do
    let input ← load directory file
    let .ok wire := Gzip.Dictionary.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque GZIP dictionary conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == [9, 9] do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v1-absent"
  let .error (.writer _) := Gzip.Dictionary.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok checked := Snappy.openFile {} clean "blob" | throw (IO.userError "opaque leaf binding failed")
  let .ok earlier := Gzip.Dictionary.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-crc", "extra-member"] do
    let input ← load directory file
    let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "late damage changed the footer binding")
    let .ok prefixSlots := Gzip.Dictionary.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")
  let badCRC ← load directory "bad-crc"
  let .error (.column (.page 1 1 "blob" 2 header (.decode (.dictionary (.decode (.checksum (.mismatch wanted got))))))) :=
    Gzip.Dictionary.convert {} tightIpc {} badCRC "blob" |
    throw (IO.userError "expected the original CRC failure before GZIP expansion and IPC admission")
  unless header == crcOffset && wanted.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong original CRC coordinates or bit patterns")
  let extra ← load directory "extra-member"
  let .error (.column (.page 1 1 "blob" 2 header (.decode (.dictionary (.decode (.indices (.page
      (.payload (.trailingInput .gzip))))))))) := Gzip.Dictionary.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected the original GZIP trailing-member refusal")
  unless header == memberOffset do throw (IO.userError "wrong member frame")
  let v2 ← load directory "v2"
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Dictionary.convert {} tightIpc {} v2 "blob" | throw (IO.userError "expected original V2 refusal")
  unless header == v2Offset do throw (IO.userError "wrong V2 frame")
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.dictionary (.decode (.payload .gzipIncomplete)))))) :=
    Gzip.Dictionary.convert { gzipCalls := 0 } tightIpc {} clean "blob" |
    throw (IO.userError "expected original dictionary GZIP budget refusal")
  unless header == budgetOffset do throw (IO.userError "wrong budget frame")
  let fallback ← load directory "fallback"
  let .error (.column (.page 1 1 "blob" 6 header (.encoding 0))) :=
    Gzip.Dictionary.convert {} tightIpc {} fallback "blob" | throw (IO.userError "expected original PLAIN refusal")
  unless header == fallbackOffset do throw (IO.userError "wrong PLAIN frame")
  let annotated ← load directory "string"
  let .error (.openFile (.annotation 10)) := Gzip.Dictionary.convert {} tightIpc {} annotated "blob" |
    throw (IO.userError "expected original STRING annotation refusal")
  let .error (.column (.column 0 1 "blob" (.codec 2))) := Snappy.Dictionary.convert {} {} {} clean "blob" |
    throw (IO.userError "expected Snappy dictionary admission to still refuse GZIP")
  IO.println "Lean checked exact opaque batches and original indexed CRC, extra member, V2, fuel and PLAIN refusals"
