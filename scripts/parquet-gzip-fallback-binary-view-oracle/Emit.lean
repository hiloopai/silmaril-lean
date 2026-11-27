module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and original offsets")
  let some [crcOffset, memberOffset, reentryOffset, v2Offset, budgetOffset, plainOffset, expectedCRC, actualCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for file in ["v1-crc", "v1-absent"] do
    let input ← load directory file
    let .ok wire := Gzip.Fallback.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque GZIP fallback conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == [64, 72] do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray
  let clean ← load directory "v1-crc"
  let .error (.writer _) := Gzip.Fallback.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok checked := Snappy.openFile {} clean "blob" | throw (IO.userError "opaque leaf binding failed")
  let .ok earlier := Gzip.Fallback.readGroup {} checked 0 | throw (IO.userError "first mixed group failed")
  for file in ["bad-crc", "extra-member", "reentry"] do
    let input ← load directory file
    let .ok bound := Snappy.openFile {} input "blob" | throw (IO.userError "late change broke the footer binding")
    let .ok prefixSlots := Gzip.Fallback.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")
  let badCRC ← load directory "bad-crc"
  let .error (.column (.page 1 1 "blob" 9 header (.decode (.plain (.decode (.checksum (.mismatch wanted got))))))) :=
    Gzip.Fallback.convert {} tightIpc {} badCRC "blob" |
    throw (IO.userError "expected late PLAIN CRC failure ahead of expansion and IPC")
  unless header == crcOffset && wanted.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong original CRC coordinates or bit patterns")
  let extra ← load directory "extra-member"
  let .error (.column (.page 1 1 "blob" 9 header (.decode (.plain (.decode (.plain
      (.payload (.trailingInput .gzip)))))))) := Gzip.Fallback.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected late PLAIN extra-member refusal")
  unless header == memberOffset do throw (IO.userError "wrong member frame")
  let reentry ← load directory "reentry"
  let .error (.column (.page 1 1 "blob" 6 header (.decode .dictionaryAfterPlain))) :=
    Gzip.Fallback.convert {} tightIpc {} reentry "blob" | throw (IO.userError "expected indexed reentry refusal")
  unless header == reentryOffset do throw (IO.userError "wrong reentry frame")
  let v2 ← load directory "v2"
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Gzip.Fallback.convert {} tightIpc {} v2 "blob" | throw (IO.userError "expected original V2 refusal")
  unless header == v2Offset do throw (IO.userError "wrong V2 frame")
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.dictionary (.decode (.payload .gzipIncomplete)))))) :=
    Gzip.Fallback.convert { gzipCalls := 0 } tightIpc {} clean "blob" |
    throw (IO.userError "expected original dictionary GZIP budget refusal")
  unless header == budgetOffset do throw (IO.userError "wrong budget frame")
  let dictionaryOnly ← load directory "dictionary-only"
  let .ok _ := Gzip.Dictionary.convert {} {} {} dictionaryOnly "blob" |
    throw (IO.userError "original dictionary-only profile refused a known-good source")
  let .error (.column (.column 0 1 "blob" .encodings)) := Gzip.Fallback.convert {} tightIpc {} dictionaryOnly "blob" |
    throw (IO.userError "expected missing PLAIN phase refusal")
  let .error (.column (.page 0 1 "blob" 6 header (.encoding 0))) :=
    Gzip.Dictionary.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "original dictionary-only entry point admitted fallback")
  unless header == plainOffset do throw (IO.userError "wrong first PLAIN header")
  IO.println "Lean checked native batches, indexed fallback failures, source precedence and strict dictionary admission"
