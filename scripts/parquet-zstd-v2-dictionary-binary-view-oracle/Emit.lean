module

import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Defs

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
  let some [dictOffset, dataOffset, indexOffset, extraOffset, fallbackPage, fallbackOffset, v1Offset,
    firstDictionary, dictCRC, alteredDictCRC, dataCRC, alteredDataCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [257, 129, 128]), ("v2-absent", [257, 129, 128]),
      ("compressed-tail", [257, 128])] do
    let input ← load directory file
    let .ok wire := Zstd.Dictionary.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"dictionary-only conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  let .error (.writer _) := Zstd.Dictionary.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Zstd.Dictionary.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-dictionary-crc", "bad-level-crc", "bad-raw-index", "extra-frame"] do
    let input ← load directory file
    let bound ← bindBlob input
    let .ok prefixSlots := Zstd.Dictionary.V2.readGroup {} bound 0 |
      throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")

  let badDictionary ← load directory "bad-dictionary-crc"
  let .error (.column (.page 1 1 "blob" 0 header (.checksum (.mismatch want got)))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} badDictionary "blob" |
    throw (IO.userError "expected the original dictionary CRC failure")
  unless header == dictOffset && want.toNat == dictCRC && got.toNat == alteredDictCRC do
    throw (IO.userError "wrong dictionary CRC offset or bits")
  let badData ← load directory "bad-level-crc"
  let .error (.column (.page 1 1 "blob" 1 header (.checksum (.mismatch want got)))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} badData "blob" |
    throw (IO.userError "expected the original raw-level CRC failure")
  unless header == dataOffset && want.toNat == dataCRC && got.toNat == alteredDataCRC do
    throw (IO.userError "wrong data CRC offset or bits")
  let badIndex ← load directory "bad-raw-index"
  let .error (.column (.page 1 1 "blob" 2 header (.decode (.indices (.outOfBounds 7))))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} badIndex "blob" |
    throw (IO.userError "expected the late literal index refusal")
  unless header == indexOffset do throw (IO.userError "wrong literal index offset")
  let extra ← load directory "extra-frame"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.zstd (.frame (.frame .trailingInput)))))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected the original trailing-frame refusal")
  unless header == extraOffset do throw (IO.userError "wrong trailing-frame offset")
  let fallback ← load directory "fallback"
  let .error (.column (.page 0 1 "blob" page header (.encoding 0))) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} fallback "blob" |
    throw (IO.userError "expected strict PLAIN fallback refusal")
  unless page == fallbackPage && header == fallbackOffset do throw (IO.userError "wrong PLAIN fallback coordinate")
  let v1 ← load directory "v1"
  let .error (.column (.page 0 1 "blob" 1 header .unsupportedVersion)) :=
    Zstd.Dictionary.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected the original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 coordinate")

  let windowCap : Zstd.Dictionary.V2.Limits := { compression := ⟨0, 43690⟩ }
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.zstd (.frame (.frame .windowLimit)))))) :=
    Zstd.Dictionary.V2.convert windowCap tightIpc {} clean "blob" |
    throw (IO.userError "expected dictionary window cap before IPC admission")
  unless header == firstDictionary do throw (IO.userError "wrong capped dictionary offset")
  let entryCap : Zstd.Dictionary.V2.Limits := { toPhysical := { maxDictionaryEntries := 4 } }
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.dictionaryEntryLimit 4 5)))) :=
    Zstd.Dictionary.V2.convert entryCap tightIpc {} clean "blob" |
    throw (IO.userError "expected dictionary entry cap before expansion")
  unless header == firstDictionary do throw (IO.userError "wrong entry cap offset")
  IO.println "Lean checked original dictionary and V2 page coordinates, native EOS, CRC, bounded indexes and frame extents"
