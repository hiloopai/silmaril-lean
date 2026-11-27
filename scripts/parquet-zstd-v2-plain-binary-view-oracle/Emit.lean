module

import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Defs

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
  let some [crcOffset, rawOffset, memberOffset, v1Offset, dictOffset, budgetOffset, literalOffset, expectedCRC, actualCRC] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid original offsets")
  let directory := System.FilePath.mk path
  let tightIpc : Arrow.Limits := { fields := 0 }
  for (file, counts) in [("v2-crc", [65, 33]), ("v2-absent", [65, 33]), ("compressed-tail", [65, 32])] do
    let input ← load directory file
    let .ok wire := Zstd.Plain.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"opaque Zstandard V2 PLAIN conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts do throw (IO.userError "wrong original group boundaries")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let clean ← load directory "v2-crc"
  let checked ← bindBlob clean
  let .error (.writer _) := Zstd.Plain.V2.convert {} tightIpc {} clean "blob" |
    throw (IO.userError "expected the IPC cap after successful source exhaustion")
  let .ok earlier := Zstd.Plain.V2.readGroup {} checked 0 | throw (IO.userError "first group failed")
  for file in ["bad-level-crc", "bad-raw-length", "extra-frame", "literal-marked-compressed"] do
    let input ← load directory file
    let bound ← bindBlob input
    let .ok prefixSlots := Zstd.Plain.V2.readGroup {} bound 0 | throw (IO.userError "earlier source group failed")
    unless prefixSlots == earlier do throw (IO.userError "earlier opaque slots changed")

  let badCRC ← load directory "bad-level-crc"
  let .error (.column (.page 1 1 "blob" 0 header (.checksum (.mismatch want got)))) :=
    Zstd.Plain.V2.convert {} tightIpc {} badCRC "blob" | throw (IO.userError "expected original raw-level CRC failure")
  unless header == crcOffset && want.toNat == expectedCRC && got.toNat == actualCRC do
    throw (IO.userError "wrong CRC offset or bits")
  let raw ← load directory "bad-raw-length"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.zstd (.scalar (.plain .integerOverflow)))))) :=
    Zstd.Plain.V2.convert {} tightIpc {} raw "blob" | throw (IO.userError "expected original raw length failure")
  unless header == rawOffset do throw (IO.userError "wrong raw PLAIN offset")
  let extra ← load directory "extra-frame"
  let .error (.column (.page 1 1 "blob" 0 header (.decode (.zstd (.frame (.frame .trailingInput)))))) :=
    Zstd.Plain.V2.convert {} tightIpc {} extra "blob" |
    throw (IO.userError "expected original Zstandard trailing-frame refusal")
  unless header == memberOffset do throw (IO.userError "wrong trailing-frame offset")
  let flagged ← load directory "literal-marked-compressed"
  let .error (.column (.page 1 1 "blob" 1 header (.decode (.zstd (.frame (.frame .badMagic)))))) :=
    Zstd.Plain.V2.convert {} tightIpc {} flagged "blob" |
    throw (IO.userError "expected original literal rewritten as compressed to fail")
  unless header == literalOffset do throw (IO.userError "wrong flagged literal offset")
  let capped : Zstd.Plain.V2.Limits := { compression := ⟨0, 43690⟩ }
  let .error (.column (.page 0 1 "blob" 0 header (.decode (.zstd (.frame (.frame .windowLimit)))))) :=
    Zstd.Plain.V2.convert capped tightIpc {} clean "blob" |
    throw (IO.userError "expected indexed Zstandard window cap ahead of IPC admission")
  unless header == budgetOffset do throw (IO.userError "wrong capped suffix offset")
  let snapshot := checked.physical.snapshot
  let some group := snapshot.groupAt 0 | throw (IO.userError "missing first group")
  let some column := group.columns[checked.physical.binding.columnOrdinal]? | throw (IO.userError "missing blob chunk")
  let some span := Page.columnSpan snapshot.footer.start column.metadata | throw (IO.userError "missing blob span")
  let .ok [_, _, rawPage] := Page.readChunk {} snapshot.bytes span | throw (IO.userError "wrong original frame list")
  let .ok [some empty] := Zstd.Plain.V2.decodePage capped column.metadata snapshot.bytes rawPage |
    throw (IO.userError "literal suffix incorrectly needed a Zstandard window")
  unless empty.length == 0 do throw (IO.userError "wrong selected literal slot")

  let v1 ← load directory "v1"
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedVersion)) :=
    Zstd.Plain.V2.convert {} tightIpc {} v1 "blob" | throw (IO.userError "expected original V1 refusal")
  unless header == v1Offset do throw (IO.userError "wrong V1 frame")
  let dictionary ← load directory "dictionary"
  let .error (.column (.page 0 1 "blob" 0 header .unsupportedKind)) :=
    Zstd.Plain.V2.convert capped tightIpc {} dictionary "blob" |
    throw (IO.userError "expected original leading dictionary refusal before expansion")
  unless header == dictOffset do throw (IO.userError "wrong original dictionary frame")
  IO.println "Lean checked Zstandard PLAIN V2 EOS, both flags, indexed CRC, exact frame and cap controls"
