module

import Silmaril.Formats.Arrow.Body.Defs
import Silmaril.Formats.Arrow.StreamWriter.Defs
import Silmaril.Formats.Arrow.FileReader.Defs
import Lean.Data.Json.FromToJson.Basic

open Silmaril Silmaril.Formats.Arrow

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError label)

private def packed (bytes : ByteArray) : KBytes :=
  .leaf bytes.size (KBytes.leVal bytes.data.toList)

private def expectFailure (label : String) (source : KBytes) (error : Error)
    (limits : Limits := {}) : IO Unit :=
  match readStream limits source with
  | .error actual => check s!"{label}: expected {repr error}, got {repr actual}" (actual == error)
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def schema : List Field := [⟨"n", true, .int32⟩, ⟨"téxt", true, .utf8⟩]

private def batches : List RecordBatch :=
  [⟨4, [⟨4, 1⟩, ⟨4, 1⟩], [⟨0, 1⟩, ⟨8, 16⟩, ⟨24, 1⟩, ⟨32, 20⟩, ⟨56, 5⟩]⟩,
   ⟨0, [⟨0, 0⟩, ⟨0, 0⟩], [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 4⟩, ⟨8, 0⟩]⟩,
   ⟨1, [⟨1, 1⟩, ⟨1, 1⟩], [⟨0, 1⟩, ⟨8, 4⟩, ⟨16, 1⟩, ⟨24, 8⟩, ⟨32, 0⟩]⟩,
   ⟨1, [⟨1, 0⟩, ⟨1, 0⟩], [⟨0, 0⟩, ⟨0, 4⟩, ⟨8, 0⟩, ⟨8, 8⟩, ⟨16, 0⟩]⟩]

private def checkStream (bytes : ByteArray) (input : KBytes) (label : String) : IO Unit := do
  let stream ← match readStream {} input with
    | .ok stream => pure stream
    | .error reason => throw (IO.userError s!"{label}: {repr reason}")
  check (label ++ " schema") (stream.fields == schema)
  check (label ++ " ordered metadata") (stream.batches.map (·.metadata) == batches)
  let ranges := [(384, 448), (648, 656), (864, 896), (1104, 1120)]
  let bodies := ranges.map fun (first, stop) => (bytes.extract first stop).data.toList
  check (label ++ " exact bodies") (stream.batches.map (·.body.toList) == bodies)

private def patch (bytes : ByteArray) (offset width value : Nat) : KBytes :=
  packed <| ((KBytes.unpack width value).zipIdx).foldl
    (fun data (byte, index) => data.set! (offset + index) byte) bytes

-- Ordered observations independently read back by PyArrow in fixture.py.
private def expectedRows : List (List Row) :=
  [[[some (.int32 (-2147483648)), some (.utf8 "é")],
    [none, some (.utf8 "")],
    [some (.int32 2147483647), none],
    [some (.int32 0), some (.utf8 "雪")]],
   [],
   [[none, none]],
   [[some (.int32 17), some (.utf8 "")]]]

private def checkRows (input : KBytes) (label : String) : IO Unit := do
  match readRows {} input with
  | .ok stream =>
    check (label ++ " schema and ordered rows") (stream.fields == schema && stream.batches == expectedRows)
  | .error reason => throw (IO.userError s!"{label}: {repr reason}")

private def expectBodyFailure (label : String) (input : KBytes) (expected : Error)
    (limits : ObservationLimits := {}) : IO Unit := do
  match readRows limits input with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
  | .error actual => check s!"{label}: expected {repr expected}, got {repr actual}" (actual == expected)

private def checkedFrame (fields : List Field) (metadata : RecordBatch) (body : KBytes) :
    IO (BatchFrame fields) :=
  match validateBatch fields metadata body with
  | .ok frame => pure frame
  | .error reason => throw (IO.userError s!"synthetic frame: {repr reason}")

private def bodyRegressions (bytes : ByteArray) : IO Unit := do
  let input := packed bytes
  expectBodyFailure "bitmap null count" (patch bytes 384 1 255) (.malformed .validityBitmap)
  expectBodyFailure "bitmap omitted with nulls" (patch bytes 272 8 0) (.malformed .validityBitmap)
  expectBodyFailure "short int32 values" (patch bytes 288 8 12) (.malformed .bodyValues)
  expectBodyFailure "short utf8 offsets" (patch bytes 320 8 16) (.malformed .stringOffsets)
  expectBodyFailure "offset sign bit" (patch bytes 416 4 0x80000000) (.malformed .stringOffsets)
  expectBodyFailure "decrease at a null slot" (patch bytes 428 4 1) (.malformed .stringOffsets)
  expectBodyFailure "utf8 range exceeds data" (patch bytes 336 8 4) (.malformed .stringOffsets)
  expectBodyFailure "invalid utf8 data" (patch bytes 440 1 0xff) (.malformed .invalidUtf8)
  expectBodyFailure "invalid zero-row sentinel" (patch bytes 648 4 1) (.malformed .stringOffsets)
  expectBodyFailure "per-batch row cap" input (.limit .rows) { ipc := { rows := 3 } }
  expectBodyFailure "aggregate row cap" input (.limit .totalRows) { totalRows := 4 }
  expectBodyFailure "aggregate cell cap" input (.limit .totalCells) { totalCells := 11 }
  checkRows (patch bytes 384 1 0xfd) "unused bitmap bits"
  checkRows (patch bytes 272 8 8) "bitmap descriptor padding"
  let shortBitmap ← checkedFrame [⟨"n", true, .int32⟩]
    ⟨9, [⟨9, 1⟩], [⟨0, 1⟩, ⟨8, 36⟩]⟩ (.leaf 48 0)
  let .error (.malformed .validityBitmap) := decodeBatch {} shortBitmap
    | throw (IO.userError "nine slots cannot fit in a one-byte bitmap")
  let crossOctet ← checkedFrame [⟨"n", true, .int32⟩]
    ⟨9, [⟨9, 8⟩], [⟨0, 2⟩, ⟨8, 36⟩]⟩ (.leaf 48 0x0100)
  let .ok rows := decodeBatch {} crossOctet
    | throw (IO.userError "bitmap did not cover the second octet")
  check "second octet uses the low bit first"
    (rows == List.replicate 8 [none] ++ [[some (.int32 0)]])
  -- The bytes of a null string can be undefined, including invalid UTF-8.
  let nullBytes := KBytes.leVal ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0xff] : List UInt8)
  let nullString ← checkedFrame [⟨"text", true, .utf8⟩]
    ⟨1, [⟨1, 1⟩], [⟨0, 1⟩, ⟨8, 8⟩, ⟨16, 1⟩]⟩ (.leaf 24 nullBytes)
  let .ok [[none]] := decodeBatch {} nullString
    | throw (IO.userError "a null string may occupy undefined data bytes")
  let noColumns ← checkedFrame [] ⟨2, [], []⟩ (.leaf 0 0)
  let .ok [[], []] := decodeBatch {} noColumns
    | throw (IO.userError "zero-column batch lost rows")
  let .error (.limit .totalRows) := decodeBatch { totalRows := 1 } noColumns
    | throw (IO.userError "zero-column rows must count toward the row budget")

namespace PhysicalWriterTests

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

private structure Fixture where
  name : String
  input : BatchInput
  expected : List Row

private def mixed : Fixture :=
  ⟨"mixed", ⟨9, [
    ⟨"n", true, .int32 [some (-2147483648), none, some 2147483647, some (-1), some 0,
      none, some 42, some 17, some 8]⟩,
    ⟨"téxt", true, .utf8 [some "é", some "", none, some "雪", some "🧪", none,
      some "a", some "", some "λ"]⟩]⟩,
    [[some (.int32 (-2147483648)), some (.utf8 "é")],
     [none, some (.utf8 "")], [some (.int32 2147483647), none],
     [some (.int32 (-1)), some (.utf8 "雪")], [some (.int32 0), some (.utf8 "🧪")],
     [none, none], [some (.int32 42), some (.utf8 "a")],
     [some (.int32 17), some (.utf8 "")], [some (.int32 8), some (.utf8 "λ")]]⟩

private def cases : List Fixture :=
  [mixed,
    ⟨"empty", ⟨0, [⟨"n", false, .int32 []⟩, ⟨"téxt", true, .utf8 []⟩]⟩, []⟩,
    ⟨"zero-columns", ⟨3, []⟩, [[], [], []]⟩]

private def save (directory : System.FilePath) (name : String) {fields : List Field}
    (frame : BatchFrame fields) : IO Unit := do
  let metadata := Lean.Json.mkObj [
    ("rowCount", Lean.toJson frame.metadata.rowCount),
    ("fields", .arr (fields.map (fun f => Lean.Json.mkObj [
      ("name", Lean.toJson f.name), ("nullable", Lean.toJson f.nullable),
      ("type", Lean.toJson (if f.type == .int32 then "int32" else "utf8"))])).toArray),
    ("nodes", .arr (frame.metadata.nodes.map (fun n => Lean.Json.mkObj [
      ("length", Lean.toJson n.length), ("nullCount", Lean.toJson n.nullCount)])).toArray),
    ("buffers", .arr (frame.metadata.buffers.map (fun b => Lean.Json.mkObj [
      ("offset", Lean.toJson b.offset), ("length", Lean.toJson b.length)])).toArray)]
  IO.FS.writeBinFile (directory / (name ++ ".body")) frame.body.toByteArray
  IO.FS.writeFile (directory / (name ++ ".json")) (metadata.compress ++ "\n")

private def assertFailure (limits : ObservationLimits) (input : BatchInput) (error : Error) : IO Unit :=
  match emitBatch limits input with
  | .ok _ => throw (IO.userError s!"expected {repr error}")
  | .error actual =>
    unless actual == error do throw (IO.userError s!"expected {repr error}, got {repr actual}")

def run (directory : Option System.FilePath) : IO Unit := do
  if let some path := directory then IO.FS.createDirAll path
  for fixture in cases do
    let frame ← match emitBatch {} fixture.input with
      | .ok frame => pure frame
      | .error error => throw (IO.userError s!"emit {fixture.name}: {repr error}")
    unless frame.metadata.rowCount == fixture.input.rowCount && frame.body.len % 8 == 0 do
      throw (IO.userError s!"{fixture.name}: wrong row count or body alignment")
    unless (decodeBatch {} frame).toOption == some fixture.expected do
      throw (IO.userError s!"{fixture.name}: physical body roundtrip")
    if let some path := directory then save path fixture.name frame
  assertFailure {} ⟨2, [⟨"n", true, .int32 [some 1]⟩]⟩ (.malformed .batchLayout)
  assertFailure {} ⟨1, [⟨"n", false, .int32 [none]⟩]⟩ (.malformed .batchLayout)
  assertFailure { totalRows := 2 } ⟨3, []⟩ (.limit .totalRows)
  assertFailure { totalCells := 17 } mixed.input (.limit .totalCells)
  assertFailure { ipc := { bodyBytes := 4 } } mixed.input (.limit .bodyBytes)
  let tooMany := 2^63
  assertFailure { ipc := { rows := tooMany }, totalRows := tooMany } ⟨tooMany, []⟩
    (.malformed .batchLayout)
  IO.println "Arrow IPC V5 writer: mixed, empty, zero-column and rejection cases passed"

def runStreams (directory : Option System.FilePath) : IO Unit := do
  if let some path := directory then IO.FS.createDirAll path
  let empty := { mixed.input with rowCount := 0, columns := [
    ⟨"n", true, .int32 []⟩, ⟨"téxt", true, .utf8 []⟩] }
  let emptyBatch : BatchInput := ⟨0, [⟨"n", false, .int32 []⟩, ⟨"téxt", true, .utf8 []⟩]⟩
  let specimens : List (String × List Field × List BatchInput × List (List Row)) := [
    ("mixed", mixed.input.fields, [mixed.input, empty, mixed.input], [mixed.expected, [], mixed.expected]),
    ("empty", emptyBatch.fields, [emptyBatch], [[]]),
    ("zero-columns", [], [⟨3, []⟩, ⟨0, []⟩], [[[], [], []], []]),
    ("schema-only", [⟨"", false, .utf8⟩], [], [])]
  for (name, fields, inputs, expected) in specimens do
    let counts := inputs.map (·.rowCount)
    let limits : ObservationLimits := {
      ipc := { fields := fields.length, rows := counts.foldl max 0, batches := inputs.length }
      totalRows := counts.sum
      totalCells := fields.length * counts.sum
    }
    let .ok bytes := StreamWriter.emit limits fields inputs
      | throw (IO.userError s!"{name}: stream emission failed")
    let wire := packed bytes.toByteArray
    let .ok stream := readStream limits.ipc wire
      | throw (IO.userError s!"{name}: stream metadata read failed")
    check s!"{name}: schema and explicit counts"
      (stream.fields == fields && stream.batches.map (·.metadata.rowCount) == counts)
    let .ok expectedMetadata := inputs.mapM (fun input => (emitBatch {} input).map (·.metadata))
      | throw (IO.userError s!"{name}: physical batches failed")
    check s!"{name}: exact record metadata"
      (stream.batches.map (·.metadata) == expectedMetadata)
    let .ok rows := readRows limits wire
      | throw (IO.userError s!"{name}: ordered stream read failed")
    check s!"{name}: ordered rows" (rows == ⟨fields, expected⟩)
    check s!"{name}: continuation and EOS"
      (wire.read 0 4 == 0xffffffff && wire.read (wire.len - 8) 8 == 0xffffffff)
    expectFailure s!"{name}: EOS required" (wire.slice 0 (wire.len - 8)) (.malformed .truncated)
    if let some path := directory then IO.FS.writeBinFile (path / (name ++ ".arrows")) bytes.toByteArray
  let .error (.limit .metadataBytes) := StreamWriter.emit { ipc := { metadataBytes := 64 } } [] []
    | throw (IO.userError "metadata budget accepted")
  let .error (.limit .batches) := StreamWriter.emit { ipc := { batches := 1 } } [] [⟨0, []⟩, ⟨0, []⟩]
    | throw (IO.userError "batch budget accepted")
  let .error (.limit .totalRows) := StreamWriter.emit { totalRows := 2 } [] [⟨1, []⟩, ⟨2, []⟩]
    | throw (IO.userError "aggregate zero-column row budget accepted")
  let .error (.malformed .batchLayout) := StreamWriter.emit {} [] [mixed.input]
    | throw (IO.userError "inconsistent schema accepted")
  let oversized : RecordBatch := ⟨0, [⟨0, 2^63⟩], []⟩
  let .error (.malformed .flatbuffer) := MetadataWriter.emit {} ⟨.recordBatch oversized, 0⟩
    | throw (IO.userError "nonrepresentable field node accepted")
  IO.println "Arrow IPC V5 stream writer: exact metadata, ordered nullable rows, counts and EOS passed"

end PhysicalWriterTests

private def fileFixture (name : String) : IO ByteArray :=
  IO.FS.readBinFile (System.FilePath.mk "tests/formats/arrow-ipc" / name)

private def expectFileFailure (label : String) (input : KBytes) (expected : Error)
    (limits : ObservationLimits := {}) : IO Unit := do
  match FileReader.readRows limits input with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
  | .error error => check s!"{label}: {repr error}" (error == expected)

private def fileRegressions : IO Unit := do
  let bytes ← fileFixture "file-mixed.arrow"
  let source := packed bytes
  let index ← match FileReader.readIndex {} source with
    | .ok index => pure index
    | .error error => throw (IO.userError s!"file index: {repr error}")
  check "file footer interval" (index.span.start == 1136 && index.span.length == 280)
  check "embedded schema and block index"
    (index.footer.fields == schema && index.schemaEnd == 184 && index.footer.blocks ==
      [⟨184, 208, 64⟩, ⟨456, 200, 8⟩, ⟨664, 208, 32⟩, ⟨904, 208, 16⟩])
  for n in [:expectedRows.length + 1] do
    let .ok rows := index.readRowsAt {} n | throw (IO.userError s!"file batch {n}")
    check s!"indexed file batch {n}" (rows == expectedRows[n]?)
  for (name, fields, expected) in [
      ("file-mixed.arrow", schema, expectedRows),
      ("file-schema-only.arrow", schema, []),
      ("file-zero-columns.arrow", [], [[[], [], []], []])] do
    let source := packed (← fileFixture name)
    let .ok observed := FileReader.readRows {} source
      | throw (IO.userError s!"file materialization {name}")
    check s!"file observations {name}" (observed == ⟨fields, expected⟩)
  for split in [8, 392, 1128, 1136, 1179, 1416] do
    let carrier := packed (bytes.extract 0 split) ++ packed (bytes.extract split bytes.size)
    let .ok observed := FileReader.readRows {} carrier
      | throw (IO.userError s!"file at byte split {split}")
    check s!"file observations at byte split {split}" (observed == ⟨schema, expectedRows⟩)
  expectFileFailure "leading magic" (patch bytes 0 1 0) (.malformed .source)
  expectFileFailure "trailing magic" (patch bytes 1425 1 0) (.malformed .source)
  expectFileFailure "nonzero leading padding" (patch bytes 6 1 1) (.malformed .alignment)
  expectFileFailure "negative footer length" (patch bytes 1416 4 (2^31)) (.malformed .metadataLength)
  expectFileFailure "footer starts before magic" (patch bytes 1416 4 1424) (.malformed .truncated)
  expectFileFailure "unaligned footer" (patch bytes 1416 4 281) (.malformed .alignment)
  expectFileFailure "missing EOS" (patch bytes 1132 4 8) (.malformed .trailingBytes)
  expectFileFailure "footer schema differs" (patch bytes 1392 1 0x78) (.malformed .schemaOrder)
  expectFileFailure "footer version" (patch bytes 1158 2 3) (.unsupported (.metadataVersion 3))
  -- A length word at 1176 leaves room for one struct at 1180, but the element is unaligned.
  let shiftedVector := (patch bytes 1168 4 8).toByteArray
  expectFileFailure "unaligned nonempty block vector" (patch shiftedVector 1176 4 1)
    (.malformed .flatbuffer)
  expectFileFailure "negative offset" (patch bytes 1176 8 (2^63)) (.malformed .flatbuffer)
  expectFileFailure "negative metadata length" (patch bytes 1184 4 (2^31)) (.malformed .flatbuffer)
  expectFileFailure "unaligned indexed length" (patch bytes 1184 4 207) (.malformed .batchLayout)
  expectFileFailure "repeated block offset" (patch bytes 1200 8 184) (.malformed .batchLayout)
  expectFileFailure "displaced first block" (patch bytes 1176 8 192) (.malformed .batchLayout)
  expectFileFailure "block outside file" (patch bytes 1248 8 4096) (.malformed .batchLayout)
  expectFileFailure "footer overlap" (patch bytes 1264 8 32) (.malformed .batchLayout)
  -- Keep the full block extent identical while making footer and message disagree.
  let wrongMetadata := (patch bytes 1184 4 216).toByteArray
  expectFileFailure "metadata length disagrees with prefix" (patch wrongMetadata 1192 8 56)
    (.malformed .metadataLength)
  expectFileFailure "body length disagrees with message" (patch bytes 224 8 56) (.malformed .bodyLength)
  expectFileFailure "blocks omitted from index" (patch bytes 1172 4 0) (.malformed .batchLayout)
  expectFileFailure "file footer byte cap" (packed bytes) (.limit .metadataBytes)
    { ipc := { metadataBytes := 279 } }
  expectFileFailure "file batch cap" (packed bytes) (.limit .batches)
    { ipc := { batches := 3 } }
  expectFileFailure "file aggregate cells" (packed bytes) (.limit .totalCells) { totalCells := 11 }
  expectFileFailure "dictionary file" (packed (← fileFixture "file-dictionary.arrow")) (.unsupported .dictionary)
  expectFileFailure "Int64 file" (packed (← fileFixture "file-int64.arrow")) (.unsupported .fieldInteger)
  IO.println "Arrow IPC V5 file: footer ranges, indexed observations, errors and budgets passed"

public def main (args : List String) : IO Unit := do
  let (bodyDirectory, streamDirectory) ← match args with
    | [] => pure (none, none)
    | ["--write-body-fixtures", output] => pure (some (System.FilePath.mk output), none)
    | ["--write-stream-fixtures", output] => pure (none, some (System.FilePath.mk output))
    | _ => throw (IO.userError "usage: arrow_ipc_metadata_tests [--write-body-fixtures DIR | --write-stream-fixtures DIR]")
  let bytes ← IO.FS.readBinFile "tests/formats/arrow-ipc/nullable-int32-utf8.arrows"
  check "fixture length" (bytes.size == 1128)
  let input := packed bytes
  for split in [:bytes.size + 1] do
    let left := packed (bytes.extract 0 split)
    let right := packed (bytes.extract split bytes.size)
    checkStream bytes (left ++ right) s!"split {split}"
    checkRows (left ++ right) s!"body split {split}"
  for stop in [:bytes.size] do
    expectFailure s!"truncation at {stop}" (packed (bytes.extract 0 stop)) (.malformed .truncated)
  let eos := packed (bytes.extract 1120 1128)
  let schemaFrame := packed (bytes.extract 0 176)
  expectFailure "no schema" eos (.malformed .schemaOrder)
  expectFailure "record batch first" (packed (bytes.extract 176 bytes.size)) (.malformed .schemaOrder)
  expectFailure "repeated schema" (schemaFrame ++ schemaFrame ++ eos) (.malformed .schemaOrder)
  expectFailure "trailing octet" (input ++ .leaf 1 0) (.malformed .trailingBytes)
  expectFailure "bad continuation" (patch bytes 0 4 0) (.malformed .continuation)
  expectFailure "legacy prefix" (patch bytes 0 4 168) (.unsupported .legacyFraming)
  expectFailure "negative length" (patch bytes 4 4 0x80000000) (.malformed .metadataLength)
  expectFailure "misaligned metadata length" (patch bytes 4 4 167) (.malformed .metadataLength)
  expectFailure "invalid root offset" (patch bytes 8 4 0) (.malformed .flatbuffer)
  expectFailure "invalid vtable size" (patch bytes 14 2 9) (.malformed .flatbuffer)
  expectFailure "invalid vtable displacement" (patch bytes 24 4 0) (.malformed .flatbuffer)
  expectFailure "unsupported V4" (patch bytes 30 2 3) (.unsupported (.metadataVersion 3))
  expectFailure "missing message union tag" (patch bytes 29 1 0) (.malformed .flatbuffer)
  expectFailure "unknown message tag" (patch bytes 29 1 42) (.unsupported (.messageKind 42))
  expectFailure "unknown field type tag" (patch bytes 71 1 42) (.unsupported (.fieldType 42))
  expectFailure "field name UTF-8" (patch bytes 92 1 0xff) (.malformed .invalidUtf8)
  expectFailure "field name terminator" (patch bytes 97 1 1) (.malformed .flatbuffer)
  expectFailure "non-boolean nullable" (patch bytes 70 1 2) (.malformed .flatbuffer)
  expectFailure "negative body length" (patch bytes 216 8 (2^63)) (.malformed .bodyLength)
  expectFailure "misaligned body length" (patch bytes 216 8 63) (.malformed .bodyLength)
  expectFailure "vector exceeds metadata" (patch bytes 260 4 0xffffffff) (.malformed .flatbuffer)
  expectFailure "missing buffer descriptor" (patch bytes 260 4 4) (.malformed .batchLayout)
  expectFailure "short field node" (patch bytes 352 8 3) (.malformed .batchLayout)
  expectFailure "excess null count" (patch bytes 360 8 5) (.malformed .batchLayout)
  expectFailure "null in required field" (patch bytes 130 1 0) (.malformed .batchLayout)
  expectFailure "misaligned buffer offset" (patch bytes 280 8 9) (.malformed .batchLayout)
  expectFailure "overlapping buffers" (patch bytes 280 8 0) (.malformed .batchLayout)
  expectFailure "buffer exceeds body" (patch bytes 336 8 16) (.malformed .batchLayout)
  expectFailure "metadata byte cap" input (.limit .metadataBytes) { metadataBytes := 167 }
  expectFailure "body byte cap" input (.limit .bodyBytes) { bodyBytes := 63 }
  expectFailure "field cap" input (.limit .fields) { fields := 1 }
  expectFailure "row cap" input (.limit .rows) { rows := 3 }
  expectFailure "batch cap" input (.limit .batches) { batches := 3 }
  let .ok zeroBatches := readStream { batches := 0 } (schemaFrame ++ eos)
    | throw (IO.userError "schema and EOS should fit a zero batch cap")
  check "schema-only stream" (zeroBatches.fields == schema && zeroBatches.batches.isEmpty)
  IO.println "Arrow IPC V5 metadata: 1129 split points, 1128 truncations, and malformed, unsupported and limit cases passed"
  bodyRegressions bytes
  IO.println "Arrow IPC V5 body: ordered PyArrow rows across 1129 split points and malformed-body and budget cases passed"
  PhysicalWriterTests.run bodyDirectory
  PhysicalWriterTests.runStreams streamDirectory
  fileRegressions
