module

import Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray

private def load (root : System.FilePath) (stem : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (root / "source" / (stem ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def expectError (label : String) (written : Except FromIpc.Error PlainByteArrayV1Writer.File.Encoded)
    (expected : FromIpc.Error) : IO Unit := do
  let .error actual := written | throw (IO.userError s!"{label}: unexpected file")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def checkLimits (root : System.FilePath) (input : KBytes) (ipc : Arrow.Limits)
    (output : PlainByteArrayV1Writer.File.Encoded) : IO Unit := do
  let badWriter : File.Limits := { maxFileBytes := 4, maxFileRows := 0 }
  expectError "trailing octet before writer caps"
    (FromIpc.convert ipc {} badWriter (← load root "trailing"))
    (.source (.batch 3 .trailingBytes))
  expectError "missing EOS before writer caps"
    (FromIpc.convert ipc {} badWriter (← load root "missing-eos"))
    (.source (.batch 3 (.envelope (.malformed .truncated))))
  expectError "source batch cap before writer"
    (FromIpc.convert { ipc with batches := 2 } {} badWriter input) (.source (.batch 2 .batchLimit))
  expectError "required null in late source batch"
    (FromIpc.convert {} {} badWriter (← load root "required-null"))
    (.source (.batch 1 (.decode .invalidNode)))
  expectError "checked Utf8View profile"
    (FromIpc.convert {} {} badWriter (← load root "text")) .expectedBinaryView
  expectError "writer aggregate row limit"
    (FromIpc.convert ipc {} { maxFileRows := 4, maxFileBytes := 4 } input) (.writer (.rowLimit 4 5))
  expectError "writer one-group page rows"
    (FromIpc.convert ipc {} { column := { maxRows := 3 } } input) (.writer .pageBudget)
  expectError "writer value limit"
    (FromIpc.convert ipc {} { maxValueBytes := 255 } input) (.writer (.page (.plain .valueByteLimit)))
  expectError "writer minimum file limit"
    (FromIpc.convert ipc {} { maxFileBytes := 4 } input) (.writer .fileLimit)
  expectError "writer footer still needs a byte"
    (FromIpc.convert ipc {} { maxFileBytes := output.bytes.length - 1 } input) (.writer (.footer .byteLimit))

private def check (root : System.FilePath) (stem name : String) (nullable : Bool)
    (counts : List Nat) : IO Unit := do
  let input ← load root stem
  let ipc : Arrow.Limits := { fields := 1, rows := counts.foldl max 0, batches := counts.length }
  let .ok source := FromIpc.readSource ipc {} input
    | throw (IO.userError s!"{stem}: checked source failed")
  unless source.name == name && source.nullable == nullable && source.batches.map List.length == counts do
    throw (IO.userError s!"{stem}: original descriptor or batches changed")
  let limits : File.Limits := { maxFileRows := counts.sum, maxValueBytes := 256 }
  let output ← match FromIpc.convert ipc {} limits input with
    | .ok output => pure output
    | .error cause => throw (IO.userError s!"{stem}: {repr cause}")
  let .ok exact := FromIpc.convert ipc {} { limits with maxFileBytes := output.bytes.length } input
    | throw (IO.userError s!"{stem}: exact writer file limit refused")
  unless exact.bytes == output.bytes do
    throw (IO.userError s!"{stem}: exact writer cap changed the output")
  let selection : FlatColumn.Layout := if nullable then .optional else .required
  let .ok checked := File.openFile limits output.bytes name selection
    | throw (IO.userError s!"{stem}: checked Parquet source failed")
  let .ok actual := checked.readGroup limits 0
    | throw (IO.userError s!"{stem}: group zero failed")
  let .error (.groupIndex 1) := checked.readGroup limits 1
    | throw (IO.userError s!"{stem}: group one was admitted")
  let some prepared := PlainByteArrayV1Writer.File.Input.ofSlots name selection source.slots
    | throw (IO.userError s!"{stem}: prep did not retain the selected descriptor")
  let .ok (span, footer) := Footer.readFooter limits.snapshot.footer output.bytes
    | throw (IO.userError s!"{stem}: original footer failed")
  unless checked.binding.columnOrdinal == 0 && checked.snapshot.groupCount == 1 &&
      actual == source.slots && span == output.footer &&
      footer == PlainByteArrayV1Writer.File.metadata prepared output do
    throw (IO.userError s!"{stem}: exact descriptor, footer, or flattened slots changed")
  if stem == "optional" then checkLimits root input ipc output
  IO.FS.writeBinFile (root / (stem ++ ".parquet")) output.bytes.data

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected fixture directory")
  let root := System.FilePath.mk directory
  check root "optional" "octets, café" true [2, 0, 3]
  check root "required" "raw" false [2, 1]
  check root "schema-only" "empty" true []
  check root "explicit-empty" "empty" false [0]
  IO.println "Four native BinaryView-to-Parquet files, exact caps and ten typed refusals checked."
