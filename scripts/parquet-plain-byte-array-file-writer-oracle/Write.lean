module

import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs
meta import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File

private def raw : Bytes := Bytes.ofList [255, 0, 128]
private def long : Bytes := Bytes.ofList (List.range 256 |>.map UInt8.ofNat)

private def expectError (label : String) (written : Except Error Encoded) (expected : Error) : IO Unit := do
  let .error actual := written | throw (IO.userError s!"{label}: unexpected file")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def write (root : System.FilePath) (stem : String) (input : Input) : IO Encoded := do
  let output ← match emit {} input with
    | .ok output => pure output
    | .error cause => throw (IO.userError s!"{stem}: {repr cause}")
  let .ok checked := Plain.ByteArray.File.openFile {} output.bytes input.name input.layout
    | throw (IO.userError s!"{stem}: file reader refused output")
  let .ok values := checked.readGroup {} 0 | throw (IO.userError s!"{stem}: group zero failed")
  let .error (.groupIndex 1) := checked.readGroup {} 1
    | throw (IO.userError s!"{stem}: group one was admitted")
  let other := if input.layout == .optional then FlatColumn.Layout.required else .optional
  let .error (.schema (.leafMismatch 0 _)) :=
      Plain.ByteArray.File.openFile {} output.bytes input.name other
    | throw (IO.userError s!"{stem}: wrong nullability was admitted")
  let .ok (footer, observed) := Footer.readFooter {} output.bytes
    | throw (IO.userError s!"{stem}: footer reader refused output")
  unless checked.snapshot.groupCount == 1 && checked.binding.columnOrdinal == 0 &&
      checked.binding.leaf.name == input.name && values == input.page.slots &&
      footer == output.footer && footer.start == output.pageSpan.stop && observed == metadata input output do
    throw (IO.userError s!"{stem}: wrong descriptor, footer, or slot readback")
  IO.FS.writeBinFile (root / (stem ++ ".parquet")) output.bytes.data
  return output

private def checkLimits (input : Input) (output : Encoded) : IO Unit := do
  let exact : Limits := {
    maxFileBytes := output.bytes.length
    maxFileRows := input.page.numValues
    maxValueBytes := long.length
    column := {
      maxChunkBytes := output.page.wire.length
      maxPageBytes := output.page.body.length
      maxRows := input.page.numValues
      framing := { maxPages := 1, maxHeaderBytes := output.page.headerBytes.length } }
    snapshot := { footer := { maxFooterBytes := output.footer.stop - output.footer.start } } }
  let .ok bounded := emit exact input | throw (IO.userError "exact combined caps refused")
  unless bounded.bytes == output.bytes do throw (IO.userError "exact caps changed output bytes")
  expectError "row limit before file limit"
    (emit { exact with maxFileRows := 1, maxFileBytes := 4 } input) (.rowLimit 1 input.page.numValues)
  expectError "schema collection limit"
    (emit { exact with snapshot := { footer := { compact := { maxCollectionSize := 1 } } } } input) .schemaLimit
  expectError "schema string limit"
    (emit { exact with snapshot := { footer := { compact := { maxBinaryBytes := 5 } } } } input) .schemaLimit
  expectError "page header limit"
    (emit { exact with column := { exact.column with framing := { maxHeaderBytes := 1 } } } input) .pageBudget
  expectError "chunk preflight before file limit"
    (emit { exact with maxFileBytes := 4, column := { exact.column with maxChunkBytes := 1 } } input)
    (.chunkLimit 1 output.page.wire.length)
  expectError "minimum file extent" (emit { exact with maxFileBytes := 4 } input) .fileLimit
  expectError "file bytes bound footer serialization"
    (emit { exact with maxFileBytes := output.bytes.length - 1 } input) (.footer .byteLimit)
  expectError "footer limit"
    (emit { exact with snapshot := { footer := { maxFooterBytes := output.footer.stop - output.footer.start - 1 } } }
      input) (.footer .byteLimit)
  expectError "plain value cap"
    (emit { exact with maxValueBytes := long.length - 1 } input) (.page (.plain .valueByteLimit))
  expectError "indexed readback framing cap"
    (emit { exact with column := { exact.column with framing := { exact.column.framing with maxPages := 0 } } }
      input) (.groupReadback (.column 0 0 input.name (.framing .pageLimit)))

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let root := System.FilePath.mk directory
  let input : Input := ⟨"clés", .optional [none, some .empty, some raw, none, some long]⟩
  let optional ← write root "optional" input
  let _ ← write root "required" ⟨"raw", .required [.empty, raw, long]⟩
  let _ ← write root "optional-empty" ⟨"empty", .optional []⟩
  let _ ← write root "required-empty" ⟨"empty", .required []⟩
  checkLimits input optional
  IO.println "Four indexed writer readbacks and ten typed refusal controls passed."
