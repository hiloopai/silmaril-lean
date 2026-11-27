module

import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.Defs
meta import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups

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
  let .error (.groupIndex failed) := checked.readGroup {} input.groups.length
    | throw (IO.userError s!"{stem}: one-past-end group was admitted")
  unless failed == input.groups.length && checked.snapshot.groupCount == input.groups.length &&
      checked.binding.columnOrdinal == 0 && checked.binding.leaf.name == input.name do
    throw (IO.userError s!"{stem}: wrong leaf or group count")
  for (slots, index) in input.groups.zipIdx do
    let .ok values := checked.readGroup {} index | throw (IO.userError s!"{stem}: group {index} failed")
    unless values == slots do throw (IO.userError s!"{stem}: wrong slots in group {index}")
  let other := if input.layout == .optional then FlatColumn.Layout.required else .optional
  let .error (.schema (.leafMismatch 0 _)) :=
      Plain.ByteArray.File.openFile {} output.bytes input.name other
    | throw (IO.userError s!"{stem}: wrong nullability was admitted")
  IO.FS.writeBinFile (root / (stem ++ ".parquet")) output.bytes.data
  return output

private def checkLimits (input : Input) (output : Encoded) : IO Unit := do
  let some lastData := output.groups[2]? | throw (IO.userError "missing later data group")
  let footerSize := output.footer.stop - output.footer.start
  let maximum (f : Group → Nat) := (output.groups.map f).foldl max 0
  let exact : Limits := {
    maxGroups := input.groups.length
    file := {
      maxFileBytes := output.bytes.length
      maxFileRows := input.totalRows
      maxValueBytes := long.length
      column := {
        maxChunkBytes := maximum (·.page.wire.length)
        maxPageBytes := maximum (·.page.body.length)
        maxRows := maximum Group.rows
        framing := { maxPages := 1, maxHeaderBytes := maximum (·.page.headerBytes.length) } }
      snapshot := { footer := {
        maxFooterBytes := footerSize
        compact := { maxCollectionSize := input.groups.length } } } } }
  let .ok bounded := emit exact input | throw (IO.userError "exact combined caps refused")
  unless bounded.bytes == output.bytes do throw (IO.userError "exact caps changed output bytes")
  let file := exact.file
  let column := file.column
  let snapshot := file.snapshot
  let footer := snapshot.footer
  expectError "group cap precedes row cap"
    (emit { exact with maxGroups := 3, file := { file with maxFileRows := 0 } } input)
    (.groupLimit 3 4)
  expectError "Compact collection cap limits groups"
    (emit { exact with file := { file with snapshot := { snapshot with footer := {
      footer with compact := { footer.compact with maxCollectionSize := 3 } } } } } input)
    (.groupLimit 3 4)
  expectError "aggregate rows precede file cap"
    (emit { exact with file := { file with maxFileRows := 4, maxFileBytes := 4 } } input) (.rowLimit 4 5)
  expectError "schema string bound"
    (emit { exact with file := { file with snapshot := { snapshot with footer := {
      footer with compact := { footer.compact with maxBinaryBytes := 5 } } } } } input)
    .schemaLimit
  expectError "null in later required group"
    (emit {} ⟨"raw", .required, [[some raw], [], [none]]⟩) (.requiredSlot 2)
  expectError "later page body bound"
    (emit { exact with file := { file with column := { column with
      maxPageBytes := lastData.page.body.length - 1 } } } input) (.pageBudget 2)
  let chunkCap := lastData.page.wire.length - 1
  expectError "later chunk byte bound"
    (emit { exact with file := { file with column := { column with maxChunkBytes := chunkCap } } } input)
    (.chunkLimit 2 chunkCap lastData.page.wire.length)
  expectError "aggregate data extent"
    (emit { exact with file := { file with maxFileBytes := output.footer.start + 7 } } input)
    .fileLimit
  expectError "aggregate file byte bound"
    (emit { exact with file := { file with maxFileBytes := output.bytes.length - 1 } } input) (.footer .byteLimit)
  expectError "footer byte bound"
    (emit { exact with file := { file with snapshot := { snapshot with footer := {
      footer with maxFooterBytes := footerSize - 1 } } } } input) (.footer .byteLimit)
  expectError "later value byte bound"
    (emit { exact with file := { file with maxValueBytes := long.length - 1 } } input)
    (.page 2 (.plain .valueByteLimit))
  expectError "indexed framing refusal"
    (emit { exact with file := { file with column := { column with framing := {
      column.framing with maxPages := 0 } } } } input)
    (.groupReadback (.column 0 0 input.name (.framing .pageLimit)))

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let root := System.FilePath.mk directory
  let optional : Input := ⟨"clés", .optional, [[none, some .empty, some raw], [], [none, some long], []]⟩
  let output ← write root "optional" optional
  let _ ← write root "required" ⟨"raw", .required, [[some .empty, some raw], [],
    [some long, some .empty, some raw]]⟩
  let _ ← write root "schema-only" ⟨"empty", .optional, []⟩
  let _ ← write root "explicit-empty" ⟨"empty", .optional, [[]]⟩
  let singleSlots := [none, some Bytes.empty, some raw, none, some long]
  let single ← write root "singleton" ⟨"clés", .optional, [singleSlots]⟩
  let .ok predecessor := PlainByteArrayV1Writer.File.emit {} ⟨"clés", .optional singleSlots⟩
    | throw (IO.userError "existing singleton writer refused fixture")
  unless single.bytes == predecessor.bytes do throw (IO.userError "singleton wire changed")
  checkLimits optional output
  IO.println "Five native files, exact combined caps, singleton wire equality, and twelve typed refusals passed."
