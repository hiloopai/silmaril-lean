module

import Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Csv.Typed.Utf8

private def loadCsv (root : System.FilePath) (name : String) : IO Csv.Bytes :=
  (IO.FS.readBinFile (root / (name ++ ".csv"))).map (·.data.toList)

private def expectError (label : String) (result : Except FromCsv.Error PlainByteArrayV1Writer.File.Encoded)
    (expected : FromCsv.Error) : IO Unit := do
  let .error actual := result | throw (IO.userError s!"{label}: unexpected file")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def checkReturned (stem : String) (field : OpaqueIpc.Descriptor) (limits : File.Limits)
    (output : PlainByteArrayV1Writer.File.Encoded) (slots : List (Option Bytes)) : IO Unit := do
  let selection := FromCsv.layout field.nullable
  let .ok checked := File.openFile limits output.bytes field.name selection
    | throw (IO.userError s!"{stem}: selected reader failed")
  let .ok actual := checked.readGroup limits 0 | throw (IO.userError s!"{stem}: group zero failed")
  let .error (.groupIndex 1) := checked.readGroup limits 1
    | throw (IO.userError s!"{stem}: group one was admitted")
  let values := slots.map (Option.map Bytes.toList)
  let some prepared := FromCsv.prepare field values | throw (IO.userError "expected preparation failed")
  let .ok (footer, metadata) := Footer.readFooter limits.snapshot.footer output.bytes
    | throw (IO.userError s!"{stem}: native footer did not read")
  unless checked.snapshot.groupCount == 1 && checked.binding.columnOrdinal == 0 &&
      checked.binding.leaf.name == field.name && actual == slots &&
      footer == output.footer && metadata == PlainByteArrayV1Writer.File.metadata prepared output do
    throw (IO.userError s!"{stem}: descriptor, footer, or slot order differs")

private def checkErrors (root : System.FilePath) (field : OpaqueIpc.Descriptor)
    (wire : Csv.Bytes) (output : PlainByteArrayV1Writer.File.Encoded) : IO Unit := do
  let fixtures := root / "input"
  let badWriter : File.Limits := { maxFileBytes := 4 }
  let malformed ← loadCsv fixtures "malformed"
  expectError "layout before CSV and writer limits"
    (FromCsv.convert { maxBytes := 0 } badWriter { field with layout := .binary } malformed)
    (.expectedBinaryView .binary)
  expectError "invalid header" (FromCsv.convert {} badWriter field (← loadCsv fixtures "bad-header"))
    (.csv (.csv .headerMismatch))
  for name in ["bad-hex", "odd-hex"] do
    expectError name (FromCsv.convert {} badWriter field (← loadCsv fixtures name))
      (.csv (.csv (.parseCell 0)))
  expectError "required null" (FromCsv.convert {} badWriter ⟨"key", false, .binaryView⟩
    (← loadCsv fixtures "required-null")) (.csv (.requiredNull 1))
  expectError "malformed CSV octets" (FromCsv.convert {} badWriter field malformed) (.csv (.csv .malformedWire))
  let smaller := wire.length - 1
  expectError "CSV byte limit" (FromCsv.convert { maxBytes := smaller } badWriter field wire)
    (.csv (.byteLimit smaller wire.length))
  expectError "CSV row limit" (FromCsv.convert { maxRows := 7 } badWriter field wire)
    (.csv (.rowLimit 7))
  expectError "writer row limit"
    (FromCsv.convert {} { maxFileRows := 7, maxFileBytes := 4 } field wire) (.writer (.rowLimit 7 8))
  expectError "writer minimum file limit" (FromCsv.convert {} badWriter field wire) (.writer .fileLimit)
  expectError "writer value limit" (FromCsv.convert {} { maxValueBytes := 12 } field wire)
    (.writer (.page (.plain .valueByteLimit)))
  expectError "writer footer limit"
    (FromCsv.convert {} { maxFileBytes := output.bytes.length - 1 } field wire) (.writer (.footer .byteLimit))

private def check (root : System.FilePath) (file stem name : String)
    (selection : FlatColumn.Layout) (counts : List Nat) : IO Unit := do
  let input : Bytes := ⟨← IO.FS.readBinFile (root / "forward" / "source" / file)⟩
  let .ok source := ToIpc.readSource {} input name selection
    | throw (IO.userError s!"{stem}: original source failed")
  let count := counts.sum
  let .ok csv := ToCsv.exportCsv {} {} { maxRows := count + 1 } input name selection
    | throw (IO.userError s!"{stem}: original Parquet CSV export failed")
  let recorded ← loadCsv (root / "forward") stem
  unless source.groups.map List.length == counts && csv.field == ToCsv.descriptor name selection &&
      csv.wire == recorded do
    throw (IO.userError s!"{stem}: original selected descriptor, groups or CSV changed")
  let limits : File.Limits := { maxFileRows := count }
  let .ok output := FromCsv.convert ⟨csv.wire.length, count⟩ limits csv.field csv.wire
    | throw (IO.userError s!"{stem}: Lean CSV to Parquet failed")
  checkReturned stem csv.field limits output source.groups.flatten
  let independent ← loadCsv (root / "forward" / "source") stem
  let .ok fromPython := FromCsv.convert ⟨independent.length, count⟩ limits csv.field independent
    | throw (IO.userError s!"{stem}: independent CSV to Parquet failed")
  checkReturned (stem ++ " CPython CSV") csv.field limits fromPython source.groups.flatten
  if stem == "optional-v2" then checkErrors root csv.field csv.wire output
  IO.FS.writeBinFile (root / (stem ++ ".parquet")) output.bytes.data

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected fixture directory")
  let root := System.FilePath.mk directory
  check root "selected.parquet" "optional-v2" "blob" .optional [4, 4]
  check root "plain-byte-array-v1.parquet" "required-v1" "key" .required [12, 12, 12]
  check root "schema-only.parquet" "schema-only" "blob" .optional []
  check root "framed-zero-row-group.parquet" "empty-batch" "blob" .optional [0]
  let field : OpaqueIpc.Descriptor := ⟨"empty", false, .binaryView⟩
  let csv ← loadCsv (root / "input") "required-empty"
  let .ok output := FromCsv.convert ⟨csv.length, 0⟩ { maxFileRows := 0 } field csv
    | throw (IO.userError "header-only required CSV failed")
  checkReturned "required-empty" field { maxFileRows := 0 } output []
  IO.FS.writeBinFile (root / "required-empty.parquet") output.bytes.data
  IO.println "Four original Parquet-to-CSV-to-Parquet comparisons, five independent CSV imports and twelve typed refusals."
