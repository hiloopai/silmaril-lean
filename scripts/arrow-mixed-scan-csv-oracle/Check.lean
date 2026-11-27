module

import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Utf8
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def loadIpc (directory : System.FilePath) (name : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def loadCsv (directory : System.FilePath) (name : String) : IO Csv.Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".csv"))).map (·.data.toList)

private def fields (schema : Rows.Schema) : List Arrow.MixedFlat.Field :=
  List.ofFn fun i => (schema.kind i).1

private def cells (table : Rows.Table) : List (List (Option Cell)) :=
  table.rows.map fun row => List.ofFn row

private def expectError {α ε : Type} [DecidableEq ε] [Repr ε]
    (label : String) (result : Except ε α) (expected : ε) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")
  | .error cause =>
    unless cause == expected do throw (IO.userError s!"{label}: got {repr cause}, expected {repr expected}")

private def checkCase (directory : System.FilePath) (name : String) (width rowCount : Nat) :
    IO MixedIpc.Output := do
  let input ← loadIpc directory name
  let some native := Rows.readRows {} input | throw (IO.userError s!"{name}: IPC read failed")
  let output ← match MixedIpc.convert {} {} input with
    | .ok output => pure output
    | .error cause => throw (IO.userError s!"{name}: conversion failed: {repr cause}")
  unless native.schema.width == width && native.rowCount == rowCount &&
      fields output.schema == fields native.schema do
    throw (IO.userError s!"{name}: native row count or descriptors changed")
  let limits : MixedIpc.Limits := ⟨output.wire.length, rowCount⟩
  let .ok reopened := MixedIpc.decode limits output.schema output.wire
    | throw (IO.userError s!"{name}: Lean CSV re-import failed")
  let external ← loadCsv directory (name ++ ".python")
  let .ok independent := MixedIpc.decode ⟨external.length, rowCount⟩ output.schema external
    | throw (IO.userError s!"{name}: CPython CSV import failed")
  unless fields reopened.schema == fields native.schema && fields independent.schema == fields native.schema &&
      cells reopened == cells native && cells independent == cells native do
    throw (IO.userError s!"{name}: CSV altered ordered slots")
  IO.FS.writeBinFile (directory / (name ++ ".lean.csv")) ⟨output.wire.toArray⟩
  return output

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  let mixed ← checkCase directory "mixed" 4 4
  unless fields mixed.schema == [⟨"téxt", true, .view .utf8⟩, ⟨"amount", true, .primitive .int32⟩,
      ⟨"téxt", true, .primitive .utf8⟩, ⟨"required", false, .primitive .int32⟩] do
    throw (IO.userError "unexpected mixed Arrow field descriptors")
  let _ ← checkCase directory "schema-only" 4 0
  let _ ← checkCase directory "zero-width" 0 2

  let input ← loadIpc directory "mixed"
  let missingEos := input.slice 0 (input.len - 8)
  expectError "missing EOS" (MixedIpc.convert {} {} missingEos)
    (.input (.ipc (.message 3 missingEos.len (.envelope (.malformed .truncated)))))
  let opaqueIpc ← loadIpc directory "opaque"
  expectError "opaque BinaryView" (MixedIpc.convert {} {} opaqueIpc)
    (.output (.unsupportedField 0 ⟨"raw", true, .view .binary⟩))
  let invalidText ← loadIpc directory "invalid-text"
  expectError "CSV text alphabet" (MixedIpc.convert {} {} invalidText) (.output (.csv .unrepresentableWire))

  let wrongHeader ← loadCsv directory "wrong-header"
  let badInteger ← loadCsv directory "bad-integer"
  let requiredNull ← loadCsv directory "required-null"
  expectError "header order" (MixedIpc.decode {} mixed.schema wrongHeader) (.csv .headerMismatch)
  expectError "noncanonical integer" (MixedIpc.decode {} mixed.schema badInteger) (.csv (.parseCell 1))
  expectError "required null" (MixedIpc.decode {} mixed.schema requiredNull) (.requiredNull 1 3)
  let fewerBytes := mixed.wire.length - 1
  expectError "input byte limit" (MixedIpc.decode { maxBytes := fewerBytes } mixed.schema mixed.wire)
    (.byteLimit fewerBytes mixed.wire.length)
  expectError "output byte limit" (MixedIpc.convert {} { maxBytes := fewerBytes } input)
    (.output (.byteLimit fewerBytes mixed.wire.length))
  expectError "input row limit" (MixedIpc.decode { maxRows := 3 } mixed.schema mixed.wire) (.rowLimit 3)
  expectError "output row limit" (MixedIpc.convert {} { maxRows := 3 } input) (.output (.rowLimit 3))
  IO.println "Three IPC/CSV/Scan round trips, independent CSV imports, and ten typed refusals checked."
