module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def ipcInput (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ "-input.arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private abbrev convert := Leaf.Events.ToIpc.Seconds.convert
private abbrev ConversionError := Leaf.Events.ToIpc.Seconds.Error

private def expectError (label : String) (expected : ConversionError) (result : Except ConversionError KBytes) : IO Unit := do
  match result with
  | .error actual =>
    unless actual == expected do throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
  let directory : System.FilePath := folder
  for name in ["utc_v1", "local_v2"] do
    let source ← input directory name
    let wire ← require (convert {} {} source)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

  for name in ["utc_optional", "local_required", "all_empty", "schema_only"] do
    let original ← ipcInput directory name
    let middle ← require (FromIpc.Seconds.convert {} {} original)
    let output ← require (convert {} {} middle)
    let image := "image_" ++ name
    IO.FS.writeBinFile (directory / (image ++ ".parquet")) middle.data
    IO.FS.writeBinFile (directory / (image ++ ".arrows")) output.toByteArray

  let source ← input directory "utc_v1"
  let old ← require (Leaf.Events.ToIpc.convert {} {} source 1)
  let decoded ← require (Arrow.TimestampStream.read {} old)
  unless decoded.binding.metadata.unit = .millisecond do
    throw (IO.userError "default TIMESTAMP stream changed millis output")

  let cases : List (String × ConversionError) :=
    [("offgrid_negative", .nonintegral 2 2 (-1001)),
     ("offgrid_positive", .nonintegral 1 2 1001),
     ("late_bad_source", .source (.source (.groupFailure 2 (.page 0 (.scalar (.unsupportedEncoding 5)))))),
     ("wrong_unit", .expectedMillis),
     ("multi_field", .fieldCount 2),
     ("page_less", .source (.source (.openFailure (.snapshot (.invalidMetadata .pageInterval)))))]
  for (name, expected) in cases do
    expectError name expected (convert {} {ipc.batches := 0} (← input directory name))
  expectError "output group cap" (.writer (.writer (.limit .batches))) (convert {} {ipc.batches := 0} source)
  expectError "original group cap" (.source (.groupLimit 1 2)) (convert {maxGroups := 1} {} source)
  IO.println "Eight typed refusals and unchanged default millis readback passed"
