module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private def input (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def expectError (label : String) (expected : FromIpc.Seconds.Error)
    (result : Except FromIpc.Seconds.Error Bytes) : IO Unit := do
  match result with
  | .error actual =>
    unless actual == expected do throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
  let directory : System.FilePath := folder
  let convert := FromIpc.Seconds.convert {}
  for name in ["utc_optional", "local_required", "all_empty", "schema_only"] do
    let wire ← input directory name
    match convert {} wire with
    | .ok file => IO.FS.writeBinFile (directory / (name ++ ".parquet")) file.data
    | .error cause => throw (IO.userError s!"{name}: {repr cause}")

  let optional ← input directory "utc_optional"
  expectError "source cap" .inputByteLimit (convert {maxInputBytes := 0} optional)
  expectError "empty batches count toward the sink group cap" (.sink .groupLimit)
    (convert {maxGroups := 3} optional)
  match FromIpc.convert {} {} optional with
  | .error .seconds => pure ()
  | _ => throw (IO.userError "strict writer changed its seconds admission")

  let sinkRejected : FromIpc.Limits := {maxGroups := 0}
  let cases : List (String × FromIpc.Seconds.Error) :=
    [("positive_overflow", .rescale 2 2 .outOfRange),
     ("negative_overflow", .rescale 1 1 .outOfRange),
     ("wrong_unit", .expectedSeconds),
     ("named_timezone", .metadata (.timezone "Asia/Kathmandu")),
     ("offset_timezone", .metadata (.timezone "+00:00")),
     ("present_empty_timezone", .metadata (.timezone "")),
     ("truncated_body", .source (.batch 3 (.body (.malformed .truncated)))),
     ("missing_eos", .source (.batch 4 (.envelope (.malformed .truncated)))),
     ("trailing_bytes", .source (.batch 4 .trailingBytes)),
     ("timezone_missing_eos", .source (.batch 2 (.envelope (.malformed .truncated))))]
  for (name, expected) in cases do
    let wire ← input directory name
    expectError name expected (convert sinkRejected wire)
  IO.println "Twelve typed refusals and the unchanged strict seconds refusal passed"
