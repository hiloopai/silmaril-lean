module

import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def matchesError (label : String) (offset : Nat) : GroupError → Bool
  | .framing (.framing (.header .invalidV2Lengths)) => label == "raw-flag"
  | .frame page header cause =>
    page == 0 && header == offset && match label, cause with
      | "raw-crc", .snappy (.checksum (.mismatch ..))
      | "level-crc", .snappy (.checksum (.mismatch ..))
      | "snappy-crc", .snappy (.checksum (.mismatch ..))
      | "header-rows", .snappy (.v2RowCount 3 4)
      | "header-nulls", .snappy (.v2NullCount 3 4)
      | "header-slots", .slots 109 110
      | "bad-snappy", .snappy (.payload (.malformed .snappy)) => true
      | _, _ => false
  | _ => false

private def refuse (label source groupText offsetText : String) : IO Unit := do
  let some group := groupText.toNat? | throw (IO.userError "expected group ordinal")
  let some offset := offsetText.toNat? | throw (IO.userError "expected header offset")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { ipc.totalRows := 0 }
  let output := convert limits ⟨input⟩
  let .error (.source (.groupFailure actual cause)) := output.wire
    | throw (IO.userError (reprStr (output.wire.map (fun _ => ()))))
  if actual ≠ group || !matchesError label offset cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := output.trace | throw (IO.userError "expected original source trace")
  let .readError reported := trace.termination | throw (IO.userError "expected indexed read error")
  if reported ≠ .groupFailure group cause then throw (IO.userError "source error changed")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected one LIST field")
  if trace.batches.map (·.values field) ≠ [first].take group then
    throw (IO.userError "earlier batches changed")
  let location := if label == "raw-flag" then "framing" else s!"page 0 @{offset}"
  let batches := if trace.batches.length == 1 then "batch" else "batches"
  IO.println s!"{label}: group {group} {location}; retained {trace.batches.length} original {batches} and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, group, offset] => refuse label source group offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT GROUP OFFSET")
