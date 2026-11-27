module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy

private def write (source path : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  match (convertV2 {} ⟨input⟩).wire with
  | .ok output => IO.FS.writeBinFile path output.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private def matchesControl (offset : Nat) (label : String) : GroupError → Bool
  | .framing (.framing (.header .invalidV2Lengths)) => label == "geometry"
  | .rowCount 5 4 => label == "group-rows"
  | .frame 3 actual cause =>
    actual == offset && match label, cause with
      | "crc-level", .checksum (.mismatch ..) | "crc-values", .checksum (.mismatch ..) => true
      | "level-split", .page (.repetition .trailingBytes) => true
      | "continued", .v2Continuation => true
      | "page-rows", .v2RowCount 2 1 => true
      | "page-nulls", .v2NullCount 0 1 => true
      | "page-slots", .slotBudget 40 41 => true
      | "budget", .expandedBudget 164 165 => true
      | _, _ => false
  | _ => false

private def refuse (label source offset : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let some pageOffset := offset.toNat? | throw (IO.userError "expected a page offset")
  let limits : Limits := { ipc.totalRows := 0 }
  let limits := if label = "budget" then { limits with maxExpandedBytes := 205 } else limits
  let converted := convertV2 limits ⟨input⟩
  let .error (.source (.groupFailure 1 cause)) := converted.wire
    | throw (IO.userError (reprStr (converted.wire.map (fun _ => ()))))
  if !matchesControl pageOffset label cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := converted.trace | throw (IO.userError "expected preceding trace")
  let .readError (.groupFailure 1 traceCause) := trace.termination
    | throw (IO.userError "expected original indexed trace failure")
  if traceCause ≠ cause then throw (IO.userError "wire and trace causes differ")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected LIST field")
  let first : List ListPage.Row :=
    [none, some [], some [some (-7), none], some [some (-2147483648), some 2147483647]]
  if trace.batches.map (·.values field) ≠ [first] then
    throw (IO.userError "earlier checked batch changed")
  IO.println s!"{label}: group 1, {reprStr cause}; one retained batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] => write source path
  | ["refuse", label, source, offset] => refuse label source offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT OFFSET")
