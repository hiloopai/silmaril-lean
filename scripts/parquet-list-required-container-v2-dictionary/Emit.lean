module

import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Defs
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def matchesError (label : String) (ordinal offset : Nat) : GroupError → Bool
  | .frame page header cause =>
    page == ordinal && header == offset && match label, cause with
      | "dictionary-crc", .checksum (.mismatch ..)
      | "raw-index-crc", .v2 (.checksum (.mismatch ..))
      | "compressed-index-crc", .v2 (.checksum (.mismatch ..))
      | "level-crc", .v2 (.checksum (.mismatch ..))
      | "index-out-of-bounds", .indices (.outOfBounds 3)
      | "no-index-width", .indices .missingBitWidth
      | "late-continuation", .v2 .v2Continuation
      | "page-rows", .v2 (.v2RowCount 0 1)
      | "page-nulls", .v2 (.v2NullCount 0 1)
      | "plain-fallback", .dataEncoding 0 => true
      | _, _ => false
  | _ => false

private def refuse (label source pageText offsetText : String) : IO Unit := do
  let some page := pageText.toNat? | throw (IO.userError "expected page ordinal")
  let some offset := offsetText.toNat? | throw (IO.userError "expected header offset")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { snappy.ipc.totalRows := 0 }
  let output := convert limits ⟨input⟩
  let .error (.source (.groupFailure actual cause)) := output.wire
    | throw (IO.userError (reprStr (output.wire.map (fun _ => ()))))
  if actual ≠ 1 || !matchesError label page offset cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := output.trace | throw (IO.userError "expected original source trace")
  let .readError reported := trace.termination | throw (IO.userError "expected indexed read error")
  if reported ≠ .groupFailure 1 cause then throw (IO.userError "source error changed")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected one LIST field")
  if trace.batches.map (·.values field) ≠ [first] then
    throw (IO.userError "earlier batches changed")
  IO.println s!"{label}: group 1 frame {page} @{offset}; retained one original batch and no IPC bytes"


public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, page, offset] => refuse label source page offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT PAGE OFFSET")
