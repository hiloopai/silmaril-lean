module

import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def refuse (label source offsetText : String) : IO Unit := do
  let some offset := offsetText.toNat? | throw (IO.userError "expected header offset")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { ipc.totalRows := 0 }
  let output := convert limits ⟨input⟩
  let expected := if label == "leading-continuation" then ListPage.Error.continuationWithoutList else .levelPair
  let cause : SourceError := .groupFailure 1 (.frame 0 offset (.page expected))
  let .error (.source failed) := output.wire
    | throw (IO.userError (reprStr (output.wire.map (fun _ => ()))))
  if cause ≠ failed then throw (IO.userError (reprStr failed))
  let .ok ⟨schema, trace⟩ := output.trace | throw (IO.userError "expected original source trace")
  let .readError reported := trace.termination | throw (IO.userError "expected indexed read error")
  if reported ≠ cause then throw (IO.userError "source error changed")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected one LIST field")
  if trace.batches.map (·.values field) ≠ [first] then throw (IO.userError "earlier batch changed")
  IO.println s!"{label}: group 1 page 0 @{offset}; one original batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, offset] => refuse label source offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT OFFSET")
