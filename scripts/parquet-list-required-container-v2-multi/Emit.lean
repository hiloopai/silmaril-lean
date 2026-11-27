module

import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer (SourceError)
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def expected (label : String) (offset : Nat) : Option GroupError :=
  match label with
  | "page-rows" => some (.frame 2 offset (.data (.pageRows 0 1)))
  | "page-nulls" => some (.frame 2 offset (.data (.pageNulls 1 0)))
  | "page-slots" => some (.frame 2 offset (.slotBudget 1 2))
  | "group-rows" => some (.rowCount 3 4)
  | "group-slots" => some (.missingSlots 1)
  | "short-plain" => some (.frame 2 offset (.data (.page (.plain .truncated))))
  | "long-plain" => some (.frame 2 offset (.data (.page (.plain .trailingBytes))))
  | "continue-empty" => some (.frame 0 offset (.data (.page .continuationWithoutList)))
  | "first-of-two" => some (.frame 1 offset .rowContinuation)
  | "late-continuation" => some (.frame 2 offset .rowContinuation)
  | _ => none

private def refuse (label source offsetText : String) : IO Unit := do
  let some offset := offsetText.toNat? | throw (IO.userError "expected header offset")
  let some failure := expected label offset | throw (IO.userError "unknown refusal")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { ipc.totalRows := 0 }
  let output := convert limits ⟨input⟩
  let cause : SourceError GroupError := .groupFailure 1 failure
  let .error (.source failed) := output.wire
    | throw (IO.userError (reprStr (output.wire.map (fun _ => ()))))
  if cause ≠ failed then throw (IO.userError (reprStr failed))
  let .ok ⟨schema, trace⟩ := output.trace | throw (IO.userError "expected original source trace")
  let .readError reported := trace.termination | throw (IO.userError "expected indexed read error")
  if reported ≠ cause then throw (IO.userError "source error changed")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected one LIST field")
  if trace.batches.map (·.values field) ≠ [first] then throw (IO.userError "earlier batch changed")
  let location := match failure with
    | .frame page start _ => s!"page {page} @{start}"
    | _ => "footer totals"
  IO.println s!"{label}: group 1 {location}; one original batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, offset] => refuse label source offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT OFFSET")
