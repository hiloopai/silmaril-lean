module

import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi
open Silmaril.Formats.Parquet.ListFile.Multi.ToIpc

private def write (source path : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  match (convert {} ⟨input⟩).wire with
  | .ok output => IO.FS.writeBinFile path output.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private def refuseLate (source : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let converted := convert { ipc.totalRows := 0 } ⟨input⟩
  let .error (.source (.groupFailure 1 (.frame 0 48 (.page .continuationWithoutList)))) := converted.wire
    | throw (IO.userError "expected the original indexed continuation refusal")
  let .ok ⟨schema, trace⟩ := converted.trace | throw (IO.userError "expected the earlier trace")
  let .readError (.groupFailure 1 (.frame 0 48 (.page .continuationWithoutList))) := trace.termination
    | throw (IO.userError "expected the original trace error")
  let some column := (List.finRange schema.width).head? | throw (IO.userError "expected the LIST field")
  let first : List ListPage.Row :=
    [none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]]
  if trace.batches.map (·.values column) ≠ [first] then
    throw (IO.userError "the earlier ordered batch was altered")
  IO.println "late group 1, frame 0 @48: continuationWithoutList; one retained batch and no IPC bytes"

private def refuseUnframed (source : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let result := convert {} ⟨input⟩
  let .error (.source (.openFailure (.snapshot (.invalidMetadata .pageInterval)))) := result.wire
    | throw (IO.userError "expected the original empty-chunk refusal")
  IO.println "unframed empty chunk: pageInterval; no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] => write source path
  | ["late", source] => refuseLate source
  | ["unframed", source] => refuseUnframed source
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | late INPUT | unframed INPUT")
