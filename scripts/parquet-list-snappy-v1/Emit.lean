module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy

private def write (source path : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  match (convert {} ⟨input⟩).wire with
  | .ok output => IO.FS.writeBinFile path output.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private def refuse (label source offset cap : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let some pageOffset := offset.toNat? | throw (IO.userError "expected a page offset")
  let some budget := cap.toNat? | throw (IO.userError "expected an expansion budget")
  let limits : Limits := { ipc.totalRows := 0 }
  let limits := if label = "budget" then { limits with maxExpandedBytes := budget } else limits
  let converted := convert limits ⟨input⟩
  let .error (.source (.groupFailure 1 (.frame ordinal actual cause))) := converted.wire
    | throw (IO.userError (reprStr (converted.wire.map (fun _ => ()))))
  if actual ≠ pageOffset then throw (IO.userError "incorrect original page offset")
  let expected := match label, ordinal, cause with
    | "crc", 3, .checksum (.mismatch ..) => true
    | "payload", 3, .payload (.malformed .snappy) => true
    | "leading", 0, .page .continuationWithoutList => true
    | "budget", 3, .expandedBudget 16 17 => true
    | _, _, _ => false
  if !expected then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := converted.trace | throw (IO.userError "expected the earlier trace")
  let .readError (.groupFailure 1 (.frame tracePage traceOffset traceCause)) := trace.termination
    | throw (IO.userError "expected the same indexed trace error")
  if (tracePage, traceOffset, traceCause) ≠ (ordinal, actual, cause) then
    throw (IO.userError "trace error differed from wire error")
  let some column := (List.finRange schema.width).head? | throw (IO.userError "expected a LIST field")
  let first : List ListPage.Row :=
    [none, some [], some (List.replicate 7 (some (-2147483648)) ++ [none]), some [some 2147483647, none]]
  if trace.batches.map (·.values column) ≠ [first] then
    throw (IO.userError "earlier ordered batch changed")
  IO.println s!"{label}: group 1 page {ordinal} @{actual}; one retained batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] => write source path
  | ["refuse", label, source, offset, cap] => refuse label source offset cap
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT OFFSET CAP")
