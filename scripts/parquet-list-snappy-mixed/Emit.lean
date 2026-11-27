module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy (Limits Result FrameError)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed

private def write (source path : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  match (convert {} ⟨input⟩).wire with
  | .ok output => IO.FS.writeBinFile path output.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private def assertFailure (converted : Result) (index offset : Nat) (label : String)
    (accept : FrameError → Bool) : IO Unit := do
  let .error (.source (.groupFailure 1 (.frame page header cause))) := converted.wire
    | throw (IO.userError (reprStr (converted.wire.map (fun _ => ()))))
  if page ≠ index || header ≠ offset || !accept cause then
    throw (IO.userError (reprStr (page, header, cause)))
  let .ok ⟨schema, trace⟩ := converted.trace | throw (IO.userError "expected preceding trace")
  let .readError (.groupFailure 1 (.frame tracePage traceOffset traceCause)) := trace.termination
    | throw (IO.userError "expected original indexed failure")
  if (tracePage, traceOffset, traceCause) ≠ (page, header, cause) then
    throw (IO.userError "wire and trace causes differ")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected LIST field")
  let first : List ListPage.Row :=
    [none, some [], some (List.replicate 7 (some (-2147483648)) ++ [none]),
      some [some (-2147483648), some 2147483647]]
  if trace.batches.map (·.values field) ≠ [first] then
    throw (IO.userError "earlier checked batch changed")
  IO.println s!"{label}: group 1 page {page} @{header}; one retained batch and no IPC bytes"

private def refuse (source label ordinal offset : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let some page := ordinal.toNat? | throw (IO.userError "expected page ordinal")
  let some header := offset.toNat? | throw (IO.userError "expected header offset")
  let result := convert { ipc.totalRows := 0 } ⟨input⟩
  assertFailure result page header label fun cause =>
    match cause with
    | .v2Continuation => label == "starts-v2-mid-row" || label == "continues-after-v2" ||
        label == "continues-through-empty"
    | .checksum (.mismatch ..) => label == "v1-crc" || label == "v2-crc"
    | _ => false

private def budget (source offset limit : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let some header := offset.toNat? | throw (IO.userError "expected header offset")
  let some bytes := limit.toNat? | throw (IO.userError "expected byte budget")
  let result := convert { maxExpandedBytes := bytes, ipc.totalRows := 0 } ⟨input⟩
  assertFailure result 3 header "expanded byte limit" (· == .expandedBudget 164 165)

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] => write source path
  | ["refuse", label, source, index, offset] => refuse source label index offset
  | ["budget", source, offset, limit] => budget source offset limit
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT INDEX OFFSET | budget INPUT OFFSET LIMIT")
