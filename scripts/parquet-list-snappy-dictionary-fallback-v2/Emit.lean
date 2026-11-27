module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1 (GroupError Limits)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2

private def first : List ListPage.Row :=
  [none, some [], some [none, some (-2147483648), some (-2147483648)], some [some (-2147483648)],
    some [some 0, some 1, some 2, some 3, some 4, some 5], some [some 2147483647, none],
    some (List.replicate 20 (some 6)), some ((List.replicate 16 [some 7, none]).flatten)]

private def matchesError (label : String) (ordinal offset : Nat) : GroupError → Bool
  | .frame page header cause =>
    page == ordinal && header == offset && match label, cause with
      | "reentry", .dictionaryReentry => true
      | "missing-prefix", .fallbackExpectedDictionary => true
      | "early-index-crc-before-reentry", .checksum (.mismatch ..) => true
      | "late-plain-crc", .v2 (.checksum (.mismatch ..)) => true
      | "wrong-plain-rows", .v2 (.v2RowCount 2 1) => true
      | _, _ => false
  | _ => false

private def refuse (label source ordinal offset : String) : IO Unit := do
  let some page := ordinal.toNat? | throw (IO.userError "expected page ordinal")
  let some header := offset.toNat? | throw (IO.userError "expected header offset")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { snappy.ipc.totalRows := 0 }
  let result := convert limits ⟨input⟩
  let .error (.source (.groupFailure 1 cause)) := result.wire
    | throw (IO.userError (reprStr (result.wire.map (fun _ => ()))))
  if !matchesError label page header cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := result.trace | throw (IO.userError "expected original source trace")
  let .readError (.groupFailure 1 original) := trace.termination
    | throw (IO.userError "expected indexed source failure")
  if original ≠ cause then throw (IO.userError "wire and trace causes differ")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected LIST field")
  if trace.batches.map (·.values field) ≠ [first] then
    throw (IO.userError "earlier checked batch changed")
  IO.println s!"{label}: group 1 page {page} @{header}; one retained batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, ordinal, offset] => refuse label source ordinal offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT PAGE OFFSET")
