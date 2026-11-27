module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

private def write (source path : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  match (convert {} ⟨input⟩).wire with
  | .ok output => IO.FS.writeBinFile path output.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private def matchesError (label : String) (ordinal offset : Nat) : GroupError → Bool
  | .dataOffset declared actual =>
    label == "data-offset" && actual == offset && declared == Int.ofNat (offset + 1)
  | .frame page header cause =>
    page == ordinal && header == offset && match label, cause with
      | "dictionary-crc", .checksum (.mismatch ..) | "data-crc", .checksum (.mismatch ..) => true
      | "dictionary-count", .dictionarySize 12 8 => true
      | "index", .indices (.outOfBounds 2) => true
      | "plain-tag", .dataEncoding 0 => true
      | "budget", .expandedBudget 15 16 => true
      | _, _ => false
  | _ => false

private def refuse (label source ordinal offset cap : String) : IO Unit := do
  let input ← IO.FS.readBinFile source
  let some page := ordinal.toNat? | throw (IO.userError "expected page ordinal")
  let some header := offset.toNat? | throw (IO.userError "expected header offset")
  let some bytes := cap.toNat? | throw (IO.userError "expected expansion budget")
  let limits : Limits := { snappy.ipc.totalRows := 0 }
  let limits := if label == "budget" then { limits with snappy.maxExpandedBytes := bytes } else limits
  let converted := convert limits ⟨input⟩
  let .error (.source (.groupFailure 1 cause)) := converted.wire
    | throw (IO.userError (reprStr (converted.wire.map (fun _ => ()))))
  if !matchesError label page header cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := converted.trace | throw (IO.userError "expected preceding trace")
  let .readError (.groupFailure 1 original) := trace.termination
    | throw (IO.userError "expected original indexed failure")
  if original ≠ cause then throw (IO.userError "wire and trace causes differ")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected LIST field")
  let first : List ListPage.Row :=
    [none, some [], some [some (-7), none, some (-7), some 2147483647],
      some [some (-2147483648), some 2147483647, some (-2147483648)]]
  if trace.batches.map (·.values field) ≠ [first] then
    throw (IO.userError "earlier checked batch changed")
  IO.println s!"{label}: group 1 page {page} @{header}; one retained batch and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] => write source path
  | ["refuse", label, source, ordinal, offset, cap] => refuse label source ordinal offset cap
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT PAGE OFFSET CAP")
