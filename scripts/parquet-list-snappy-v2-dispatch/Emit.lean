module

import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1 (Limits)

private def matchesError (label : String) (page offset : Nat) : GroupError → Bool
  | .plain (.frame ordinal header (.checksum (.mismatch ..))) =>
    ordinal == page && header == offset && label == "plain-crc"
  | .dictionary (.frame ordinal header (.checksum (.mismatch ..))) =>
    ordinal == page && header == offset && label == "dictionary-crc"
  | .fallback (.frame ordinal header cause) =>
    ordinal == page && header == offset && match label, cause with
      | "fallback-plain-crc", .v2 (.checksum (.mismatch ..)) => true
      | "early-index-crc-before-reentry", .checksum (.mismatch ..) => true
      | "reentry", .dictionaryReentry => true
      | _, _ => false
  | _ => false

private def refuse (label source baseline groupText pageText offsetText : String) : IO Unit := do
  let some group := groupText.toNat? | throw (IO.userError "expected group ordinal")
  let some page := pageText.toNat? | throw (IO.userError "expected page ordinal")
  let some offset := offsetText.toNat? | throw (IO.userError "expected header offset")
  let input ← IO.FS.readBinFile source
  let limits : Limits := { snappy.ipc.totalRows := 0 }
  let result := convert limits ⟨input⟩
  let .error (.source (.groupFailure index cause)) := result.wire
    | throw (IO.userError (reprStr (result.wire.map (fun _ => ()))))
  if index ≠ group || !matchesError label page offset cause then throw (IO.userError (reprStr cause))
  let .ok ⟨schema, trace⟩ := result.trace | throw (IO.userError "expected original source trace")
  let .readError (.groupFailure priorIndex original) := trace.termination
    | throw (IO.userError "expected indexed source failure")
  if priorIndex ≠ group || original ≠ cause then throw (IO.userError "wire and trace causes differ")
  let some field := (List.finRange schema.width).head? | throw (IO.userError "expected LIST field")
  let originalInput ← IO.FS.readBinFile baseline
  let .ok ⟨originalSchema, originalTrace⟩ := (convert {} ⟨originalInput⟩).trace
    | throw (IO.userError "expected complete baseline source trace")
  let .eos := originalTrace.termination | throw (IO.userError "expected baseline EOS")
  let some originalField := (List.finRange originalSchema.width).head?
    | throw (IO.userError "expected baseline LIST field")
  let retained := trace.batches.map (·.values field)
  let expected := (originalTrace.batches.map (·.values originalField)).take group
  if retained ≠ expected then throw (IO.userError "earlier batches changed")
  IO.println s!"{label}: group {group} page {page} @{offset}; retained batch lengths {retained.map List.length} and no IPC bytes"

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, path] =>
    let input ← IO.FS.readBinFile source
    match (convert {} ⟨input⟩).wire with
    | .ok output => IO.FS.writeBinFile path output.toByteArray
    | .error cause => throw (IO.userError (reprStr cause))
  | ["refuse", label, source, baseline, group, page, offset] => refuse label source baseline group page offset
  | _ => throw (IO.userError "usage: Emit.lean write INPUT OUTPUT | refuse KIND INPUT BASELINE GROUP PAGE OFFSET")
