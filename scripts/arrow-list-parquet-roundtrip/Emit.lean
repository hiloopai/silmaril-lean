module

import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
meta import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs

open Silmaril Silmaril.Formats.Parquet
open ListFile.Writer.FromIpc

private def readBytes (path : String) : IO KBytes := do
  let source ← IO.FS.readBinFile path
  pure (.leaf source.size (KBytes.leVal source.data.toList))

private def write (source parquet ipc : String) : IO Unit := do
  let input ← readBytes source
  let limits : Limits := {}
  let written ← match convert limits input with
    | .ok result => pure result
    | .error cause => throw (IO.userError (reprStr cause))
  let returned := ListFile.Multi.ToIpc.convert ⟨limits.parquet.readback, {}⟩ written.bytes
  let .ok bytes := returned.wire | throw (IO.userError "native return conversion failed")
  IO.FS.writeBinFile parquet written.bytes.data
  IO.FS.writeBinFile ipc bytes.toByteArray

private def refuse (source mode : String) : IO Unit := do
  let input ← readBytes source
  let result := convert { parquet.maxGroups := 0 } input
  match mode, result with
  | "child", .error (.childName "item") => IO.println "original child name item refused; no Parquet carrier"
  | "late", .error (.source (.batch 2 (.body (.malformed .truncated)))) =>
    IO.println "late IPC batch 2: truncated body; original source error, no Parquet carrier"
  | "late-child", .error (.source (.batch 1 (.body (.malformed .truncated)))) =>
    IO.println "late IPC batch 1: truncated body before child-name or writer admission; no Parquet carrier"
  | _, .error cause => throw (IO.userError (reprStr cause))
  | _, .ok _ => throw (IO.userError "unexpected Parquet publication")

public def main (args : List String) : IO Unit := do
  match args with
  | ["write", source, parquet, ipc] => write source parquet ipc
  | ["refuse", mode, source] => refuse source mode
  | _ => throw (IO.userError "usage: Emit.lean write SOURCE PARQUET IPC | refuse MODE SOURCE")
