module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray.Utf8

private def load (directory : System.FilePath) (name : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def checkRoundTrip (directory : System.FilePath) (name : String) (counts : List Nat) : IO Unit := do
  let input ← load directory name
  let .ok original := FromIpc.readSource {} {} input |
    throw (IO.userError s!"source rejected {name}")
  let .ok parquet := FromIpc.convert {} {} {} input |
    throw (IO.userError s!"conversion rejected {name}")
  let .ok verified := openFile {} parquet original.name original.layout |
    throw (IO.userError "checked annotated footer rejected")
  unless verified.annotation == .logicalAndConverted &&
      verified.physical.snapshot.groupCount == counts.length do
    throw (IO.userError "wrong annotation or original group count")
  let .ok restoredWire := convert {} {} parquet original.name original.layout |
    throw (IO.userError "checked forward STRING export rejected")
  let .ok restored := FromIpc.readSource {} {} restoredWire |
    throw (IO.userError "failed UTF-8 IPC readback")
  unless original.name == restored.name && original.nullable == restored.nullable &&
      original.batches == restored.batches && restored.batches.map List.length == counts do
    throw (IO.userError "wrong descriptor, octets, null positions or group boundaries")
  IO.FS.writeBinFile (directory / (name ++ ".parquet")) parquet.data

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  checkRoundTrip directory "optional" [5, 0, 4]
  checkRoundTrip directory "required" [2, 0, 2]
  checkRoundTrip directory "schema-only" []
  let .error (.nullInRequired 0) := FromIpc.emit {} ⟨"text", false, [[none]]⟩ |
    throw (IO.userError "the native writer must reject nulls for a required leaf")
  let binary ← load directory "binary"
  let .error .expectedUtf8View := FromIpc.convert {} {} {} binary |
    throw (IO.userError "BinaryView must retain its declared binary kind")
  let optional ← load directory "optional"
  let .error (.groupLimit 2 3) := FromIpc.convert {} {} { maxGroups := 2 } optional |
    throw (IO.userError "empty group must count toward the writer group cap")
  let .error (.rowLimit 8 9) := FromIpc.convert {} {} { file.maxFileRows := 8 } optional |
    throw (IO.userError "aggregate row limit was not applied")
  let .error .fileLimit := FromIpc.convert {} {} { file.maxFileBytes := 12 } optional |
    throw (IO.userError "file extent was not bounded")
  let .error (.footer .byteLimit) :=
    FromIpc.convert {} {} { file.snapshot.footer.maxFooterBytes := 0 } optional |
    throw (IO.userError "footer extent was not bounded")
  let .error (.page 0 (.plain .valueByteLimit)) :=
    FromIpc.convert {} {} { file.maxValueBytes := 1 } optional |
    throw (IO.userError "scalar limit must measure UTF-8 bytes")
  let truncated ← load directory "truncated"
  let .error (.source (.batch 3 (.envelope (.malformed .truncated)))) :=
    FromIpc.convert {} {} { maxGroups := 0 } truncated |
    throw (IO.userError "missing EOS must take precedence over the writer cap")
  let badText ← load directory "bad-text"
  let .error (.source (.batch 2 (.decode (.column .invalidUtf8)))) :=
    FromIpc.convert {} {} { maxGroups := 0 } badText |
    throw (IO.userError "wrong original error for late invalid Utf8View")
  IO.println "Lean matched checked source and sink text, typed refusals and exact original late IPC errors"
