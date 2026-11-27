module

import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema readFrame)
open Silmaril.Formats.Arrow.RecursiveSchema.Writer (Error emit plan checkSize)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect {α : Type} (label : String) (wanted : Error) (result : Except Error α) : IO Unit := do
  match result with
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"{label}: expected {repr wanted}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def schemaFrom (path : System.FilePath) : IO Schema := do
  let data ← IO.FS.readBinFile path
  let bytes := KBytes.ofChunks 1 data.size (data.data.toList.map UInt8.toNat)
  let (schema, _) ← require (readFrame {} bytes)
  return schema

private def emitCase (dir : System.FilePath) (name : String) : IO Unit := do
  let schema ← schemaFrom (dir / (name ++ ".arrow"))
  let bytes ← require (emit { ipc.batches := 0, ipc.rows := 0, ipc.bodyBytes := 0 } schema)
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) bytes.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let dir : System.FilePath := folder
  for name in ["four_level", "empty_name", "zero_width", "repeated_children", "absent_name"] do
    emitCase dir name

  let schema ← schemaFrom (dir / "four_level.arrow")
  let bound ← require (plan {} schema)
  let _ ← require (emit { depth := 4, ipc.fields := bound.fields, ipc.metadataBytes := bound.bytes } schema)
  let _ ← require (emit { depth := 0, ipc.fields := 0, ipc.metadataBytes := 72 } ⟨[]⟩)

  let leaf : Field := .node (some "value") true .int32 []
  expect "List needs a child" (.arity 0 .list 0) (emit {} ⟨[.node none true .list []]⟩)
  expect "List admits one child" (.arity 0 .list 2) (emit {} ⟨[.node none true .list [leaf, leaf]]⟩)
  expect "Int is a leaf" (.arity 1 .int64 1)
    (emit {} ⟨[.node none true .struct [.node none true .int64 [leaf]]]⟩)
  expect "deep child cap" (.depth 3) (emit { depth := 3 } schema)
  expect "global occurrence cap" (.fields 10) (emit { ipc.fields := 10 } schema)
  expect "metadata cap" (.metadataLimit bound.bytes) (emit { ipc.metadataBytes := bound.bytes - 1 } schema)
  expect "root byte cap" (.metadataLimit 72) (emit { ipc.metadataBytes := 71 } ⟨[]⟩)
  expect "signed framing cap" (.offsetLimit (2^31)) (checkSize { ipc.metadataBytes := 2^31 } (2^31))
  IO.println "Emitted five schema-only streams and checked eight typed refusals"
