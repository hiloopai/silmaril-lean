module

import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream (Trace Completed read)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect (wanted : Error) (result : Except Error KBytes) : IO Unit := do
  match result with
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"accepted invalid input expecting {repr wanted}")

private def openFixture (dir : System.FilePath) (name : String) : IO Trace := do
  let data ← IO.FS.readBinFile (dir / (name ++ ".arrow"))
  let carrier := KBytes.ofChunks 1 data.size (data.data.toList.map UInt8.toNat)
  require (read {} carrier)

private def reemit (dir : System.FilePath) (name : String) : IO Unit := do
  let source ← openFixture dir name
  let batches := source.batches.map Completed.observed
  let wire ← require (emit { schema.ipc.batches := batches.length } source.schema batches)
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) wire.toByteArray

private def controls (dir : System.FilePath) : IO Unit := do
  let original ← openFixture dir "four_level"
  let [first, second] := original.batches.map Completed.observed |
    throw (IO.userError "expected a populated batch followed by an empty batch")
  let late := { second with rowCount := 1 }
  let later := { second with rowCount := 2 }
  expect (.batch 1 (.rowCount 1 0)) (emit {} original.schema [first, late, later])
  expect (.batch 2 (.rowCount 2 0)) (emit {} original.schema [first, second, later])
  expect (.batchLimit 3 2) (emit { schema.ipc.batches := 2 } original.schema [first, late, later])

  let invalid : Schema := ⟨[.node none true .list []]⟩
  expect (.batchLimit 1 0) (emit { schema.ipc.batches := 0 } invalid [second])
  expect (.schema (.arity 0 .list 0)) (emit {} invalid [])
  expect (.batch 0 (.ipc (.limit .rows))) (emit { schema.ipc.rows := 0 } original.schema [first])

  let leaf : Field := .node (some "wide") false .int64 []
  let good : Observation := ⟨1, [[some (.int64 (-9223372036854775808))]]⟩
  let required : Observation := ⟨1, [[none]]⟩
  expect (.batch 1 (.required 0 0)) (emit {} ⟨[leaf]⟩ [good, required])

public def main (args : List String) : IO Unit := do
  let folder :: names := args | throw (IO.userError "expected fixture folder and names")
  for name in names do
    reemit folder name
  controls folder
  IO.println "Emitted native recursive streams and checked seven typed refusals"
