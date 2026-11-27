module

import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (Limits)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect (wanted : Error) (result : Except Error KBytes) : IO Unit := do
  match result with
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"accepted invalid input expecting {repr wanted}")

private def reemit (dir : System.FilePath) (name : String) : IO Unit := do
  let carrier ← IO.FS.readBinFile (dir / (name ++ ".arrow"))
  let original := KBytes.ofChunks 1 carrier.size (carrier.data.toList.map UInt8.toNat)
  let source ← require (Formats.Arrow.RecursiveSchema.Stream.read {} original)
  let schema ← require (Formats.Arrow.RecursiveSchema.Writer.emit {} source.schema)
  let frames ← source.batches.mapM fun batch => require (emit {} source.schema batch.observed)
  let schemaFrame := schema.slice 0 (schema.len - 8)
  let wire := schemaFrame ++ frames.foldr (· ++ ·) Formats.Arrow.StreamWriter.eos
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) wire.toByteArray

private def controls : IO Unit := do
  let leaf : Field := .node (some "wide") false .int64 []
  let scalar : Schema := ⟨[leaf]⟩
  let value : Observation := ⟨1, [[some (.int64 (-9223372036854775808))]]⟩
  let scalarLimits : Limits :=
    { schema := { depth := 1, ipc := { rows := 1, fields := 1, metadataBytes := 152, bodyBytes := 16 } }
      slots := 1 }
  let emptyLimits : Limits :=
    { schema := { depth := 0, ipc := { rows := 2, fields := 0, metadataBytes := 104, bodyBytes := 0 } }
      slots := 0 }
  let _ ← require (emit scalarLimits scalar value)
  let _ ← require (emit emptyLimits ⟨[]⟩ ⟨2, [[], []]⟩)
  let _ ← require (checkOffset 0 (2^31 - 1))

  expect (.rowCount 2 1) (emit {} scalar ⟨2, value.rows⟩)
  expect (.rowWidth 0 1 0) (emit {} scalar ⟨1, [[]]⟩)
  expect (.required 0 0) (emit {} scalar ⟨1, [[none]]⟩)
  expect (.kind 0 0 .int64) (emit {} scalar ⟨1, [[some (.int32 5)]]⟩)
  let compound : Schema := ⟨[.node none true .struct [leaf]]⟩
  expect (.structWidth 0 0 1 0) (emit {} compound ⟨1, [[some (.struct [])]]⟩)
  expect (.required 1 0) (emit {} compound ⟨1, [[some (.struct [none])]]⟩)
  expect (.arity 0 .list 0) (emit {} ⟨[.node none true .list []]⟩ ⟨0, []⟩)
  expect (.depth 1) (emit { schema.depth := 1 } compound ⟨1, [[none]]⟩)
  expect (.ipc (.limit .fields)) (emit { schema.ipc.fields := 1 } compound ⟨1, [[none]]⟩)
  expect (.ipc (.limit .rows)) (emit { schema.ipc.rows := 0 } scalar value)
  expect (.ipc (.limit .metadataBytes)) (emit { schema.ipc.metadataBytes := 151 } scalar value)
  expect (.ipc (.limit .bodyBytes)) (emit { schema.ipc.bodyBytes := 15 } scalar value)
  expect (.slots 0) (emit { slots := 0 } scalar value)
  let nested : Schema := ⟨[.node none true .list [leaf]]⟩
  let nestedValues : Observation := ⟨1, [[some (.list [some (.int64 1), some (.int64 2)])]]⟩
  expect (.slots 1) (emit { slots := 2 } nested nestedValues)
  match checkOffset 7 (2^31) with
  | .error cause =>
    unless cause = .listOffset 7 (2^31) do
      throw (IO.userError s!"wrong offset refusal: {repr cause}")
  | .ok _ => throw (IO.userError "signed List offset overflow was accepted")

public def main (args : List String) : IO Unit := do
  let folder :: names := args | throw (IO.userError "expected fixture folder and names")
  for name in names do
    reemit folder name
  controls
  IO.println "Emitted native recursive RecordBatches and checked fifteen typed refusals"
