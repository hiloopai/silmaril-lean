module

import Lean.Data.Json
import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
meta import Lean.Data.Json
meta import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs

open Lean (Json toJson)
open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatProjection
open Silmaril.Formats.Parquet.FlatProjection.Composition

private def original : List Nat := [3, 0, 1, 2]

private def load (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map Bytes.mk

private def read (limits : Limits) (file : Bytes) (ordinals : List Nat) :
    IO (Checked × List Arrow.MixedFlat.OrderedWriter.BatchInput) := do
  let .ok opened := openFile limits file ordinals | throw (IO.userError "source open failed")
  let .ok batches := opened.readAll limits | throw (IO.userError "source read failed")
  return (opened, batches)

private def describe (field : Arrow.MixedFlat.Field) : IO Json := do
  let kind ← match field.kind with
    | .primitive .int32 => pure "int32"
    | .view .binary => pure "binary"
    | _ => throw (IO.userError "unexpected field kind")
  return Json.mkObj [("name", toJson field.name), ("nullable", toJson field.nullable), ("kind", toJson kind)]

private def values : Arrow.MixedFlat.OrderedWriter.Column → IO Json
  | .int32 _ _ slots => pure (toJson (slots.map (Option.map Int32.toInt)))
  | .binary _ _ slots => pure (toJson (slots.map (Option.map (List.map UInt8.toNat ∘ KBytes.toList))))
  | .utf8View .. => throw (IO.userError "unexpected textual values")

private def compare (file : Bytes) (positions counts : List Nat) : IO Json := do
  let .some ordinals := composeOrdinals original positions | throw (IO.userError "invalid fixture positions")
  let wideCaps : Limits := { column := { maxFileBytes := file.length + 1 }, maxFileRows := 19, maxFields := 4 }
  let directCaps : Limits := ⟨{ maxFileBytes := file.length }, counts.sum, ordinals.length⟩
  let (wide, wideBatches) ← read wideCaps file original
  let (direct, directBatches) ← read directCaps file ordinals
  let .some projected := project positions (observe wide wideBatches)
    | throw (IO.userError "successful wider read cannot be selected")
  unless projected = observe direct directBatches ∧ directBatches.map (·.rowCount) = counts do
    throw (IO.userError "direct read disagrees with selected observation")
  let fields ← direct.fields.mapM describe
  let groups ← directBatches.mapM fun batch => do
    return Json.mkObj [("rows", toJson batch.rowCount), ("values", toJson (← batch.columns.mapM values))]
  return Json.mkObj [("fields", toJson fields), ("groups", toJson groups)]

private def refused (limits : Limits) (file : Bytes) (ordinals : List Nat) (expected : SourceError) : IO Unit := do
  let .error actual := openFile limits file ordinals
    | throw (IO.userError s!"expected {repr expected}, got a source")
  unless actual == expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fixture directory")
  let directory := System.FilePath.mk path
  let wide ← load directory "wide"
  let empty ← load directory "empty-middle"
  let schemaOnly ← load directory "schema-only"
  let observations ← [
    (wide, [2, 1, 2], [12, 6]),
    (wide, [2, 1, 2, 0, 2], [12, 6]),
    (empty, [], [12, 0, 6]),
    (empty, [2, 1, 2], [12, 0, 6]),
    (schemaOnly, [2, 1, 2], []),
  ].mapM fun (source, positions, counts) => compare source positions counts

  let exact : Limits := { column := { maxFileBytes := wide.length }, maxFileRows := 18, maxFields := 3 }
  refused { exact with column := { exact.column with maxFileBytes := wide.length - 1 } } wide [1, 0, 1]
    (.fileByteLimit (wide.length - 1) wide.length)
  refused { exact with maxFileRows := 17 } wide [1, 0, 1] (.fileRowLimit 17 18)
  refused { exact with maxFields := 2 } wide [1, 0, 1] (.fieldLimit 2 3)
  refused { exact with maxFields := 4 } wide [1, 0, 1, 3, 1] (.fieldLimit 4 5)
  IO.FS.writeFile (directory / "observations.json") ((toJson observations).compress ++ "\n")
  IO.println "Five exact source observations with independent exact caps, and four one-under admission refusals."
