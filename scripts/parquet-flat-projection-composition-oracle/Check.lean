module

import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatProjection
open Silmaril.Formats.Parquet.FlatProjection.Composition

private def original : List Nat := [3, 0, 1, 2]

private def positions : List Nat := [2, 1, 2]

private def wideLimits : Limits := { maxFields := 4, maxFileRows := 18 }

private def directLimits : Limits := { maxFields := 3, maxFileRows := 20 }

private def load (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map Bytes.mk

private def readObservation (limits : Limits) (input : Bytes) (ordinals : List Nat) : IO Observation := do
  let .ok opened := openFile limits input ordinals | throw (IO.userError "source open failed")
  let .ok batches := opened.readAll limits | throw (IO.userError "source read failed")
  return observe opened batches

private def checkComposition (directory : System.FilePath) (input : Bytes) (name : String)
    (selection counts : List Nat) : IO Unit := do
  let wide ← readObservation wideLimits input original
  let .some ordinals := composeOrdinals original selection
    | throw (IO.userError s!"{name}: valid position rejected")
  let narrow ← readObservation directLimits input ordinals
  let .some selected := project selection wide
    | throw (IO.userError s!"{name}: observation projection failed")
  unless selected = narrow ∧ selected.batches.map Prod.fst = counts do
    throw (IO.userError s!"{name}: selection and direct read disagree")
  let .ok wire := convert directLimits {} input ordinals
    | throw (IO.userError s!"{name}: output failed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def expect (limits : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (ordinals : List Nat) (error : Error) : IO Unit := do
  let .error actual := convert limits ipc input ordinals
    | throw (IO.userError s!"expected {repr error}, got a stream")
  unless actual == error do throw (IO.userError s!"expected {repr error}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [path, pageHeader] := args | throw (IO.userError "expected fixture directory and damaged header")
  let some header := pageHeader.toNat? | throw (IO.userError "expected a numeric damaged header")
  let directory := System.FilePath.mk path
  let genuine ← load directory "wide"
  let framed ← load directory "empty-middle"
  let schemaOnly ← load directory "schema-only"
  checkComposition directory genuine "wide-repeat" positions [12, 6]
  checkComposition directory framed "framed-repeat" positions [12, 0, 6]
  checkComposition directory framed "framed-empty" [] [12, 0, 6]
  checkComposition directory schemaOnly "schema-only-repeat" positions []

  let wide ← readObservation wideLimits genuine original
  unless (composeOrdinals original [4]).isNone && (project [4] wide).isNone do
    throw (IO.userError "invalid composition position was silently dropped")
  let .some composed := composeOrdinals original positions
    | throw (IO.userError "composition lookup failed")
  unless composed == [1, 0, 1] do throw (IO.userError "wrong composed ordinals")

  let narrowFields : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 3 } } }
  let narrowCells : Arrow.MixedFlat.Limits := { observation := { totalCells := 54 } }
  expect wideLimits narrowFields genuine original (.writer (.ipc (.limit .fields)))
  expect wideLimits narrowCells genuine original (.writer (.ipc (.limit .totalCells)))
  let .ok baseline := convert directLimits {} genuine composed
    | throw (IO.userError "default narrow writer refused")
  let .ok fieldBound := convert directLimits narrowFields genuine composed
    | throw (IO.userError "exact field cap refused the narrow output")
  let .ok cellBound := convert directLimits narrowCells genuine composed
    | throw (IO.userError "exact cell cap refused the narrow output")
  unless baseline.toByteArray == fieldBound.toByteArray && baseline.toByteArray == cellBound.toByteArray do
    throw (IO.userError "IPC budget changed admitted output bytes")

  let damaged ← load directory "wide-late"
  let cause := Int32ByteArrayGroup.Error.byteArray (.page 1 3 "long" 0 header (.decode (.scalar (.plain .truncated))))
  expect wideLimits {} damaged original (.source (.read 1 0 3 cause))
  let narrow ← readObservation directLimits damaged composed
  unless project positions wide = some narrow do throw (IO.userError "unselected damage changed the narrow read")
  let .ok wire := convert directLimits {} damaged composed
    | throw (IO.userError "selected projection failed over unselected damage")
  IO.FS.writeBinFile (directory / "wide-late-drop.arrows") wire.toByteArray
  IO.println "Four source composition comparisons, an invalid position, separate IPC field/cell caps, and one source-domain failure."
