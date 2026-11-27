module

import Silmaril.Formats.Parquet.FlatProjection.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatProjection

private def load (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map Bytes.mk

private def failed (parquet : Limits) (ipc : Arrow.MixedFlat.Limits)
    (input : Bytes) (ordinals : List Nat) (expected : Error) : IO Unit := do
  let .error actual := convert parquet ipc input ordinals
    | throw (IO.userError s!"expected {repr expected}, got a stream")
  unless actual == expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def emitFixture (directory : System.FilePath) (source result : String)
    (ordinals : List Nat) (counts : List Nat) : IO Unit := do
  let input ← load directory source
  let .ok checked := openFile {} input ordinals
    | throw (IO.userError s!"{result}: open failed")
  let .ok groups := checked.readAll {}
    | throw (IO.userError s!"{result}: group read failed")
  unless checked.columns.map Bound.ordinal == ordinals && groups.map (·.rowCount) == counts do
    throw (IO.userError s!"{result}: changed ordinal order or group boundaries")
  let output ← match convert {} {} input ordinals with
    | .ok wire => pure wire
    | .error cause => throw (IO.userError s!"{result}: {repr cause}")
  IO.FS.writeBinFile (directory / (result ++ ".arrows")) output.toByteArray

public def main (args : List String) : IO Unit := do
  let [path, pageHeader] := args | throw (IO.userError "expected fixture directory and damaged header")
  let some header := pageHeader.toNat? | throw (IO.userError "expected a numeric damaged header")
  let directory := System.FilePath.mk path
  let projection := [3, 0, 1, 2]
  emitFixture directory "wide" "wide" projection [12, 6]
  emitFixture directory "wide" "reordered" [2, 1, 0] [12, 6]
  emitFixture directory "wide" "repeated" [3, 0, 3, 2] [12, 6]
  emitFixture directory "wide" "zero-width" [] [12, 6]
  emitFixture directory "empty-middle" "empty-middle" projection [12, 0, 6]
  emitFixture directory "schema-only" "schema-only" projection []
  emitFixture directory "wide-late" "unselected-damage" [2, 1, 0] [12, 6]

  let wide ← load directory "wide"
  let exact : Limits := { column := { maxFileBytes := wide.length }, maxFileRows := 18, maxFields := 4 }
  let .ok exactWire := convert exact {} wide projection
    | throw (IO.userError "exact source caps refused")
  let expected ← IO.FS.readBinFile (directory / "wide.arrows")
  unless expected == exactWire.toByteArray do throw (IO.userError "exact cap changed output bytes")
  failed { exact with column := { exact.column with maxFileBytes := wide.length - 1 } } {} wide projection
    (.source (.fileByteLimit (wide.length - 1) wide.length))
  failed { exact with maxFields := 3 } {} wide projection (.source (.fieldLimit 3 4))
  failed { exact with maxFileRows := 17 } {} wide projection (.source (.fileRowLimit 17 18))
  failed {} {} wide [3, 7] (.source (.bind 1 7 .missingLeaf))
  failed {} {} wide [3, 4] (.source (.bind 1 4 (.unsupportedPhysical (some .boolean))))
  let ipc : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 2 } } }
  failed {} ipc wide projection (.writer (.ipc (.limit .fields)))

  let damaged ← load directory "wide-late"
  let cause := Int32ByteArrayGroup.Error.byteArray
    (.page 1 3 "long" 0 header (.decode (.scalar (.plain .truncated))))
  failed {} ipc damaged projection (.source (.read 1 0 3 cause))
  failed {} {} damaged [2, 0, 3, 1] (.source (.read 1 2 3 cause))
  let .ok checked := openFile {} damaged projection
    | throw (IO.userError "late-damage fixture failed to open")
  let .ok earlier := checked.readGroup {} 0
    | throw (IO.userError "late-damage fixture lost the earlier complete group")
  unless earlier.rowCount == 12 do throw (IO.userError "bad earlier group count")
  IO.println "Seven native streams, exact source caps, and eight typed failure controls."
