module

import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def readWire (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  let lean ← readWire directory "empty-middle-wide"
  let pyarrow ← readWire directory "pyarrow-wide"
  let moved ← readWire directory "pyarrow-empty-first"
  let zero ← readWire directory "empty-middle-zero-width"
  let some observed := readEvents {} lean | throw (IO.userError "Lean stream failed")
  let exact : Arrow.MixedFlat.Limits := { observation := {
    ipc := { fields := 4, batches := 3 }, totalRows := 18, totalCells := 72 } }
  let some independent := readEvents exact pyarrow | throw (IO.userError "PyArrow stream failed")
  let some movedEmpty := readEvents exact moved | throw (IO.userError "moved batch stream failed")
  unless observed == independent && observed.batches.map Prod.fst == [12, 0, 6] do
    throw (IO.userError "independent complete IPC observations differ")
  unless movedEmpty.fields == observed.fields && movedEmpty.batches.map Prod.fst == [0, 12, 6] do
    throw (IO.userError "the moved empty batch position was lost")
  unless projectEvents (List.range observed.fields.length) observed == some observed do
    throw (IO.userError "identity changed the complete observation")
  let first := [2, 1, 2, 3, 0]
  let second := [4, 0, 2]
  let some composed := composePositions observed.fields.length first second
    | throw (IO.userError "valid composition refused")
  let staged := (projectEvents first observed).bind (projectEvents second)
  let direct := projectEvents composed independent
  unless composed == [0, 2, 2] && staged.isSome && staged == direct do
    throw (IO.userError "staged and composed repeated projections differ")
  let some zeroWidth := readEvents {} zero | throw (IO.userError "zero-width stream failed")
  unless projectEvents [] observed == some zeroWidth &&
      projectEvents [] independent == some zeroWidth && projectEvents [] zeroWidth == some zeroWidth &&
      zeroWidth.fields.isEmpty && zeroWidth.batches.map Prod.fst == [12, 0, 6] do
    throw (IO.userError "zero-width projection lost its explicit row counts")
  unless (composePositions observed.fields.length [4] []).isNone &&
      ((projectEvents [4] observed).bind (projectEvents [])).isNone &&
      (composePositions observed.fields.length first [5]).isNone &&
      ((projectEvents first observed).bind (projectEvents [5])).isNone do
    throw (IO.userError "invalid positional selection was accepted")
  let noEos := pyarrow.slice 0 (pyarrow.len - 8)
  unless (readEvents exact noEos).isNone do
    throw (IO.userError "missing EOS admitted a complete observation")
  IO.println "Two encodings agree through EOS; identity, repeats, zero width, moved empty batch, invalid positions and missing EOS checked."
