module

import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Examples
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Examples

open Silmaril Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected output directory")
  let output := System.FilePath.mk path
  for (name, fields, batches) in Examples.cases do
    let .ok wire := emit {} fields batches | throw (IO.userError s!"failed to write {name}")
    IO.FS.writeBinFile (output / s!"{name}.arrows") wire.toByteArray
