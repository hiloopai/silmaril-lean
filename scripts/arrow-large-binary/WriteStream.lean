module

import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Examples
meta import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Examples

open Silmaril Silmaril.Formats.Arrow.LargeBinary.StreamWriter

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected output directory")
  let dir := System.FilePath.mk output
  for (name, field, batches) in Examples.cases do
    let .ok wire := emit {} field batches | throw (IO.userError s!"emission failed for {name}")
    IO.FS.writeBinFile (dir / s!"{name}.arrows") wire.toByteArray
