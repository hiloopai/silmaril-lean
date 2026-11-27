module

import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Examples
meta import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Examples

open Silmaril Silmaril.Formats.Arrow.LargeUtf8.Stream.Events

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected output directory")
  let dir := System.FilePath.mk output
  for (name, framing, wire) in Examples.inputs ++ Examples.schemaInputs do
    let .ok encoded := emit {} (readAll {} framing wire) |
      throw (IO.userError s!"failed to transcode {name} source")
    IO.FS.writeBinFile (dir / s!"{name}.source.arrows") wire.toByteArray
    IO.FS.writeBinFile (dir / s!"{name}.arrows") encoded.toByteArray
