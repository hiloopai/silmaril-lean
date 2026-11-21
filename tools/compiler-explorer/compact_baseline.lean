module

import Silmaril.Project.CompilesTo.Probe.Defs
import Silmaril.Compiler.C.Compact.Defs
meta import Silmaril.Project.CompilesTo.Probe.Defs
meta import Silmaril.Compiler.C.Compact.Defs

open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo.Probe
open Silmaril.Compiler.C.Compact

public def main (args : List String) : IO Unit := do
  let [source, output] := args | throw (IO.userError "usage: compact_baseline <source.c> <out-dir>")
  let text ← IO.FS.readFile source
  let .ok ail := FrontendAil text | throw (IO.userError "C frontend rejected baseline")
  let .ok core := ElabAil ail | throw (IO.userError "Core elaborator rejected baseline")
  IO.FS.createDirAll output
  IO.FS.writeFile s!"{output}/typed-ail.sexp" (ailText ail)
  IO.FS.writeFile s!"{output}/core.sexp" (document core)
  match project ail with
  | .error reason => IO.println s!"compact projection refused {source}: {reason}"
  | .ok _ => IO.println s!"compact projection accepted {source}"
