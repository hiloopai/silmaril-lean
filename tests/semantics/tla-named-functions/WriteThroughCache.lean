module

import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

open Silmaril.Logic.Temporal.TLA

private def parse {α : Type} (result : Except Surface.Parser.Diagnostic α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the pinned WriteThroughCache.tla path")
  let source ← parse (Surface.Parser.parseModule (← IO.FS.readFile path))
  unless source.name == "WriteThroughCache" &&
      source.extendsModules == ["Naturals", "Sequences", "MemoryInterface"] do
    throw (IO.userError "unexpected module or imports")
  let [body] := source.units.filterMap (fun
    | .definition (.operator .ordinary (.ident "vmem" []) body) => some body
    | _ => none)
    | throw (IO.userError "expected exactly one vmem definition")
  -- Keep the input to the semantic bridge pinned down to the complete LET, including its IN.
  let expected ← parse (Surface.Parser.parseExpr "LET f[i \\in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
                 ELSE IF memQ[i][2].op = \"Rd\"
                      THEN f[i-1]
                      ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
    IN f[Len(memQ)]")
  unless reprStr body == reprStr expected do
    throw (IO.userError s!"unexpected vmem body: {reprStr body}")
  IO.println "WriteThroughCache.vmem: pinned local definition and IN expression match the semantic bridge"
