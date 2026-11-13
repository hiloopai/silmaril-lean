import Silmaril.Cli.Demo.Defs

/-!
# `cli-demo`

The demo grammar of `Silmaril.Cli.Demo` behind the derived front end (`Command.main`). On a
successful parse it prints the subcommand path and the typed matches, one binding per line, so
`tests/run.sh` can check the derived parser, help, errors and exit codes on a real binary.
-/

open Silmaril.Cli

def showValue : Value → String
  | .str s => s
  | .nat n => toString n
  | .int i => toString i
  | .flag => "flag"
  | .off => "off"

def main (args : List String) : IO UInt32 :=
  Demo.demo.main (fun m => do
    IO.println ("path: " ++ " ".intercalate m.path)
    for (k, vs) in m.values do
      unless vs.isEmpty do
        IO.println (k ++ ": " ++ ", ".intercalate (vs.map showValue))
    pure 0) args
