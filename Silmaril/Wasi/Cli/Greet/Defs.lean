module

public import Silmaril.Wasi.Cli.Host2.Defs
public import Silmaril.Wasi.Cli.Host3.Defs

/-!
# A worked example: `greet` as a WASI 0.2 and a WASI 0.3 command

The grammar `greetCmd` (`--name NAME`, default `world`, also read from `GREET_NAME`; `-h`,
`--help`; `-V`, `--version`) and the body that prints `hello, NAME`. `greet2` and `greet3` are
the components: `Command.mainWith` on the WASI 0.2 and 0.3 hosts (`command2`, `command3`).
`Silmaril.Wasi.Cli.Greet.Thms` proves that they meet `greetCmd.spec` for every host.

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Greet

open Silmaril.Cli Silmaril.Wasi.Cli

/-- **The grammar.** -/
def greetCmd : Command :=
  Command.withVersion (Command.withHelp
    { name := "greet", about := "Print a greeting",
      opts := [((opt "name" (help := "Who to greet")).withDefault "world").withEnv "GREET_NAME"],
      exits := [(0, "success"), (2, "usage error")] }) "1.0.0"

/-- The line `greet` prints. -/
def greetLine (m : Matches) : String := "hello, " ++ (m.str? "name").getD "world"

/-- **The WASI 0.2 component.** -/
def greet2 : Versions.P2.p2Command.Model :=
  Host2.command2 greetCmd fun m => Host2.api2.putLine .stdout (greetLine m) >>= fun _ => pure 0

/-- **The WASI 0.3 component.** -/
def greet3 : p3CliWorld.Model :=
  Host3.command3 greetCmd fun m => Host3.api3.putLine .stdout (greetLine m) >>= fun _ => pure 0

/-- **The specification**: the front end's, and `hello, NAME` with exit `0`. -/
def greetSpec : Spec := greetCmd.spec fun m => lineSpec .stdout (greetLine m) 0

end Silmaril.Wasi.Cli.Greet

end
