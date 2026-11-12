module

public import Silmaril.Cli.Surface.Defs
public meta import Silmaril.Cli.Surface.Defs

/-!
# CLI surfaces: the example of docs/projects/cli.md

The `greet` example of the API guide (docs/projects/cli.md, "Apply"), evaluated (`#guard`).
-/

public section

namespace Silmaril.Cli.Surface.Examples

open Silmaril.Cli.Surface

def greet : Command where
  name := "greet"
  about := "Print a greeting"
  pos := [{ metavar := "NAME", required := true }]
  opts := [Opt.val "times" "N" "repeat the greeting" (short := 'n'),
           Opt.flag "shout" "upper case", Opt.helpWith "Print help"]

#guard greet.usage ["greet"] == "Usage: greet [OPTIONS] <NAME>"

#guard greet.help ["greet"] ==
  "Print a greeting\n\nUsage: greet [OPTIONS] <NAME>\n\nArguments:\n  <NAME>\n\nOptions:\n" ++
  "  -n, --times <N>  repeat the greeting\n      --shout      upper case\n" ++
  "  -h, --help       Print help\n"

#guard greet.parse ["-n", "2", "--shout", "ada"] ==
  .run { path := [], opts := [("times", some "2"), ("shout", none)], args := ["ada"] }

#guard greet.parse ["--times"] ==
  .error "a value is required for '-n, --times <N>' but none was supplied"

#guard greet.parse ["ada", "bob"] == .error "unexpected argument 'bob' found"
#guard greet.parse [] == .error "the following required arguments were not provided"
#guard greet.parse ["--", "--shout"] == .run { args := ["--shout"] }
#guard greet.parse ["-h", "--bogus"] == .help ["greet"]
#guard (greet.parse ["--bogus", "-h"]).exit == some 2

end Silmaril.Cli.Surface.Examples
