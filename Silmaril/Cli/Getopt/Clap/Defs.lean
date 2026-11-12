module

public import Silmaril.Cli.Getopt.Defs
public import Silmaril.Cli.Clap.Defs

/-!
# The getopt and clap dialects of one grammar

`Tool.clap` reads the grammar of a getopt tool in the clap dialect. The theorem relating the two
readings is in `Silmaril.Cli.Getopt.Clap.Thms`.

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-- The clap tool of a getopt tool: the same grammar, clap's defaults. -/
def Tool.clap (t : Tool) : Clap.Tool := { grammar := t.grammar }

end Silmaril.Cli.Getopt
