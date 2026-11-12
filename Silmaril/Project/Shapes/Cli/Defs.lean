module

public import Silmaril.Project.Defs
public import Silmaril.Cli.Info.Defs

/-!
# Standard problem shapes: command-line programs (`--help`, `--version`)

The conventions "`--help` works" and "`--version` works" as shapes, parametrized by the
**model** (`M`, a model of the full interface of the CLI institution,
`Silmaril.Cli.Institution.Model Level.full.sig`) and the **variant** (`Silmaril.Cli.Info`:
which spellings trigger the request, where, what more arguments must give, the reply, whether
anything else may happen). A Lean program is the model `p.model`; a program semantics at any
other interface `A` with a morphism `h : Level.full.sig ⟶ A` (a WASI component, an ELF process
model) is the reduct `Hom.mod h M` (`Silmaril.Project.Shapes.Cli.Thms`: `help_via_iff`).

| name | statement |
|---|---|
| `silmaril.shapes.cli.help` | `Help M v`: `M` satisfies the help sentence of the variant `v` |
| `silmaril.shapes.cli.help.{basic,short,loose,wins,either}` | the same with a named variant (`HelpVariant.named`) |
| `silmaril.shapes.cli.help.subcommands` | `HelpSubcommands M ps`: `--help` and `-h` at the root and after each subcommand path in `ps` |
| `silmaril.shapes.cli.version` | `Version M v`: `M` satisfies the version sentence of `v` |
| `silmaril.shapes.cli.version.{basic,short}` | the same with a named variant (`VersionVariant.named`) |
| `silmaril.shapes.cli.version.pinned` | `VersionPinned M ver`: `--version` prints a text containing `ver` |

Every sentence is a safety sentence: it constrains only the invocations that ask for help or
the version. None pins the help text; a variant may require substrings or exact texts.

A row, for a program `demo.tool`:

```lean
silmaril instance demo.tool.help := silmaril.shapes.cli.help.basic (M := Demo.tool.model)
```
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Cli

open Silmaril.Cli Silmaril.Cli.Info Silmaril.Cli.Institution

/-- **`M` answers help requests as the variant `v` says** (`HelpVariant.sen`). -/
@[problem "silmaril.shapes.cli.help"
  (title := "A command-line program answers help requests as a variant says")]
def Help (M : Silmaril.Cli.Institution.Model Level.full.sig) (v : HelpVariant) : Prop :=
  M.Sat v.sen

/-- **`--help` and `-h` work at the root and after each of the subcommand paths `ps`.** -/
@[problem "silmaril.shapes.cli.help.subcommands"
  (title := "A command-line program answers help at the root and after given subcommands")]
def HelpSubcommands (M : Silmaril.Cli.Institution.Model Level.full.sig)
    (ps : List (List String)) : Prop :=
  Help M (.subcommands ps)

/-- **`M` answers version requests as the variant `v` says** (`VersionVariant.sen`). -/
@[problem "silmaril.shapes.cli.version"
  (title := "A command-line program answers version requests as a variant says")]
def Version (M : Silmaril.Cli.Institution.Model Level.full.sig) (v : VersionVariant) : Prop :=
  M.Sat v.sen

/-- **`--version` prints a text containing `ver`.** -/
@[problem "silmaril.shapes.cli.version.pinned"
  (title := "A command-line program prints a given version")]
def VersionPinned (M : Silmaril.Cli.Institution.Model Level.full.sig) (ver : String) : Prop :=
  Version M (.pinned ver)

end Silmaril.Project.Shapes.Cli

end

silmaril instance silmaril.shapes.cli.help.basic
    (title := "help, --help at the root, exit 0, text on stdout, nothing else") :=
  silmaril.shapes.cli.help (v := Silmaril.Cli.Info.HelpVariant.basic)
silmaril instance silmaril.shapes.cli.help.short (title := "help, --help and -h at the root") :=
  silmaril.shapes.cli.help (v := Silmaril.Cli.Info.HelpVariant.basicShort)
silmaril instance silmaril.shapes.cli.help.loose
    (title := "help, --help at the root, any exit code, text on stdout or stderr") :=
  silmaril.shapes.cli.help (v := Silmaril.Cli.Info.HelpVariant.loose)
silmaril instance silmaril.shapes.cli.help.wins
    (title := "help, --help and -h win over everything after them") :=
  silmaril.shapes.cli.help (v := Silmaril.Cli.Info.HelpVariant.wins)
silmaril instance silmaril.shapes.cli.help.either
    (title := "help, --help and -h, then help or a usage error") :=
  silmaril.shapes.cli.help (v := Silmaril.Cli.Info.HelpVariant.either)
silmaril instance silmaril.shapes.cli.version.basic
    (title := "version, --version, exit 0, text on stdout, nothing else") :=
  silmaril.shapes.cli.version (v := Silmaril.Cli.Info.VersionVariant.basic)
silmaril instance silmaril.shapes.cli.version.short (title := "version, --version and -V") :=
  silmaril.shapes.cli.version (v := Silmaril.Cli.Info.VersionVariant.basicShort)
