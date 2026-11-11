module

public import Silmaril.Cli.Io.Command.Defs

/-!
# A CLI with a derived front end: `echon`

The worked example of `Prog.ofCommand` (`docs/projects/cli.md`):

```text
echon [-n] [--sep SEP] [WORD]...      SEP defaults to $ECHON_SEP, else " "
echon -h | --help | -V | --version
```

The grammar `echonCmd` is data (`Silmaril.Cli.Args`); the program `echonProg` is a pure core on
the matches behind the derived front end; its specification `echonSpec` is `Command.spec` of
the same grammar with a pure body; the harness check `echonCheck` is `Command.check` of it.
`Silmaril.Cli.Io.Echon.Thms` proves the program satisfies the spec and the check is sound;
`Prog.main` runs the program, and `checkCases` (`Silmaril.Cli.Io.Run`) checks a binary with it.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io.Echon

open Silmaril.Cli Silmaril.Cli.Io

/-- **The grammar of `echon`.** -/
def echonCmd : Command :=
  Command.withVersion (Command.withHelp
    { name := "echon", about := "Print words, separated and followed by a newline",
      opts := [flag "no-newline" ["n"] "Do not print the trailing newline",
               ((opt "sep" (help := "The separator")).withDefault " ").withEnv "ECHON_SEP"],
      pos := [arg "word" (arity := .many) (help := "The words to print")],
      exits := [(0, "success"), (2, "usage error")] }) "1.0.0"

/-- What `echon` prints on its matches. -/
def echonLine (m : Matches) : Bytes :=
  utf8 (((m.str? "sep").getD " ").intercalate (m.strs "word") ++
    (if m.flag "no-newline" then "" else "\n"))

/-- The core of `echon`. -/
def echonCore (m : Matches) (_ : Bytes) : Result := { stdout := echonLine m }

/-- **`echon`**: the core behind the derived front end. -/
def echonProg : Prog ExitCode := Prog.ofCommandCore echonCmd echonCore

/-- **`echon`'s specification**: the derived front end, then print the line. -/
def echonSpec : Spec := echonCmd.spec fun m => Spec.pure fun _ => { stdout := echonLine m }

/-- **`echon`'s check.** -/
def echonCheck : Check := echonCmd.check fun m _ s =>
  s.exit == 0 && s.stdout == echonLine m && s.stderr.isEmpty && s.files.isEmpty

end Silmaril.Cli.Io.Echon

end
