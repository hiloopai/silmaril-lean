module

public import Silmaril.Cli.Io.Command.Defs

/-!
# The CLI spec API on one page: definitions

The definitions of the guide at the top of `docs/projects/cli.md` (namespace `Silmaril.Cli.Guide`): a
grammar `greetCmd`, a behaviour specification `greetSpec` derived from the same grammar, a Lean
program `greetProg` built from a pure core, and a decidable check `greetCheck` for the test
harness. `Silmaril.Cli.Guide.Thms` evaluates the front end and proves the program and the check
correct.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Guide

open Silmaril.Cli Silmaril.Cli.Io

/-! ## The grammar is data -/

/-- `greet [-s] [--greeting G] NAME`; `G` defaults to `$GREETING`, else `hello`. -/
def greetCmd : Command :=
  Command.withVersion (Command.withHelp
    { name := "greet", about := "Greet someone",
      opts := [flag "shout" ["s"] "Print in capitals",
               ((opt "greeting" (help := "The greeting")).withDefault "hello").withEnv "GREETING"],
      pos := [arg "name" (help := "Who to greet")],
      exits := [(0, "success"), (2, "usage error")] }) "1.0.0"

/-! ## The behaviour specification, from the same grammar -/

/-- What `greet` prints on its matches. -/
def greetLine (m : Matches) : Bytes :=
  let s := (m.str? "greeting").getD "hello" ++ ", " ++ " ".intercalate (m.strs "name") ++ "\n"
  utf8 (if m.flag "shout" then s.toUpper else s)

/-- Help, version and usage errors as derived from the grammar; otherwise print the line,
read nothing, change no file, exit 0. -/
def greetSpec : Spec := greetCmd.spec fun m => Spec.pure fun _ => { stdout := greetLine m }

/-! ## A Lean program from a pure core meets it -/

def greetProg : Prog ExitCode := Prog.ofCommandCore greetCmd fun m _ => { stdout := greetLine m }

/-! ## A decidable check for the test harness, sound for the spec -/

def greetCheck : Check := greetCmd.check fun m _ s =>
  s.exit == 0 && s.stdout == greetLine m && s.stderr.isEmpty && s.files.isEmpty

/-! ## Growing the CLI: adding a flag keeps every old command line -/

def quiet : Opt := flag "quiet" ["q"] "Print nothing"

end Silmaril.Cli.Guide

end
