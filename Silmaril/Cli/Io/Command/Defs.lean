module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Cli.Front.Defs
public import Silmaril.Cli.Io.Check.Defs

/-!
# Programs and specifications behind a derived argument front end

A grammar `c : Command` (`Silmaril.Cli.Args`) fixes everything a CLI does before its own work:
which environment variables it reads, how the arguments parse and resolve, and what it prints
and exits with for help, version and usage errors (`interpret`, `Outcome.text`,
`Outcome.exitCode?`). This module makes that a **behaviour specification** and a **program**:

* `Command.envOf c i` (from `Silmaril.Cli.Front`): the environment the grammar reads on the
  invocation `i` (its declared variables only, `Command.envVars`).
* `Command.frontObs c out i`: the observation of an outcome that does not run the program: its
  text on its channel with a newline (as `Command.main` prints it), its exit code (`0` for help
  and version, `2` for usage errors), nothing read, consumed or changed.
* **`Command.spec c body`** (from `Silmaril.Cli.Front`, the front end as a spec): the
  derived front end, then `body m` on the matches `m`. Help, version and usage errors are
  determined by the grammar, so they cannot drift. Off the `run` outcome it is exactly
  `Command.frontObs` (`Command.spec_eq` in `Silmaril.Cli.Io.Command.Thms`).
* **`Prog.ofCommand c body`**: the same as a `Prog`: read the arguments and the declared
  variables, `interpret`, print the outcome's text, or run `body m`. `Prog.ofCommandCore c core`
  is the special case of a pure core on the matches and stdin.
* `Command.check c body`: the harness check of `Command.spec` from checks of the bodies.

`Silmaril.Cli.Io.Command.Thms` proves `Prog.ofCommand c body` is observed as `Command.spec`
predicts (`obs_ofCommand`), so it satisfies `Command.spec c S` iff each body satisfies `S m` on
the invocations that select it (`sat_ofCommand_iff`), and that `Command.check` is sound.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-- The exit code of an outcome that does not run the program (as `Command.spec` fixes it). -/
def Outcome.code (out : Outcome) : ExitCode := (out.exitCode?.getD 0).toUInt32.toUInt8

/-- **The observation of a front-end outcome** that does not run the program. -/
def Command.frontObs (c : Command) (out : Outcome) (i : Input) : Obs :=
  match out.text c with
  | some (.stdout, s) => { stdout := utf8 (s ++ "\n"), exit := out.code, fs := i.fs }
  | some (.stderr, s) => { stderr := utf8 (s ++ "\n"), exit := out.code, fs := i.fs }
  | none => { exit := out.code, fs := i.fs }

end Silmaril.Cli

namespace Silmaril.Cli.Io

/-- The front end as a program: arguments, the declared variables, `interpret`. -/
def front (c : Command) : Prog Outcome := do
  let args ← getArgs
  let vals ← getEnvs c.envVars
  pure (interpret c (fun v => (vals.lookup v).join) args)

/-- Print an outcome's text with a newline. -/
def emitText (c : Command) (out : Outcome) : Prog Unit :=
  match out.text c with
  | some (.stdout, s) => print (utf8 (s ++ "\n"))
  | some (.stderr, s) => eprint (utf8 (s ++ "\n"))
  | none => .pure ()

namespace Prog

/-- **A program behind the derived front end of `c`**: help, version and usage errors as the
grammar says, else `body m` on the matches. -/
def ofCommand (c : Command) (body : Matches → Prog ExitCode) : Prog ExitCode := do
  let out ← front c
  match out with
  | .run m => body m
  | res => do
    emitText c res
    pure res.code

/-- **A pure core behind the derived front end**: the core gets the matches and stdin. -/
def ofCommandCore (c : Command) (core : Matches → Bytes → Result) : Prog ExitCode :=
  ofCommand c fun m => do
    let s ← readStdin
    emit (core m s)

end Prog

/-- **The harness check of `Command.spec c S`**, from checks of the bodies. -/
def _root_.Silmaril.Cli.Command.check (c : Command) (body : Matches → Check) : Check := fun i s =>
  match interpret c (c.envOf i) i.args with
  | .run m => body m i s
  | res =>
    let o := c.frontObs res i
    s.stdout == o.stdout && s.stderr == o.stderr && s.exit == o.exit && s.files.isEmpty

end Silmaril.Cli.Io

end
