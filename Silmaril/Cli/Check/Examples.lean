module

public import Silmaril.Cli.Check.Thms
public import Silmaril.Cli.Files.Defs
public meta import Silmaril.Cli.Check.Defs
public meta import Silmaril.Cli.Files.Defs

/-!
# CLI behaviour: checks, compiled examples

The examples of `docs/projects/cli.md`: one spec, proved for a program
and decided on recorded runs of a binary. `echo` prints its arguments; its check is
`Check.prints`, which decides `Spec.prints` (`decides_prints`); `orFail` and `orRefused` of it
are decided by prefix tests (`Decides.orFail`, `Decides.orRefused`).
-/

@[expose] public section

namespace Silmaril.Cli.Examples.Check

open Silmaril.Cli Silmaril.Cli.Spec

/-- What `echo` prints. -/
def echoOut (i : Input) : Bytes := utf8 (" ".intercalate i.args ++ "\n")

/-- `echo ARGS…`: print the arguments and succeed, no file changed. -/
def echo : Spec := prints echoOut

/-- Its check. -/
def echoCheck : Silmaril.Cli.Check := Check.prints echoOut

theorem echoCheck_decides : echoCheck.Decides echo := Check.decides_prints echoOut

/-- `echo`, allowing a failure after a prefix of its output (a WASI host may stop it). -/
theorem echoCheck_orFail : (echoCheck.orFail echoOut).Decides (orFail echo) :=
  echoCheck_decides.orFail (Check.fixes_prints echoOut)

/-- `echo`, allowing lost output after a refused write. -/
theorem echoCheck_orRefused :
    (echoCheck.orRefused echoOut fun _ => 0).Decides (orRefused echo) :=
  echoCheck_decides.orRefused (Check.fixes_prints echoOut)

/-- A test case: `echo a b` in a directory holding `in.txt`. -/
def case₁ : Input := ({ args := ["a", "b"] } : Input).inCwd [("in.txt", [1, 2, 3])]

#guard echoCheck case₁ { stdout := utf8 "a b\n" }
#guard !echoCheck case₁ { stdout := utf8 "a b" }
#guard !echoCheck case₁ { stdout := utf8 "a b\n", changes := [(FPath.cwd "in.txt", none)] }
#guard echoCheck case₁ { stdout := utf8 "a b\n", changes := [(FPath.cwd "in.txt", some [1, 2, 3])] }
#guard echoCheck.orFail echoOut case₁ { stdout := utf8 "a ", exit := 1 }
#guard !echoCheck.orFail echoOut case₁ { stdout := utf8 "a ", exit := 0 }
#guard echoCheck.orRefused echoOut (fun _ => 0) case₁ { refused := true }
#guard !echoCheck.orRefused echoOut (fun _ => 0) case₁ { }

end Silmaril.Cli.Examples.Check
