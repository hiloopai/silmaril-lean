module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Cli.Behaviour.Defs

@[expose] public section

/-!
# The derived front end as a behaviour specification

`Silmaril.Cli.Args` derives, from a grammar `c : Command`, the whole front end of a program:
`interpret c env argv` decides whether the program runs (with typed `Matches`), prints its help
or version, or reports a usage error. This file reads that front end in the behaviour model of
`Silmaril.Cli.Behaviour` (`Input`, `Obs`, `Spec`):

* `Command.spec c S` (**the interpreter's outcome as a `Spec`**): when the arguments resolve to
  matches `m`, the program behaves as `S m`; otherwise it prints the help or the version on
  stdout and exits 0, or the error and the usage of the subcommand on stderr and exits 2,
  touching no file and reading no stdin.
* `Spec.usageError`: a loose usage error (exit 2, nothing on stdout, files unchanged, nothing
  read), which every usage-error outcome of `Command.spec` refines (`spec_usageError`).
* `Beh`: programs in the behaviour model, a relational state monad (an invocation, a result
  and an observation), with the host operations of the front end (`Beh.host`). `Command.main`
  is `Command.mainWith Host.io`; read with `Beh.host` it is `Command.modelMain`, and
  `Silmaril.Cli.Front.Thms` proves that it refines `Command.spec` (`main_refines`).

The `IO` host reads each operation the way `Beh.host` does (`IO.getEnv` per declared variable,
`IO.println`/`IO.eprintln` write the text and a newline); that correspondence is the trusted
step, as for the bridge's `Prog.toIO`.

A Silmaril addition; the guide is `docs/projects/wasm-binaryen-tooling.md`.
-/

namespace Silmaril.Cli

/-! ## Programs in the behaviour model -/

/-- **A program in the behaviour model**: on an invocation, the results it may return, each
with the observation of the run. -/
def Beh (α : Type) : Type := Input → α → Obs → Prop

/-- The observation of a step that does nothing. -/
def Obs.skip (i : Input) : Obs := { fs := i.fs }

namespace Beh

variable {α β : Type}

/-- Return `a`, doing nothing. -/
protected def pure (a : α) : Beh α := fun i b o => b = a ∧ o = Obs.skip i

/-- Sequencing: the second program runs on what the first left. -/
protected def bind (p : Beh α) (f : α → Beh β) : Beh β := fun i b o =>
  ∃ a o₁ o₂, p i a o₁ ∧ f a (i.after o₁) b o₂ ∧ o = o₁.andThen o₂

instance : Monad Beh where
  pure := Beh.pure
  bind := Beh.bind

/-- The values of the declared variables `vs` (the others read as unset). -/
def envOf (vs : List String) (i : Input) : String → Option String :=
  fun v => if v ∈ vs then i.getEnv v else none

/-- Read the environment variables `vs`. -/
def getEnvs (vs : List String) : Beh (String → Option String) := fun i f o =>
  f = envOf vs i ∧ o = Obs.skip i

/-- What printing a line (or nothing) shows. -/
def lineObs (i : Input) : Option (Channel × String) → Obs
  | some (.stdout, s) => { stdout := utf8 (s ++ "\n"), fs := i.fs }
  | some (.stderr, s) => { stderr := utf8 (s ++ "\n"), fs := i.fs }
  | none => Obs.skip i

/-- Print a line on a channel. -/
def putLine (ch : Channel) (s : String) : Beh Unit := fun i _ o => o = lineObs i (some (ch, s))

/-- **The host of the front end in the behaviour model.** -/
def host : Host Beh := ⟨getEnvs, putLine⟩

/-- A specification, as a main program returning its exit code. -/
def ofSpec (S : Spec) : Beh UInt32 := fun i c o => S i o ∧ c = o.exit.toUInt32

/-- **The specification of a main program**: its observations, with the exit code it returns
(its low 8 bits, as a process exit status). -/
def toSpec (p : Beh UInt32) : Spec := fun i o =>
  ∃ c o', p i c o' ∧ o = { o' with exit := c.toUInt8 }

/-- A program that reads its arguments from the invocation. -/
def withArgs (p : List String → Beh α) : Beh α := fun i => p i.args i

end Beh

/-! ## The front end as a specification -/

/-- The environment the front end of `c` reads from an invocation: its declared variables. -/
def Command.envOf (c : Command) (i : Input) : String → Option String := Beh.envOf c.envVars i

/-- What the front end decides on an invocation. -/
def Command.outcome (c : Command) (i : Input) : Outcome := interpret c (c.envOf i) i.args

/-- **The interpreter's outcome as a behaviour specification**: on matches `m` the program
behaves as `S m`; otherwise it prints the outcome's text with a newline (help and version on
stdout, a usage error with the usage of its subcommand on stderr) and exits with the outcome's
code (0, 0, 2), touching nothing else. -/
def Command.spec (c : Command) (S : Matches → Spec) : Spec := fun i o =>
  match c.outcome i with
  | .run m => S m i o
  | out => o = { Beh.lineObs i (out.text c) with exit := (out.exitCode?.getD 0).toUInt32.toUInt8 }

/-- The invocations on which the front end reports a usage error. -/
def Command.UsageErr (c : Command) (i : Input) : Prop := ∃ p e, c.outcome i = .error p e

/-- **A loose usage error**: exit code 2, nothing on stdout, no file changed or read, no stdin
consumed. -/
def Spec.usageError : Spec := fun i o =>
  o.exit = 2 ∧ o.stdout = [] ∧ o.fs = i.fs ∧ o.reads = [] ∧ o.consumed = 0

/-- **`Command.main` read in the behaviour model**: the same program (`Command.mainWith`), with
the host `Beh.host` and the arguments of the invocation. -/
def Command.modelMain (c : Command) (run : Matches → Beh UInt32) : Beh UInt32 :=
  Beh.withArgs (c.mainWith Beh.host run)

end Silmaril.Cli
