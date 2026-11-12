module

public import Silmaril.Cli.Behaviour.Defs

/-!
# CLI behaviour: decidable checks of recorded runs

What a test harness can decide about one run of a program, related to the behaviour model
(`docs/projects/cli.md`).

* **`Recorded`**: what a harness records of a run: stdout, stderr, exit code, stdin consumed, files
  read, the files created, changed or removed (`changes`, with their final contents), and whether
  the environment refused something. `Recorded.toObs r i` reads it as an observation of the
  invocation `i` (files not in `changes` are as before; the file log is not recorded).
* **`Check := Input → Recorded → Bool`**: a decidable specification. `c.Decides S` says the check
  decides the spec: `c i r = true ↔ S i (r.toObs i)` for every invocation and run. The proof of a
  program and the test of a binary then use the same spec.
* Checks for the builders of `Silmaril.Cli.Behaviour` (`exits`, `succeeds`, `fails`, `stdoutIs`,
  `stderrIs`, `silent`, `keepsFiles`, `consumesAll`, `prints`, `pure`), `and` and `or`, and the
  allowances `orFail` and `orRefused` for specs whose stdout and exit code are fixed
  (`Spec.Fixes`), so that `∃ o'` in their definitions becomes a prefix test. The `Decides`
  lemmas are in `Silmaril.Cli.Check.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-- **What a test harness records of a run.** -/
structure Recorded where
  /-- Stdout. -/
  stdout : Bytes := []
  /-- Stderr. -/
  stderr : Bytes := []
  /-- The exit code. -/
  exit : ExitCode := 0
  /-- Stdin consumed (a harness that feeds all of stdin and cannot tell records its length). -/
  consumed : Nat := 0
  /-- Files read, when known. -/
  reads : List FPath := []
  /-- The files created, changed or removed, with their final contents (`none`: removed). -/
  changes : List (FPath × Option Bytes) := []
  /-- The environment refused something during the run. -/
  refused : Bool := false
deriving DecidableEq, Repr

namespace Recorded

/-- The files after the run: the recorded changes over the files before it. -/
def fs (r : Recorded) (i : Input) : Fs := fun p =>
  match r.changes.lookup p with
  | some c => c
  | none => i.fs p

/-- **The observation a recorded run stands for** on the invocation `i`. -/
def toObs (r : Recorded) (i : Input) : Obs :=
  { stdout := r.stdout, stderr := r.stderr, exit := r.exit, consumed := r.consumed,
    reads := r.reads, fs := r.fs i, refused := r.refused }

end Recorded

/-- **A decidable specification** of recorded runs. -/
abbrev Check := Input → Recorded → Bool

namespace Spec

/-- **`S` fixes stdout and exit code**: it has a run on every invocation, and every run it
allows prints `out i` and exits with `code i`. The specs whose `orFail` and `orRefused` have a
check (`Check.orFail`, `Check.orRefused`). -/
def Fixes (S : Spec) (out : Input → Bytes) (code : Input → ExitCode) : Prop :=
  ∀ i, (∃ o, S i o) ∧ ∀ o, S i o → o.stdout = out i ∧ o.exit = code i

end Spec

namespace Check

/-- **`c` decides `S`** on recorded runs. -/
def Decides (c : Check) (S : Spec) : Prop := ∀ i r, c i r = true ↔ S i (r.toObs i)

/-- Both checks. -/
def and (c d : Check) : Check := fun i r => c i r && d i r

/-- Either check. -/
def or (c d : Check) : Check := fun i r => c i r || d i r

/-- Exit code `k`. -/
def exits (k : ExitCode) : Check := fun _ r => decide (r.exit = k)

/-- Exit code `0`. -/
def succeeds : Check := exits 0

/-- A nonzero exit code. -/
def fails : Check := fun _ r => decide (r.exit ≠ 0)

/-- Stdout is `f i`. -/
def stdoutIs (f : Input → Bytes) : Check := fun i r => decide (r.stdout = f i)

/-- Stderr is `f i`. -/
def stderrIs (f : Input → Bytes) : Check := fun i r => decide (r.stderr = f i)

/-- Nothing on stderr. -/
def silent : Check := fun _ r => r.stderr.isEmpty

/-- No file changed: every recorded change leaves the file as it was. -/
def keepsFiles : Check := fun i r => r.changes.all fun e => decide (r.fs i e.1 = i.fs e.1)

/-- All of stdin consumed. -/
def consumesAll : Check := fun i r => decide (r.consumed = i.stdin.length)

/-- Print `f i` and succeed, no file changed. -/
def prints (f : Input → Bytes) : Check := (succeeds.and (stdoutIs f)).and keepsFiles

/-- The pure program `f`: its outputs and exit code, no file read or changed. -/
def pure (f : Input → Spec.Out) : Check := fun i r =>
  decide (r.stdout = (f i).stdout) && decide (r.stderr = (f i).stderr) &&
    decide (r.exit = (f i).exit) && keepsFiles i r && r.reads.isEmpty &&
    decide (r.consumed ≤ i.stdin.length)

/-- **`c`, or a failure** after a prefix of `out i`: decides `orFail S` when `c` decides `S`
and `S` fixes stdout to `out`. -/
def orFail (out : Input → Bytes) (c : Check) : Check := fun i r =>
  c i r || (decide (r.exit ≠ 0) && r.stdout.isPrefixOf (out i))

/-- **`c`, or output lost to a refusal**: decides `orRefused S` when `c` decides `S` and `S`
fixes stdout and exit code to `out` and `code`. -/
def orRefused (out : Input → Bytes) (code : Input → ExitCode) (c : Check) : Check := fun i r =>
  c i r || (r.refused && r.stdout.isPrefixOf (out i) &&
    (decide (r.exit = code i) || decide (r.exit ≠ 0)))

end Check

end Silmaril.Cli
