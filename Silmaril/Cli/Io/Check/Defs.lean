module

public import Silmaril.Cli.Io.Examples.Defs

/-!
# Checking runs of binaries against behaviour specifications

What a test harness sees of a run (`Snap`): stdout, stderr, the exit code and the files under
the working directory that are new or changed afterwards (by path components). It does not see
how much stdin was consumed, which files were read, or whether the environment refused
something, and it does not see deletions. `Snap.Agrees s i o`: the observation `o` of the
behaviour model shows `s` on `i` (the files outside `"."` are `i`'s).

A **check** is a decidable test of a snapshot, `Check := Input → Snap → Bool`.
`Check.Sound c S`: a snapshot the check passes is shown by an observation that `S` allows. So a
binary that passes a sound check on a case has, as far as the harness can see, a run that the
specification allows. The checks of the example programs and their soundness are in
`Silmaril.Cli.Io.Check.Thms`; `Silmaril.Cli.Io.Run` runs binaries and applies them.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io

open Silmaril.Cli

/-- **What a harness sees of a run.** -/
structure Snap where
  /-- Stdout. -/
  stdout : Bytes := []
  /-- Stderr. -/
  stderr : Bytes := []
  /-- The exit code. -/
  exit : ExitCode := 0
  /-- The files under `"."` that are new or changed, by path components, with their contents. -/
  files : List (List String × Bytes) := []
deriving Repr, DecidableEq, Inhabited

/-- The files after a run as a harness sees them: the changed files under `"."`, else `i`'s. -/
def Snap.fs (s : Snap) (i : Input) : Fs := fun q =>
  if q.root = "." then ((s.files.lookup q.rel).map some).getD (i.fs q) else i.fs q

/-- **The observation `o` shows the snapshot `s`** on `i`. -/
def Snap.Agrees (s : Snap) (i : Input) (o : Obs) : Prop :=
  o.stdout = s.stdout ∧ o.stderr = s.stderr ∧ o.exit = s.exit ∧ o.fs = s.fs i

/-- A decidable test of what a harness sees. -/
abbrev Check : Type := Input → Snap → Bool

/-- **The check `c` is sound for `S`**: what it passes is shown by an allowed observation. -/
def Check.Sound (c : Check) (S : Spec) : Prop :=
  ∀ i s, c i s = true → ∃ o, s.Agrees i o ∧ S i o

/-! ## Checks of the examples -/

namespace Examples

/-- `echo`'s check. -/
def echoCheck : Check := fun i s =>
  s.exit == 0 && s.stdout == echoOut i.args && s.stderr.isEmpty && s.files.isEmpty

/-- `cat`'s check. -/
def catCheck : Check := fun i s =>
  s.exit == 0 && s.stdout == i.stdin && s.stderr.isEmpty && s.files.isEmpty

/-- What `copy` must leave at `d` (relative to `"."`): nothing reported when the file was there
already with the same contents. -/
def copyFiles (i : Input) (d : FPath) (b : Bytes) : List (List String × Bytes) :=
  if i.fs d = some b then [] else [(d.rel, b)]

/-- `copy`'s check: a failure as `Spec.failure` allows it, or the copy. -/
def copyCheck : Check := fun i s =>
  s.stdout.isEmpty &&
  match copyArgs i.args with
  | none => s.exit != 0 && !s.stderr.isEmpty && s.files.isEmpty
  | some (src, dst) =>
    match i.fileAt src, i.resolve dst with
    | none, _ => s.exit != 0 && !s.stderr.isEmpty && s.files.isEmpty
    | some b, some d =>
      d.root == "." && decide (i.Writable d) && s.exit == 0 && s.stderr.isEmpty &&
        s.files == copyFiles i d b
    | some _, none => false

end Examples

end Silmaril.Cli.Io

end
