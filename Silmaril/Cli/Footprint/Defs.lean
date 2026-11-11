module

public import Silmaril.Cli.Behaviour.Defs

/-!
# File footprints: when the pipe is the sequential pipe

`pipe S T` (`Silmaril.Cli.Behaviour`) lets the file events of its two programs interleave in any
order that replays from the files before the pipe; `pipeSeq S T` runs `S`'s file effects first
and logs them first. `pipeSeq ≤ pipe` holds for logged specs (`pipeSeq_le_pipe`). This module
gives the converse when the two programs' footprints are apart (`docs/projects/cli.md`).

* `FileEv.path`, `FileEv.isWrite`; **`FileEv.Indep e₁ e₂`**: the events commute (different
  paths, or both reads). `Apart l₁ l₂`: every event of `l₁` commutes with every event of `l₂`.
* **`Spec.Separate S T`**: the footprints of `S` and `T` are apart: every log `S` allows is
  apart from every log `T` allows (no path written by one is read or written by the other;
  shared read-only files are fine). `Spec.Within P S`: every event `S` logs is on a path in
  `P`; specs within disjoint path sets are separate (`separate_of_within`).
* **`Spec.Framed S`**: `S` depends on the files only through its log: a run on some files whose
  log replays from other files is a run on those files too, ending in the replayed files. Pure
  programs and programs that log their whole-file reads and writes are framed.
* **`Spec.relog S`**: `S` with its file log reordered (a permutation). `pipe` and `pipeSeq` can
  only agree up to the order of the log: their logs differ even for separate specs
  (`Silmaril.Cli.Footprint.Examples`: the pipe may log `T`'s write first). `Spec.LogBlind U`
  (`relog U ≤ U`): `U` does not care about that order; specs that do not mention the log are
  log-blind.

The theorems (`Silmaril.Cli.Footprint.Thms`): `Fs.replay_interleave` (an interleaving of apart
logs replays as their concatenation) and **`pipe_le_pipeSeq`** (`pipe S T ≤ relog (pipeSeq S
T)` for framed, separate specs), with `relog_pipe_eq` and `pipe_le_of_pipeSeq`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

namespace FileEv

/-- The path of a file event. -/
def path : FileEv → FPath
  | .read p _ => p
  | .write p _ => p

/-- The event is a write. -/
def isWrite : FileEv → Bool
  | .read _ _ => false
  | .write _ _ => true

/-- **Two file events commute**: they are on different paths, or both are reads. -/
def Indep (e₁ e₂ : FileEv) : Prop :=
  e₁.path ≠ e₂.path ∨ (e₁.isWrite = false ∧ e₂.isWrite = false)

end FileEv

/-- **Apart logs**: every event of `l₁` commutes with every event of `l₂`. -/
def Apart (l₁ l₂ : List FileEv) : Prop := ∀ e₁ ∈ l₁, ∀ e₂ ∈ l₂, e₁.Indep e₂

namespace Spec

/-- **Separate file footprints**: every log `S` allows is apart from every log `T` allows. -/
def Separate (S T : Spec) : Prop :=
  ∀ i₁ o₁ i₂ o₂, S i₁ o₁ → T i₂ o₂ → Apart o₁.log o₂.log

/-- **`S` logs only paths in `P`.** -/
def Within (P : FPath → Prop) (S : Spec) : Prop := ∀ i o, S i o → ∀ e ∈ o.log, P e.path

/-- **`S` depends on the files only through its log**: a run on some files whose log replays from
the files `fs` (to `f`) is a run on `fs`, ending in `f`. -/
def Framed (S : Spec) : Prop :=
  ∀ i o fs f, S i o → fs.replay o.log = some f → S { i with fs := fs } { o with fs := f }

/-- **`S` with its file log reordered.** -/
def relog (S : Spec) : Spec := fun i o => ∃ l, S i { o with log := l } ∧ l.Perm o.log

/-- **`U` does not care about the order of the file log.** -/
def LogBlind (U : Spec) : Prop := relog U ≤ U

end Spec

end Silmaril.Cli
