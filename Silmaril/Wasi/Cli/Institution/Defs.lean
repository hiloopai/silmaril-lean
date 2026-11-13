module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Cli.Institution.Defs

/-!
# A `wasi:cli` component as a model of the CLI institution

`wasiModel σ T V` is the CLI semantics of a component `σ` of a WASI world, against the hosts
whose answers satisfy the theory `T i` on each invocation, read through the view `V`
(`Silmaril.Wasi.Cli`): a run on `i` is a play of `σ` whose host answers `T i` accepts, with at most
one call of `run`, that has ended (`V.code` is known); its observation is `V.obs i t`.

`CliSat σ T V S` is a statement about partial observations (`Spec.Partial`: what has been seen
extends to an allowed observation). On ended plays stdout, stderr, the exit code and the files are
exact, while consumption and files read are lower bounds and the file log is not read. So
`CliSat` makes the component a model of `S` up to those (`cliSat_sat`, `Thms`), and a model of
exactly `S` when `S` reads only stdout, stderr, the exit code and the files (`Spec.OutOnly`),
which holds of every sentence lifted from a level up to `L2` (`cliSat_lift`, `cliSat_liftAll`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Cli.Institution (Level Model)
open Silmaril.Wasm.Resource (Protocol)

/-- **The CLI model of a component** (level `L3`): its ended plays against the hosts of the
theory, with at most one run, as read by the view. -/
def wasiModel {W : World} {St : Type} (σ : W.Model) (T : Input → Protocol St WEv) (V : View) :
    Model Level.full.sig :=
  ⟨fun i o => ∃ s, s ∈ σ ∧ (T i).Accepts (hostView (wtrace s)) ∧ calls V.run (wtrace s) ≤ 1 ∧
    (V.code (wtrace s)).isSome ∧ o = V.obs i (wtrace s)⟩

/-- **A spec that reads only stdout, stderr, the exit code and the files.** -/
def _root_.Silmaril.Cli.Spec.OutOnly (S : Spec) : Prop :=
  ∀ i (o o' : Obs), o.stdout = o'.stdout → o.stderr = o'.stderr → o.exit = o'.exit →
    o.fs = o'.fs → S i o' → S i o

end Silmaril.Wasi.Cli
