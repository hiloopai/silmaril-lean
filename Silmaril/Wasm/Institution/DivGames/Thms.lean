module

public import Silmaril.Wasm.Institution.DivGames.Defs
public import Silmaril.Proofs.Wasm.Institution.DivGames.Basic

@[expose] public section

/-!
# Reading Wasm observations off divergence- and instantiation-observing games

Proofs in `Silmaril.Proofs.Wasm.Institution.DivGames.Basic`.

## Entry observations (single invocations), divergence included

* `div_wasmRed_iff`: the divergence-observing strategy of `wasmRed P host w`
  may diverge right after invoking `x` on `vs` iff `.diverges` is a Core 3.0
  behaviour of that invocation (`instEntry`).
* `behOf_wasmRed`: **all** single-invocation behaviours, `.diverges`
  included, are read off the strategy:
  `behOf (DStrategy.ofReduction (wasmRed P host w)) ⟨(x, vs), _⟩ =
  (instEntry P host).beh w x vs`. This removes the restriction
  `b ≠ .diverges` of `Silmaril.Wasm.Institution.Games.mem_wasmRed_iff`.
* `beh_subset_of_le`: refinement of the divergence-observing strategies of
  instantiated modules implies inclusion of all their single-invocation
  behaviours (the `Eq` case of `Behaviours.Refines`, divergence included);
  this extends `finite_beh_of_le`. The converse is the frozen
  `Task.wasmRed_dle_of_beh` (not proved).

## Instantiation observations

* `instReady_wasmInst`, `instFails_wasmInst`, `instDiverges_wasmInst`: the
  instantiation outcomes of the strategy of `wasmInst P host s xas m` are
  those of silmaril's instantiation run (`Instantiate`, then `Steps`): ready
  with empty code, failure with a non-empty result, divergence.
* `instObs_wasmInst`: `instObs (DStrategy.ofInst (wasmInst P host s xas m)) =
  moduleObs P host s xas m []`: the session observations of the empty
  script, i.e. the outcome of instantiation, are read off the game.

## Comorphisms (see `Silmaril.Wasm.Institution.DivGames.{Graph,Edges}`)

* Done:
  - a divergence-aware game logic (`dstratSem`, `divGame`, `divRed`);
  - the comorphisms `entryToRed` (entry logic of instantiated modules with
    every invocation observed → divergence-aware Wasm reduction logic) and
    `redToGame`;
  - the graph `divGraph`, and `fullGraph₃` (the sum with
    `GameGraph.fullGraph`).
* **Forgetful edge to the plain game logic.** Not done. A comorphism from
  `gameSem exportIfaces E` into `divGame` (with `sem X δ` the restriction of
  `δ.forget` to `X`, `prog := ofStrategy`, `t ⊑ u ↦ t ⊑ chaos u` by
  `gc_forget_chaos`) needs `Strategy.restrict σ (exportIfaces.hom f)` to
  consist exactly of the scoped plays of `σ`, renamed. That characterization
  of the old reduct is not proved.
* **Entry logic of uninstantiated modules.** `moduleEntryPoints` takes a
  union over the instantiations allowed by `Env`; the games here are per
  instantiated module. The `Ok` premise is replaced by `True` in
  `instEntryAll`.
* **Session logic → divergence-aware games.** `wasmInst` keeps the store
  across export calls and has an instantiation phase, so its plays contain the
  whole session. Still missing:
  - a reading of scripts of length > 0 (`sessionObs`), and its adequacy
    against `moduleObs`. This needs a characterization of all plays of
    `ofInst (wasmInst …)` as sequences of exchanges (the analogue of
    `Games.Task.wasmRed_le_of_finite_beh`);
  - a counterpart of silmaril's `Session.stop` (an ill-formed request ends
    the session with nothing observed). `wasmInst` invokes any existing
    export without checking `InvokeOk`, and a refused call is unobservable in
    this may-model, so the export answers would have to report ill-formed
    requests, e.g. as `Option (Behaviour Val)`;
  - the instantiability predicate `inst` of session objects
    (`∃ c, Instantiate …`): it is not observable when the instantiation run
    gets stuck (neither a result nor divergence).
* Host calls are still not game moves: the lower signature is
  `Sig.empty` and host functions run inside `Step` (as in `wasmRed`).
-/

namespace Silmaril.Wasm.Institution.DivGames

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Games Silmaril.Wasm.Institution.Games

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- **Refinement of divergence-observing strategies of instantiated modules
implies inclusion of all their single-invocation behaviours, divergence
included.** -/
theorem beh_subset_of_le {w w' : Inst H}
    (h : DStrategy.ofReduction (wasmRed P host w) ≤ DStrategy.ofReduction (wasmRed P host w'))
    (x : String) (vs : List Val) :
    (instEntry P host).beh w x vs ⊆ (instEntry P host).beh w' x vs := by
  rw [← behOf_wasmRed, ← behOf_wasmRed]
  exact behOf_mono h _

/-- **Open, not proved (frozen statement).** The converse of
`beh_subset_of_le`: inclusion of all single-invocation behaviours implies
refinement of the divergence-observing strategies. It needs a
characterization of the finite plays, divergences and infinite plays of
`DStrategy.ofReduction (wasmRed P host w)` as sequences of independent
exchanges. Nothing depends on it. -/
def Task.wasmRed_dle_of_beh : Prop :=
  ∀ w w' : Inst H, (∀ x vs, (instEntry P host).beh w x vs ⊆ (instEntry P host).beh w' x vs) →
    DStrategy.ofReduction (wasmRed P host w) ≤ DStrategy.ofReduction (wasmRed P host w')

end Silmaril.Wasm.Institution.DivGames
