module

public import Silmaril.Wasm.Institution.Games.Defs
public import Silmaril.Proofs.Wasm.Institution.Games.Basic
public import Silmaril.Proofs.Wasm.Institution.Games.Wasm

@[expose] public section

/-!
# Reduction semantics versus game semantics: results

Proofs in `Silmaril.Proofs.Wasm.Institution.Games.{Basic,Wasm}`.

* `valid_leSen_iff`, `valid_top_iff`: validity of `p ⊑ q` is refinement of the (restricted)
  denoted strategies. `valid_of_top`: refinement at the top interface is valid at every
  interface (hiding is monotone, `Strategy.restrict_mono`).
* `valid_red_top_iff_traces`: in the reduction logic, `p ⊑ q` is valid iff every legal trace
  of `red p` is a play of `ofReduction (red q)`.
* **Simulation gives valid sentences, borrowed across the edge**: `valid_of_simulation`
  (`Reduction.Simulation (red p) (red q)` ⇒ `p ⊑ q` valid at every interface of the reduction
  logic) and `valid_game_of_simulation` (⇒ the translated sentence is valid in the game logic,
  by `Translation.valid_iff` along `redToGame`); `valid_game_of_ltsSimulation` for transition
  systems.
* `mem_ofReduction_ask_ans`: a two-move play "ask `q`, answer `b`" is in `ofReduction R` iff
  `R.start q` reduces internally to a configuration answering `b`.
* **Grounded in Wasm Core**: `mem_wasmRed_iff`: for a non-divergent `b`, the two-move play
  invoking export `x` on `vs` and answering `b` is in the strategy of `wasmRed P host w` iff `b`
  is a Core 3.0 behaviour of that invocation (`instEntry`). `finite_beh_of_le`: game refinement
  of instantiated modules implies inclusion of their finite single-invocation behaviours.
-/
