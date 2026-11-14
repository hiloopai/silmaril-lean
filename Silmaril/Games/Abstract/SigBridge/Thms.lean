module

public import Silmaril.Games.Abstract.SigBridge.Defs
public import Silmaril.Games.Abstract.Machine.Thms
public import Silmaril.Games.LTS.Thms
public import Mathlib.Order.CompleteLattice.Basic
import Silmaril.Proofs.Games.Abstract.SigBridge.Basic

/-!
# The game `E ↠ F` as an abstract game: agreement with strategies

* `strategyIso` (in the definitions) is an order isomorphism between the
  strategies of `E ↠ F` and the trace models of `sigGame E F`: the generic
  closure conditions are exactly the strategy conditions.
* A transition system and its machine have the same runs and traces
  (`traces_ofLTS`), and the state-erasure square commutes
  (`strategyIso_ofLTS`): erasing the states of `L` as an abstract machine gives
  the strategy `Strategy.ofLTS L`, read as a trace model. Every result about
  existing LTS-based strategies (Wasm game semantics, instantiation systems)
  therefore transports to the generic layer.
* Meets, joins, `⊤` and `⊥` correspond (`strategyIso` is an order
  isomorphism of complete lattices).
-/

public section

namespace Silmaril.Games.Abstract

universe u

variable {E F : Sig.{u}}

/-- A transition system and its machine have the same runs. -/
theorem Machine.run_ofLTS_iff {L : LTS E F} {x y : (Machine.ofLTS L).State}
    {s : List (Silmaril.Games.Move E F)} : (Machine.ofLTS L).Run x s y ↔ L.Run x s y :=
  Silmaril.Proofs.Games.Abstract.SigBridge.run_ofLTS_iff

/-- A transition system and its machine have the same traces. -/
theorem Machine.traces_ofLTS (L : LTS E F) : (Machine.ofLTS L).traces = L.Traces :=
  Silmaril.Proofs.Games.Abstract.SigBridge.traces_ofLTS L

/-- State erasure agrees with `Strategy.ofLTS`. -/
theorem SigBridge.strategyIso_ofLTS (L : LTS E F) :
    SigBridge.strategyIso (Strategy.ofLTS L) = (Machine.ofLTS L).denote :=
  Silmaril.Proofs.Games.Abstract.SigBridge.strategyIso_ofLTS L

/-- Joins correspond. -/
theorem SigBridge.strategyIso_sSup (S : Set (Strategy E F)) :
    SigBridge.strategyIso (sSup S) = ⨆ σ ∈ S, SigBridge.strategyIso σ :=
  SigBridge.strategyIso.map_sSup S

/-- Meets correspond. -/
theorem SigBridge.strategyIso_sInf (S : Set (Strategy E F)) :
    SigBridge.strategyIso (sInf S) = ⨅ σ ∈ S, SigBridge.strategyIso σ :=
  SigBridge.strategyIso.map_sInf S

end Silmaril.Games.Abstract
