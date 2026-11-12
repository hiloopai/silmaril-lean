module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: runs at the round-7 reading (round 5, pass 1)

`Round7.EraseDer.wholeStepValidREI_holds` is a one-step theorem at a valid configuration `c`.
Its backward half gives a SpecTec successor `configV hn d'` with `d'` related to a Core successor
`c'` only up to `Bwd.ConfigEq` (call annotations), so a run of SpecTec continues from the image
of a *witness* `d'`, not from that of a valid configuration. Round 6 met the same issue and
threaded the relation `Round4.SimRel` (`ConfigEq` and typing of the witness) through its runs
(`Round6.Target.runsR_of_open`).

This header states what the round-7 runs thread:

* `RelE B hn c d`: `d` is a `ConfigEq` witness of `c`, and the stripped witness
  `stripConfig d` is typed in `simEnv B`. Then round 6's `SimRel` holds between `stripConfig c`
  and `stripConfig d`, which is what round 6's relational steps need.
* `ReachE P host c`: every configuration Core reaches from `c` is `BoundedSelE` and `StripInj`.
  It is the run form of the domain `Atlas.SpecTecR7.DomE`.

The theorems (`Round7.Runs.runsRE`) are stated in `Round7.Runs.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The relation the round-7 runs thread**: `d` is a call-annotation witness of `c`, and its
stripped form is typed in `simEnv B`. -/
def RelE (B : Builtins) (hn : H → String) (c d : Config H) : Prop :=
  Bwd.ConfigEq c d ∧ Typed (simEnv B) hn (stripConfig d)

/-- **Every configuration Core reaches from `c` is `BoundedSelE` and `StripInj`.** -/
def ReachE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Steps P host c c' → BoundedSelE c' ∧ StripInj c'

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
