module

public import Silmaril.Wasm.Atlas.SpecTecR6.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Defs

/-!
# The SpecTec run charts at the round-7 reading

`Atlas.SpecTecR6` has run charts for round 6 (`runChart`, `readRunChart`), on sources whose
reachable configurations export nothing. This header fixes the domains of the round-7 run
transitions, where module instances may export names; `Atlas.SpecTecR7Runs.Thms` builds them
from `Round7.Runs.runsRE`.

* `RunDomE P host c`: `c` is valid and every configuration Core reaches from it is `BoundedSelE`
  and `StripInj` (`Round7.Runs.ReachE`).
* `RunDomDetE P host c`: `RunDomE`, and every reachable configuration has at most one Core
  successor.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7Runs

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

variable {H : Type}

/-- **The domain of the round-7 run corollary**: valid, with every reachable configuration
`BoundedSelE` and `StripInj`. -/
def RunDomE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Sim.Round7.Runs.ReachE P host c

/-- `RunDomE`, and every reachable configuration has at most one Core successor. -/
def RunDomDetE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  RunDomE P host c ∧ ∀ c', Steps P host c c' → SpecTecR6.StepDet P host c'

end Silmaril.Wasm.Atlas.SpecTecR7Runs
