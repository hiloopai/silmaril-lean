module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, integration: the backend reading

Integration of round 6 (`docs/projects/spectec/README.md`). Track target states
`Round6.Task.wholeStepValidR` over an abstract `Target.Reading`; track reading defines the
backend-style reading `Reading.SStepB` (an empty-domain `e?` in a rule conclusion denotes `none`
or `some e`). `backend` is that reading as a `Target.Reading`: the one the round-6 target is to be
proved for.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Int

open Silmaril.SpecTec.Sem

/-- **The backend reading** of SpecTec's whole-machine `Step`: `DDerivesB` with `otherwiseB`, on
`simEnv B` (`Round6.Reading.SStepB`). -/
def backend : Target.Reading := ⟨fun B => Reading.SStepB (simEnv B)⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
