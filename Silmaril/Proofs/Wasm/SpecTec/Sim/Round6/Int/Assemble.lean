module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Refute.Thms

/-!
# SpecTec ↔ Core 3.0, round 6, integration: assembly

* `not_wholeStepValidR_declarative`: the restated target is **false at round 5's reading**
  `Target.declarative`; its backward half fails at `testCfg`
  (`Refute.not_backwardSel_testCfg`). So the reading parameter matters.
* `wholeStepValidR_backend_of_open`: the target at the backend reading, from track target's two
  leaves (`Target.OpenR`) at that reading.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Int

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

/-- **`Round6.Task.wholeStepValidR` is false at round 5's declarative reading**: at
`ref.null; ref.test (ref null any)`, `SStep` reaches `i32.const 0` in every `simEnv B`, and Core
only `i32.const 1`. -/
theorem not_wholeStepValidR_declarative : ¬ Round6.Task.wholeStepValidR Target.declarative :=
  fun h => by
    obtain ⟨B, -, hb⟩ := h Unit Round5.Pos.hnU Round5.Pos.hnU_injective Round5.Pos.divHost
      Round5.Pos.hostFinite_divHost Round5.Pos.hostOk_divHost false {}
    exact Refute.not_backwardSel_testCfg B _ Round5.Pos.divHost Round5.Pos.hnU hb

/-- **The target at the backend reading**, from the transfer lemma and the cast leaf at it. -/
theorem wholeStepValidR_backend_of_open
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Target.OpenR backend hn (Profile.spec nd r) host) :
    Round6.Task.wholeStepValidR backend :=
  Target.wholeStepValidR_of_open backend h

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
