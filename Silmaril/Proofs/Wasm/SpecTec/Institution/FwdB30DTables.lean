module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30D.Defs
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The right-hand-side table of `Step`, against the pinned script

`stepRhsT` is `rhsLen` on every rule of `Step` of the pinned wasm-3.0 script (kernel `rfl`), and
so of `simEnv B` for every `B` (`RefsGC.relRules_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules relRules_simEnv)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `stepRhsT` is the right-hand-side table of `Step`. -/
theorem stepRhsT_eq :
    (relRules (envOfScript Specs.wasm30) "Step").map rhsLen = stepRhsT := by
  rfl

/-- The table in `simEnv B`. -/
theorem rhsT_simEnv (B : Builtins) : (relRules (simEnv B) "Step").map rhsLen = stepRhsT := by
  simp only [relRules_simEnv]
  exact stepRhsT_eq

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
