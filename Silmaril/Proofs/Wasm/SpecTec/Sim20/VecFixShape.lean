module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixShapeI

/-!
# The vector errata: shapes and signs are typed in `simEnv20V B` (by evaluation)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV)

variable {B : Builtins}

/-! ## Shapes and signs -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **Every V2 shape is a `shape` of `simEnv20V B`** (by evaluation). -/
theorem typedV_shape20V (s : Shape) : TypedV (simEnv20V B) (.varT "shape" []) (shapeV s) := by
  refine typedV_of_hasTyp_true (n := 40) ?_
  rcases s with s | s
  · exact hasTyp_shapeInt20V s
  · rcases s <;> with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- Every sign is an `sx` of `simEnv20V B` (by evaluation). -/
theorem typedV_sx20V (sx : Signedness) : TypedV (simEnv20V B) (.varT "sx" []) (sxV sx) := by
  refine typedV_of_hasTyp_true (n := 10) ?_
  rcases sx <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
