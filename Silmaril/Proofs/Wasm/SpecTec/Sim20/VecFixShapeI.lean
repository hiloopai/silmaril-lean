module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# The vector errata: integer shapes are typed in `simEnv20V B` (by evaluation)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV)

variable {B : Builtins}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- Every integer shape is a `shape` (by evaluation). -/
theorem hasTyp_shapeInt20V (s : IntShape) :
    hasTyp 40 (simEnv20V B) VarEnv.empty (.varT "shape" []) (shapeV (.int s)) = .ok true := by
  rcases s <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
