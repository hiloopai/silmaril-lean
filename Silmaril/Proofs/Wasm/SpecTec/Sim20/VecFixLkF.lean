module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: `numtype` in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- Every number type is a `numtype` of `simEnv20V B` (by evaluation). -/
theorem typedV_numtype20V (t : Silmaril.Wasm.NumType) :
    Silmaril.Wasm.SpecTec.Sim.TypedV (simEnv20V B) (.varT "numtype" []) (numTypeV t) := by
  refine typedV_of_hasTyp_true (n := 10) ?_
  rcases t with (_ | _) | (_ | _) <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
