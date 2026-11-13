module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLanePack

/-!
# `I8` and `I16` are `packtype`s of `simEnv20V` (by evaluation)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V typedV_of_hasTyp_true)
open Silmaril.Wasm.SpecTec.Sim20.Whole (jnnV20)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem typedV_packtype20V {sz : Silmaril.Wasm.PackSize} (hp : Packed sz) :
    Silmaril.Wasm.SpecTec.Sim.TypedV (simEnv20V B) (.varT "packtype" []) (jnnV20 sz) := by
  refine typedV_of_hasTyp_true (n := 10) ?_
  rcases hp with rfl | rfl <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecLane
