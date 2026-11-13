module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFire
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: rule 46 of `Step_pure` in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem hasRuleAt_vextractLaneNum20V (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 46 vextractLaneNumRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecFix
