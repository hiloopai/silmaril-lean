module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: the `iN` and `$size` lookups in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_iN20V : ∃ ps qs, (simEnv20V B).findTyp? "iN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.aliasT (.varT "uN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_size20V : (simEnv20V B).findDef? "size" = Sim.IntNumeric.defOf Original.d82 := rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
