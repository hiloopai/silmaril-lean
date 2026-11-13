module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: the `num_` and `$sizenn` lookups in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_num20V : ∃ ps qs qs', (simEnv20V B).findTyp? "num_" = some (ps,
    [.instD qs [.expA Pure.innPat20] (.aliasT (.varT "iN" [.expA (.callE "sizenn" [.expA Pure.innPat20])])),
     .instD qs' [.expA Pure.fnnPat] (.aliasT (.varT "fN" [.expA (.callE "sizenn" [.expA Pure.fnnPat])]))]) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_sizenn20V : (simEnv20V B).findDef? "sizenn" = Sim.IntNumeric.defOf Original.d88 := rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
