module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixAdmin

/-!
# The vector errata: the corrected `VEXTRACT_LANE` case of `admininstr`

`findCase_extract20V`: the `VEXTRACT_LANE` case of `adminFixV20` is `extractCaseFix`, and it
defines no quantifier (by evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase quantFreeAt)

set_option maxRecDepth 100000 in
/-- **The corrected case**, which defines no quantifier. -/
theorem findCase_extract20V :
    findCase (variantCases adminFixV20) "VEXTRACT_LANE" = some (extractPayT, [extractPremFix]) ∧
      quantFreeAt (variantCases adminFixV20) "VEXTRACT_LANE" = true := by
  constructor <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
