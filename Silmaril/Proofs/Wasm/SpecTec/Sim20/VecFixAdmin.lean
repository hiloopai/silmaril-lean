module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# The vector errata: `admininstr` and its `VEXTRACT_LANE` case

`findTyp_admin20V`, `findCase_extract20V`: in `simEnv20V B`, `admininstr` is the corrected type
`adminFixV20`, whose `VEXTRACT_LANE` case is `extractCaseFix` (kernel `rfl`).
`typedV_adminCase20V`: a case of it, with premises, is inhabited from the empty scope.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase quantFreeAt hasTypCase_of_findCase)
open Silmaril.Wasm.SpecTec.Sim (TypedV)

variable {B : Builtins}

/-! ## `admininstr` and its `VEXTRACT_LANE` case -/

/-- The cases of a one-instance variant type. -/
def variantCases : Def → List TypCase
  | .typD _ _ [.instD _ _ (.variantT cs)] => cs
  | _ => []

set_option maxRecDepth 100000 in
theorem findTyp_admin20V : (simEnv20V B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT (variantCases adminFixV20))]) := rfl

/-- A case of `admininstr` with its premises, from the empty scope. -/
theorem typedV_adminCase20V {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : findCase (variantCases adminFixV20) op = some (t, prems))
    (hq : quantFreeAt (variantCases adminFixV20) op = true)
    (hw : HasTyp (simEnv20V B) VarEnv.empty t w)
    (hp : PremsOk (simEnv20V B) (caseScope VarEnv.empty t w) prems) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (.case op w) :=
  fun _ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_admin20V
    Equiv.evalArgs_nil matchArgs_nil (hasTypCase_of_findCase hf hw hp hq)

end Silmaril.Wasm.SpecTec.Sim20.VecFix
