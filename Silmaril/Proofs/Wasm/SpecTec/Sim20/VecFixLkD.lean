module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: the `Inn` subtype test, `N` and `$lanes_` in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- An integer type passes the `Inn` pattern's subtype test. -/
theorem argSubOk_inn_int20V (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv20V B) VarEnv.empty
      (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])) (numTypeV (.int t)) = true := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem findTyp_N20V : (simEnv20V B).findTyp? "N" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

set_option maxRecDepth 100000 in
theorem findDef_lanes20V : ∃ ps t, (simEnv20V B).findDef? "lanes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecFix
