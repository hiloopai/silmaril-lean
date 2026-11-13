module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixUN
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixU8

/-!
# The vector errata: lane indices are typed in `simEnv20V B`

`typedV_laneidx20V`: every V2 lane index is a `laneidx`, through the aliases `laneidx = u8 =
uN(8)` (the `laneidx` lookup is a kernel `rfl`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d17)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (instCases findCase quantFreeAt hasTypCase_of_findCase
  premsOk_if evalExp_and)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly TypedV)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_laneidx20V : (simEnv20V B).findTyp? "laneidx" =
    some ([], [.instD [] [] (.aliasT (.varT "u8" []))]) := rfl

/-- **Every V2 lane index is a `laneidx` of `simEnv20V B`.** -/
theorem typedV_laneidx20V (j : LaneIdx) :
    TypedV (simEnv20V B) (.varT "laneidx" []) (pctV j.val) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_uN20V (B := B)
  exact Whole.typedV_aliasG findTyp_laneidx20V (Whole.typedV_aliasG findTyp_u8_20V
    (hasTyp_uN_of htd evalExp_num j.isLt) _ ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim20.VecFix
