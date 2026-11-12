module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# The vector errata: the `u8` lookup in `simEnv20V B` (kernel `rfl`)
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
theorem findTyp_u8_20V : (simEnv20V B).findTyp? "u8" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 8))]))]) := rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
