module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Defs

/-!
# Round 8, `otherwise` across erasure: the `otherwise` rules of the checked relations

One kernel computation (`decide +kernel`): the rules that `elseLhs_fixed` constrains are seven,
all of `Step_pure`, so that check is not vacuous.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- The `otherwise` rules of `grE` relations, by name. -/
def elseRules (m : Map RelDef) : List String :=
  m.flatMap fun p => if !EraseAll.grE p.1 then [] else p.2.2.2.2.filterMap fun r => match r with
    | .ruleD nm _ _ _ prems => if prems.any elseIn then some (p.1 ++ "/" ++ nm) else none

set_option maxRecDepth 100000 in
/-- **There are seven of them, all of `Step_pure`.** The check above is not vacuous. -/
theorem elseRules_fixed : elseRules (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    ["Step_pure/br_on_null-addr", "Step_pure/br_on_non_null-addr", "Step_pure/ref.is_null-false",
     "Step_pure/ref.as_non_null-addr", "Step_pure/ref.eq-true", "Step_pure/ref.eq-false",
     "Step_pure/extern.convert_any-addr"] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
