module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Sites.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 7, moving derivations across erasure: the check on `Step`'s rules

`Step` is outside the checked part `grB` for two reasons: its context rules have `Step` premises,
and four rules use the excluded names (`excNames`): `call_ref-hostfunc-res`/`-div` test
`$hostcall`, `table.grow-succeed`/`memory.grow-succeed` call `$with_tableinst`/`$with_meminst`
in their conclusions. One kernel computation (`decide +kernel`, `xStepOk_fixed`): every other
rule of `Step` has conclusion alternatives that pass the evaluator-level check at `grB`, `gdB`,
and premises that are either a `Step` premise whose arguments and expression pass it, or a premise
that passes it outright and has no `otherwise`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grB gdB xPrem xExp xArgs)

/-- A premise has no `otherwise`. -/
def noElseP : Prem → Bool
  | .elsePr => false
  | .iterPr pr _ => noElseP pr
  | _ => true

/-- **The check on a premise of `Step`**: a `Step` premise with checked arguments and expression,
or a checked premise without `otherwise`. -/
def xPremS : Prem → Bool
  | .rulePr x args op e =>
    if x == "Step" then xArgs grB gdB args && xExp grB gdB e else xPrem grB gdB (.rulePr x args op e)
  | pr => xPrem grB gdB pr && noElseP pr

/-- **The check on a rule of `Step`**, outside `excNames`. -/
def xStepRule : Rule → Bool
  | .ruleD nm _ _ e prems =>
    excNames.contains nm || ((Round6.Reading.conclAlts e).all (xExp grB gdB) && prems.all xPremS)

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` outside `excNames` passes the check.** -/
theorem xStepOk_fixed :
    Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all
      (fun d => (relsOfDef d).all fun p => p.1 != "Step" || p.2.2.2.2.all xStepRule) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
