module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckStep

/-!
# Round 7, moving derivations across erasure: the check on `Step`'s grow rules

One kernel computation (`decide +kernel`, `xGrowOk_fixed`): the rules `table.grow-succeed` and
`memory.grow-succeed` of `Step` have a conclusion with a single reading, of the shape
`(l, (%;% ($W(z, y₂, y₃), r)))` with `W` one of `$with_tableinst`, `$with_meminst` and `l`, `r`
passing the evaluator-level check at `grB`, `gdB`; a quantifier `z : state`; and premises that
pass the check and have no `otherwise`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grB gdB xPrem xExp)

/-- The grow rules of `Step`. -/
def growNames : List String := ["table.grow-succeed", "memory.grow-succeed"]

/-- The conclusion shape of a grow rule. -/
def growShape : Exp → Bool
  | .tupE [l, .caseE "%;%" (.tupE [.callE w [.expA (.varE "z"), .expA (.varE _), .expA (.varE _)],
      r])] =>
    (w == "with_tableinst" || w == "with_meminst") && xExp grB gdB l && xExp grB gdB r
  | _ => false

/-- The quantifiers declare `z : state`. -/
def hasStateZ (qs : List Param) : Bool :=
  qs.any fun q => match q with
    | .expP "z" (.varT "state" []) => true
    | _ => false

/-- **The check on a grow rule.** -/
def xGrowRule : Rule → Bool
  | .ruleD nm qs _ e prems =>
    !growNames.contains nm || (!Round6.Reading.hasOptNil e && growShape e && hasStateZ qs &&
      prems.all fun pr => xPrem grB gdB pr && noElseP pr)

set_option maxRecDepth 100000 in
/-- **The grow rules of `Step` pass the check.** -/
theorem xGrowOk_fixed :
    Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all
      (fun d => (relsOfDef d).all fun p => p.1 != "Step" || p.2.2.2.2.all xGrowRule) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
