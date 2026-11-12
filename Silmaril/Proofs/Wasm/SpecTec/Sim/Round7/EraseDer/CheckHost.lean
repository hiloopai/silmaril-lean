module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckStep

/-!
# Round 7, moving derivations across erasure: the check on `Step`'s host-call rules

One kernel computation (`decide +kernel`, `xHostOk_fixed`) about `call_ref-hostfunc-res` and
`call_ref-hostfunc-div`:

* the conclusion has a single reading and passes the evaluator-level check at `grB`, `gdB`;
* there are four premises `p₁ p₂ p₃ (if pat <- $hostcall(a₁, z, a₃))`; the first three pass the
  check, have no `otherwise` and are harmless for the mode analysis at the variables `K` that the
  mode analysis knows from the quantifiers, the conclusion's input and those three premises
  (`Determ.ruleK qs e [p₁, p₂, p₃]`);
* the pattern `pat` and the arguments of `$hostcall` pass the check, the free variables of the
  arguments are in `K`, and the store argument `z` is a quantifier `z : store`;
* every quantifier is in `K` or bound by the pattern (`Determ.invVars pat`): for `-res` these are
  `s'` and `result`, for `-div` none.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grB gdB xPrem xExp xArgs)

/-- The quantifiers declare `z : store`. -/
def hasStoreQ (z : IL.Id) (qs : List Param) : Bool :=
  qs.any fun q => match q with
    | .expP y (.varT "store" []) => y == z
    | _ => false

/-- The premises of a host-call rule. -/
def hostPrems (qs : List Param) (e : Exp) : List Prem → Bool
  | [p₁, p₂, p₃, .ifPr (.memE pat (.callE "hostcall" [a₁, .expA (.varE z), a₃]))] =>
    [p₁, p₂, p₃].all (fun pr => xPrem grB gdB pr && noElseP pr &&
        Determ.premDetOk (Determ.ruleK qs e [p₁, p₂, p₃]) pr) &&
      xExp grB gdB pat && xArgs grB gdB [a₁, .expA (.varE z), a₃] &&
      varsIn (Determ.ruleK qs e [p₁, p₂, p₃]) (freeArgs [a₁, .expA (.varE z), a₃]) &&
      hasStoreQ z qs && (Determ.ruleK qs e [p₁, p₂, p₃]).contains z &&
      (Determ.quantNames qs).all (fun x =>
        (Determ.ruleK qs e [p₁, p₂, p₃]).contains x || (Determ.invVars pat).contains x)
  | _ => false

/-- **The check on a host-call rule.** -/
def xHostRule : Rule → Bool
  | .ruleD nm qs _ e prems =>
    !hostNames.contains nm ||
      (!Round6.Reading.hasOptNil e && xExp grB gdB e && hostPrems qs e prems)

set_option maxRecDepth 100000 in
/-- **The host-call rules of `Step` pass the check.** -/
theorem xHostOk_fixed :
    Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all
      (fun d => (relsOfDef d).all fun p => p.1 != "Step" || p.2.2.2.2.all xHostRule) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
