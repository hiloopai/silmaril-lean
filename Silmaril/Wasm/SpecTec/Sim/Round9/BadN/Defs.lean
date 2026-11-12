module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, RE: `BadFwdE` at `vload-pack-val` (definitions)

`vload-pack-val` is in `BadFwdE` only because its first premise iterates as `^(k<M)` (a `listN`
iteration with an index), which round 8's `NxDer.dpremB_fwd` does not handle:

```
-- (if $ibytes_(K, j) = $mem(z, x).BYTES[i + ao.OFFSET + k * K/8 : K/8])^(k<M)
```

* `premN pr`: a premise of `NxStep.premS` that is not a `Step`/`Step_read` premise, or such an
  iteration `pr'^(k<eₙ)` over a body that iterates over lists only (`NxDer.listIter`) and has no
  `otherwise`, passing round 3's check.
* `goodRuleN`: the conclusion passes round 3's check and every premise passes `premN`.
* `stepBadN`, `BadFwdN`: `ElseBwd.stepBadE` and `ElseBwd.BadFwdE` at the rules that also fail
  `goodRuleN` (seven in the fixed script, `Round9.BadN.stepBadN_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadN

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

/-- **An indexed list iteration** `pr^(k<eₙ)` over a body that iterates over lists only and has
no `otherwise`. -/
def iterN : Prem → Bool
  | .iterPr pr (.mk (.listN _ _) _) => Round8.NxDer.listIter pr && !Round8.NxElse.elseIn pr
  | _ => false

/-- **A premise of a checked rule, indexed iterations allowed.** -/
def premN (pr : Prem) : Bool :=
  (Round8.NxStep.premS pr && !stepPremB pr) ||
    (iterN pr && EraseAll.xPrem EraseAll.grE EraseAll.gdE pr)

/-- **A rule passes the check with indexed iterations allowed.** -/
def goodRuleN : Rule → Bool
  | .ruleD _ _ _ e prems =>
    (Round6.Reading.conclAlts e).all (EraseAll.xExp EraseAll.grE EraseAll.gdE) && prems.all premN

/-- The `Step`/`Step_read` rules of `m` that fail `goodRule`, `goodRuleE` and `goodRuleN`. -/
def stepBadN (m : Map RelDef) : List String :=
  m.flatMap fun p => if !Round8.NxStep.stepRel p.1 then [] else p.2.2.2.2.filterMap fun r =>
    match r with
    | .ruleD nm _ _ _ _ =>
      if Round8.NxStep.goodRule r || goodRuleE r || goodRuleN r then none
      else some (p.1 ++ "/" ++ nm)

/-- **`ElseBwd.RuleAtE` at a rule that also fails `goodRuleN`.** -/
def RuleAtN (env : Env) (O : ElseI) (x : IL.Id) (op : MixopS) (args : List ArgV) (i : Nat)
    (v : Value) : Prop :=
  ∃ (ps : List Param) (t : Typ) (rules : List Rule) (nm : IL.Id) (qs : List Param) (e e' : Exp)
    (prems : List Prem) (ρ₀ : VarEnv) (σ : List (IL.Id × Value)),
    env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some (.ruleD nm qs op e prems) ∧
    Round8.NxStep.goodRule (.ruleD nm qs op e prems) = false ∧
    goodRuleE (.ruleD nm qs op e prems) = false ∧
    goodRuleN (.ruleD nm qs op e prems) = false ∧ e' ∈ Round6.Reading.conclAlts e ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧ QuantsOk env (ρ₀.bindVals σ) qs ∧
    EvalExp env (ρ₀.bindVals σ) e' v ∧
    ∀ pr ∈ prems, Round6.Reading.DPremB env O (O x args i v) (ρ₀.bindVals σ) pr

/-- **`BadFwdE` at the rules that fail `goodRuleN` too** (seven in the fixed script). -/
def BadFwdN (env : Env) : Prop :=
  ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value},
    Round8.NxStep.stepRel x = true →
    RuleAtN env (Round6.Reading.otherwiseB env) x op args i v →
    Round6.Reading.DDerivesB env (Round6.Reading.otherwiseB env) x op (args.map Swap.eraseA)
      (Swap.eraseV v)

end Silmaril.Wasm.SpecTec.Sim.Round9.BadN
