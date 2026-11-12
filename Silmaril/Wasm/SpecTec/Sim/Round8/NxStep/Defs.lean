module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Defs

/-!
# Round 8, REH: `Step` and `Step_read` go to the erased side, rule by rule

`Round8.NxElse.derFwdS` moves derivations of the checked relations (`EraseAll.grE`) across export
erasure under SpecTec's `otherwise`. `Step` and `Step_read` are outside `grE`. This topic moves
their derivations across, rule by rule, with no swap set, at every rule that passes a syntactic
check (`goodRule`), and states the remaining rules as explicit obligations (`BadFwd`).

* `stepRel x`: `x` is `Step` or `Step_read`.
* `premS pr`: a premise is either a relation premise of `Step`/`Step_read` whose arguments and
  expression pass round 3's `xExp` check, or a premise that passes round 3's `xPrem` check (so its
  relations are in `grE`), iterates over lists only, and is not `otherwise`.
* `goodRule r`: every conclusion alternative passes `xExp`, and every premise passes `premS`.
* `RuleAt env O x i v`: rule `i` of `x` derives `v` under the reading `O`, with its premises read
  by `DDerivesB env O` (the `rule` constructor of `Round6.Reading.DDerivesB`, at a named rule).
* `BadFwd env`: the obligation at the rules that fail `goodRule`. In the fixed script these are
  four rules of `Step` and 32 of `Step_read`, out of 36 and 103 (`Round8.NxStep.stepBad_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE xExp xArgs xPrem)

/-- `x` is `Step` or `Step_read`. -/
def stepRel (x : String) : Bool := x == "Step" || x == "Step_read"

/-- **A premise of a checked `Step`/`Step_read` rule.** -/
def premS : Prem → Bool
  | .rulePr y args op e =>
    if stepRel y then xArgs grE gdE args && xExp grE gdE e else xPrem grE gdE (.rulePr y args op e)
  | pr => xPrem grE gdE pr && NxDer.listIter pr && !NxElse.elseIn pr

/-- **A `Step`/`Step_read` rule passes the check.** -/
def goodRule : Rule → Bool
  | .ruleD _ _ _ e prems => (Round6.Reading.conclAlts e).all (xExp grE gdE) && prems.all premS

/-- The `Step`/`Step_read` rules of `m` that fail the check, as `relation/rule`. -/
def stepBad (m : Map RelDef) : List String :=
  m.flatMap fun p => if !stepRel p.1 then [] else p.2.2.2.2.filterMap fun r => match r with
    | .ruleD nm _ _ _ _ => if goodRule r then none else some (p.1 ++ "/" ++ nm)

/-- **Rule `i` of `x` derives `v`**, with premises read by `DDerivesB env O`. -/
def RuleAt (env : Env) (O : ElseI) (x : IL.Id) (op : MixopS) (args : List ArgV) (i : Nat)
    (v : Value) : Prop :=
  ∃ (ps : List Param) (t : Typ) (rules : List Rule) (nm : IL.Id) (qs : List Param) (e e' : Exp)
    (prems : List Prem) (ρ₀ : VarEnv) (σ : List (IL.Id × Value)),
    env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some (.ruleD nm qs op e prems) ∧
    goodRule (.ruleD nm qs op e prems) = false ∧ e' ∈ Round6.Reading.conclAlts e ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧ QuantsOk env (ρ₀.bindVals σ) qs ∧
    EvalExp env (ρ₀.bindVals σ) e' v ∧
    ∀ pr ∈ prems, Round6.Reading.DPremB env O (O x args i v) (ρ₀.bindVals σ) pr

/-- **The obligation at the rules that fail the check**: where such a rule of `Step` or
`Step_read` derives `v` under SpecTec's `otherwise`, the erased value is derived from the erased
arguments. -/
def BadFwd (env : Env) : Prop :=
  ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value}, stepRel x = true →
    RuleAt env (Round6.Reading.otherwiseB env) x op args i v →
    Round6.Reading.DDerivesB env (Round6.Reading.otherwiseB env) x op (args.map Swap.eraseA)
      (Swap.eraseV v)

end Silmaril.Wasm.SpecTec.Sim.Round8.NxStep
