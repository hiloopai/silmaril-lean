module

public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: moving derivations with `ExpFree` quantifiers (round 2, pass 2)

`Round7.dderivesB_utf8Env` moves positive derivations from `simEnv B` to `utf8Env B`. The
converse needs the typing agreement `Round7.TypAgree.quantsOk_utf8Env_iff`, which holds at
quantifier values that are `ExpFree`. This header names the derivations where that is so, and
one kernel check on the script.

* `DDerivesBE env O`, `DPremBE env O`: `Round6.Reading.DDerivesB`/`DPremB` with, at every rule
  instance, every expression quantifier bound to an `ExpFree` value. Forgetting the side
  condition gives a `DDerivesB` derivation (`Round7.Transfer.dderivesB_of_E`).
* `relRulesOk m`: every relation of `m` that `Step` reaches has no parameters, and every
  alternative of each rule's conclusion (`Round6.Reading.conclAlts`) and each rule's premises
  refer only to reachable definitions other than `$utf8` and to reachable relations
  (`goodEvsB`). The kernel checks it for the fixed wasm-3.0 script
  (`Round7.Transfer.relRulesOk_fixed`).

**Determination** — that every `utf8Env B` derivation of SpecTec's `Step` from an `ExpFree`
configuration is a `DDerivesBE` derivation — is not stated or proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (stepReach evExp evPrems)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree goodEvsB)
open Round6.Reading (conclAlts)

/-- The rules of a reachable relation are checked: no parameters, harmless conclusions (every
alternative) and premises. -/
def rulesOk (rules : List Rule) : Bool :=
  rules.all fun r => match r with
    | .ruleD _ _ _ e prems =>
        (conclAlts e).all (fun e' => goodEvsB (evExp e')) && goodEvsB (evPrems prems)

/-- **Every relation `Step` reaches is checked.** -/
def relRulesOk (m : Map RelDef) : Bool :=
  m.all fun p => !stepReach.contains (0, p.1) || (p.2.1.isEmpty && rulesOk p.2.2.2.2)

/-- Every expression quantifier of `qs` is bound in `ρ` to an `ExpFree` value, if bound. -/
def QuantsExpFree (ρ : VarEnv) (qs : List Param) : Prop :=
  ∀ x t w, Param.expP x t ∈ qs → ρ.findVal? x = some w → ExpFree w

mutual
/-- **`DDerivesB` with `ExpFree` quantifiers** at every rule instance. -/
inductive DDerivesBE (env : Env) (O : ElseI) : IL.Id → MixopS → List ArgV → Value → Prop where
  | rule {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param} {t : Typ}
      {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
      {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
      (hrel : env.findRel? x = some (ps, op, t, rules))
      (hrule : rules[i]? = some (.ruleD nm qs op e prems))
      (halt : e' ∈ conclAlts e)
      (hps : bindParams VarEnv.empty ps args = some ρ₀)
      (hq : QuantsOk env (ρ₀.bindVals σ) qs)
      (hx : QuantsExpFree (ρ₀.bindVals σ) qs)
      (he : EvalExp env (ρ₀.bindVals σ) e' v)
      (hp : ∀ pr ∈ prems, DPremBE env O (O x args i v) (ρ₀.bindVals σ) pr) :
      DDerivesBE env O x op args v

/-- `DPremB` with relations read by `DDerivesBE env O`. -/
inductive DPremBE (env : Env) (O : ElseI) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremBE env O els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremBE env O els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremBE env O els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesBE env O x op avs w →
      DPremBE env O els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremBE env O els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremBE env O els (ρ.bindVals row) pr → DPremBE env O els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremBE env O els (ρ.bindVals r) pr) →
      DPremBE env O els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremBE env O els (ρ.bindVals r) pr) →
      DPremBE env O els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))
end

end Silmaril.Wasm.SpecTec.Sim.Round7.Transfer
