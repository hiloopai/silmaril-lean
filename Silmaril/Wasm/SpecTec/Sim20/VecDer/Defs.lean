module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# Derivations across the 2.0 vector type errata (definitions)

`VecFix.simEnv20V B` is `StoreFix.simEnv20T B` with two type errata (`docs/projects/spectec/README.md`): the `VEXTRACT_LANE` case of `instr`/`admininstr` is restated, and the three operator
families gain float instances in front. Rules, definitions and builtins are the same, so the
evaluator cannot tell the two apart (`VecAgree.envSameX`, `envSameV`). Typing differs, and not
monotonically. This header names what a derivation of `simEnv20T B` must carry to be one of
`simEnv20V B`.

* `vbad20`: round 4's `tbad20` (the fifteen types that reach `instr` or `admininstr`) and the three
  families. Off this set the two environments have the same type table, and it is closed
  (kernel, `VecDer.typsOffB_vbad20`), so off it typing is the same in both directions.
* `QuantV ρ t w`: a quantifier `x : t` bound to `w` is harmless: `t` avoids `vbad20`, or `w` is
  `VecAgree.VOk` and `t` is a type `VecAgree.hasTyp_vec` moves (`TOk`).
* `QuantsV ρ qs`: the scope has no type variables and every expression quantifier is harmless.
* `SideC`: a side condition at a rule instance: the relation, the rule index, the scope and the
  quantifiers.
* `DDerivesBS S env O`, `DPremBS S env O`: round 6's `DDerivesB`/`DPremB` with `S` at every rule
  instance. It is round 7's `DDerivesBQ` with a side condition that may read the rule and the
  quantifier types, not only the bound values.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (ElseI QuantsOk EvalDoms domLists domSomes)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (conclAlts)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (GoodT)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (VOk TOk)

/-- **The types where `simEnv20T` and `simEnv20V` may type differently**: those that reach `instr`
or `admininstr` (`ElseAgree.tbad20`), and the three operator families. -/
def vbad20 : List String :=
  ["instr", "admininstr", "config", "expr", "code", "elem", "global", "func", "datamode",
    "elemmode", "funcinst", "module", "data", "store", "state", "vunop_", "vbinop_", "vrelop_"]

/-- **A harmless quantifier**: its type avoids `vbad20`, or its value is `VOk` at a type
`hasTyp_vec` moves. -/
def QuantV (ρ : VarEnv) (t : Typ) (w : Value) : Prop :=
  GoodT vbad20 (evTyp t) ∨ (VOk w ∧ TOk ρ t w)

/-- **Every expression quantifier of `qs` bound in `ρ` is harmless**, in a scope without type
variables. -/
def QuantsV (ρ : VarEnv) (qs : List Param) : Prop :=
  ρ.typs = [] ∧ ∀ x t w, Param.expP x t ∈ qs → ρ.findVal? x = some w → QuantV ρ t w

/-- A side condition at a rule instance: relation, rule index, scope, quantifiers. -/
abbrev SideC : Type := IL.Id → Nat → VarEnv → List Param → Prop

/-- `QuantsV`, as a side condition. -/
def sideV : SideC := fun _ _ ρ qs => QuantsV ρ qs

mutual
/-- **`DDerivesB` with the side condition `S` at every rule instance.** -/
inductive DDerivesBS (S : SideC) (env : Env) (O : ElseI) :
    IL.Id → MixopS → List ArgV → Value → Prop where
  | rule {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param} {t : Typ}
      {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
      {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
      (hrel : env.findRel? x = some (ps, op, t, rules))
      (hrule : rules[i]? = some (.ruleD nm qs op e prems))
      (halt : e' ∈ conclAlts e)
      (hps : bindParams VarEnv.empty ps args = some ρ₀)
      (hq : QuantsOk env (ρ₀.bindVals σ) qs)
      (hs : S x i (ρ₀.bindVals σ) qs)
      (he : EvalExp env (ρ₀.bindVals σ) e' v)
      (hp : ∀ pr ∈ prems, DPremBS S env O (O x args i v) (ρ₀.bindVals σ) pr) :
      DDerivesBS S env O x op args v

/-- `DPremB` with relations read by `DDerivesBS S env O`. -/
inductive DPremBS (S : SideC) (env : Env) (O : ElseI) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremBS S env O els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremBS S env O els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremBS S env O els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesBS S env O x op avs w →
      DPremBS S env O els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremBS S env O els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremBS S env O els (ρ.bindVals row) pr → DPremBS S env O els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremBS S env O els (ρ.bindVals r) pr) →
      DPremBS S env O els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremBS S env O els (ρ.bindVals r) pr) →
      DPremBS S env O els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))
end

end Silmaril.Wasm.SpecTec.Sim20.VecDer
