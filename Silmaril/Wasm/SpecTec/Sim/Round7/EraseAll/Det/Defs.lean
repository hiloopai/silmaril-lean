module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# Round 7, the export swap: rule quantifiers in the swap set (round 3, pass 3)

The first part of item 4 of the plan for `Round7.Swap.Task.stepErase`: in a `DDerivesB`
derivation whose input is in the swap set, every quantifier of every rule instance is bound to a
value in the swap set. It is the `AllIn Q` analogue of `Round7.Determ.dderivesB_E` (which shows
the same for `ExpFree`), for the relations of the checked part of the script (`grE`), and it
reuses Round 7's mode check (`Round7.Determ.ruleK`, kernel-checked by `detRelsOk_fixed`).

* `AIOn Q ρ K`: every variable of `K` bound in `ρ` is bound to a value in the swap set.
* `InAI Q v`: the input of a relation instance, the first component of a non-empty tuple, is in
  the swap set.
* `QuantsP P ρ qs`: every expression quantifier of `qs` bound in `ρ` satisfies `P`.
* `DDerivesBQ P env O`, `DPremBQ P env O`: `Round6.Reading.DDerivesB`/`DPremB` with, at every rule
  instance, every expression quantifier satisfying `P` (`Round7.Transfer.DDerivesBE` at a general
  predicate). Forgetting the side condition gives back a `DDerivesB` derivation.
* `ElseAI Q O`: `otherwise` premises read through `O`, at swap-set inputs of `grE` relations.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (AllIn)
open Round6.Reading (conclAlts)

/-- **Every variable of `K` bound in `ρ` is bound to a value in the swap set.** -/
def AIOn (Q : Value → Prop) (ρ : VarEnv) (K : List IL.Id) : Prop :=
  ∀ x ∈ K, ∀ w, ρ.findVal? x = some w → AllIn Q w

/-- **The input of a relation instance is in the swap set**: the first component of a non-empty
tuple. -/
def InAI (Q : Value → Prop) (v : Value) : Prop := ∀ a rest, v = .tuple (a :: rest) → AllIn Q a

/-- Every expression quantifier of `qs` bound in `ρ` satisfies `P`. -/
def QuantsP (P : Value → Prop) (ρ : VarEnv) (qs : List Param) : Prop :=
  ∀ x t w, Param.expP x t ∈ qs → ρ.findVal? x = some w → P w

/-- **`otherwise` read only at swap-set inputs** of the checked relations. -/
def ElseAI (Q : Value → Prop) (O : ElseI) : ElseI := fun x args i v =>
  O x args i v ∧ InAI Q v ∧ grE x = true

mutual
/-- **`DDerivesB` with quantifiers satisfying `P`** at every rule instance. -/
inductive DDerivesBQ (P : Value → Prop) (env : Env) (O : ElseI) :
    IL.Id → MixopS → List ArgV → Value → Prop where
  | rule {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param} {t : Typ}
      {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
      {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
      (hrel : env.findRel? x = some (ps, op, t, rules))
      (hrule : rules[i]? = some (.ruleD nm qs op e prems))
      (halt : e' ∈ conclAlts e)
      (hps : bindParams VarEnv.empty ps args = some ρ₀)
      (hq : QuantsOk env (ρ₀.bindVals σ) qs)
      (hx : QuantsP P (ρ₀.bindVals σ) qs)
      (he : EvalExp env (ρ₀.bindVals σ) e' v)
      (hp : ∀ pr ∈ prems, DPremBQ P env O (O x args i v) (ρ₀.bindVals σ) pr) :
      DDerivesBQ P env O x op args v

/-- `DPremB` with relations read by `DDerivesBQ P env O`. -/
inductive DPremBQ (P : Value → Prop) (env : Env) (O : ElseI) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremBQ P env O els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremBQ P env O els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremBQ P env O els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesBQ P env O x op avs w →
      DPremBQ P env O els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremBQ P env O els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremBQ P env O els (ρ.bindVals row) pr → DPremBQ P env O els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremBQ P env O els (ρ.bindVals r) pr) →
      DPremBQ P env O els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremBQ P env O els (ρ.bindVals r) pr) →
      DPremBQ P env O els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))
end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
