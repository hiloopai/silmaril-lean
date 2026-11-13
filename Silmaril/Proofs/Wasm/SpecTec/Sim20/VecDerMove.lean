module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerEnv

/-!
# A derivation with harmless quantifiers moves to the other environment

Generic in two environments `e₁`, `e₂` that evaluate alike (`StoreAgree.EnvSame`), a side
condition `S`, and a quantifier transfer `hQ` that holds under `S`.

* `forget`: `DDerivesBS S` is a `DDerivesB` derivation.
* `RuleCtxS S env x args i v`: rule `i` of `x` has an `otherwise` premise, and its quantifiers, the
  side condition and one conclusion alternative hold in `env` at `v`.
* `ElseMoveS S e₁ e₂`: the `otherwise` premises of `e₁` that occur in such a context hold in `e₂`.
* **`dderivesBS_move`**: under `ElseMoveS`, a `DDerivesBS S e₁` derivation is a `DDerivesB e₂`
  derivation. It is `Utf8Else.dderivesB_extR` with `EnvExt` replaced by `EnvSame` plus `hQ`.
* **`dderivesBS_toV`**, `sstepBS_toV`: the instance `simEnv20T B` → `simEnv20V B` with
  `S := sideV` (`QuantsV`) and `hQ := quantsOk_toV`. The only hypothesis left is `ElseMoveS`,
  discharged in `VecDerTask`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (ElseI QuantsOk)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB DPremB conclAlts otherwiseB SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame hasElseB evalExp_of evalArgs_of evalDoms_of)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

variable {e₁ e₂ : Env} {S : SideC}

/-! ## Forgetting the side condition -/

mutual
/-- **A `DDerivesBS` derivation is a `DDerivesB` derivation.** -/
theorem forget {env : Env} {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesBS S env O x op args v → DDerivesB env O x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq _ he hp =>
      .rule hrel hrule halt hps hq he fun pr hpr => forgetP (hp pr hpr)

/-- `forget` for premises. -/
theorem forgetP {env : Env} {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremBS S env O els ρ pr → DPremB env O els ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr h
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd => .rulePr ha he (forget hd)
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (forgetP hp)
  | _, _, .iterList hit hd hne hl hk hp => .iterList hit hd hne hl hk fun r hr => forgetP (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
      .iterListN hd he hk hl hlen fun r hr => forgetP (hp r hr)
end

/-! ## Moving under the `otherwise` premises that occur -/

/-- **Rule `i` of `x` at `v` apart from its premises**, for a rule with an `otherwise` premise,
with the side condition. -/
def RuleCtxS (S : SideC) (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) :
    Prop :=
  ∃ ps op t rules nm qs e prems ρ₀ σ e', env.findRel? x = some (ps, op, t, rules) ∧
    rules[i]? = some (.ruleD nm qs op e prems) ∧ (∃ pr ∈ prems, hasElseB pr = true) ∧
    e' ∈ conclAlts e ∧ bindParams VarEnv.empty ps args = some ρ₀ ∧
    QuantsOk env (ρ₀.bindVals σ) qs ∧ S x i (ρ₀.bindVals σ) qs ∧ EvalExp env (ρ₀.bindVals σ) e' v

/-- **The `otherwise` premises of `e₁` that occur, under `S`, hold in `e₂`.** -/
def ElseMoveS (S : SideC) (e₁ e₂ : Env) : Prop :=
  ∀ x args i v, RuleCtxS S e₁ x args i v → otherwiseB e₁ x args i v → otherwiseB e₂ x args i v

mutual
/-- **A derivation moves from `e₁` to `e₂`** when its quantifiers move under `S` and the
`otherwise` premises it uses do. -/
theorem dderivesBS_move (hS : EnvSame e₁ e₂)
    (hQ : ∀ x i ρ qs, S x i ρ qs → QuantsOk e₁ ρ qs → QuantsOk e₂ ρ qs) (hR : ElseMoveS S e₁ e₂) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesBS S e₁ (otherwiseB e₁) x op args v → DDerivesB e₂ (otherwiseB e₂) x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq hs he hp =>
      .rule (by rw [hS.rels]; exact hrel) hrule halt hps (hQ _ _ _ _ hs hq)
        (evalExp_of hS he) fun pr hpr => dpremBS_move hS hQ hR
          (fun hpe h => hR _ _ _ _
            ⟨_, _, _, _, _, _, _, _, _, _, _, hrel, hrule, ⟨pr, hpr, hpe⟩, halt, hps, hq, hs, he⟩ h)
          (hp pr hpr)

/-- `dderivesBS_move` for premises. -/
theorem dpremBS_move (hS : EnvSame e₁ e₂)
    (hQ : ∀ x i ρ qs, S x i ρ qs → QuantsOk e₁ ρ qs → QuantsOk e₂ ρ qs) (hR : ElseMoveS S e₁ e₂)
    {els els' : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, (hasElseB pr = true → els → els') →
      DPremBS S e₁ (otherwiseB e₁) els ρ pr → DPremB e₂ (otherwiseB e₂) els' ρ pr
  | _, _, _, .ifPr h => .ifPr (evalExp_of hS h)
  | _, _, hels, .elsePr h => .elsePr (hels rfl h)
  | _, _, _, .letPr h₂ h₁ => .letPr (evalExp_of hS h₂) (evalExp_of hS h₁)
  | _, _, _, .rulePr ha he hd =>
      .rulePr (evalArgs_of hS ha) (evalExp_of hS he) (dderivesBS_move hS hQ hR hd)
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone (evalDoms_of hS hd) hne hall
  | _, _, hels, .iterOptSome hd hne hs hp =>
      .iterOptSome (evalDoms_of hS hd) hne hs (dpremBS_move hS hQ hR hels hp)
  | _, _, hels, .iterList hit hd hne hl hk hp =>
      .iterList hit (evalDoms_of hS hd) hne hl hk fun r hr => dpremBS_move hS hQ hR hels (hp r hr)
  | _, _, hels, .iterListN hd he hk hl hlen hp =>
      .iterListN (evalDoms_of hS hd) (evalExp_of hS he) hk hl hlen fun r hr =>
        dpremBS_move hS hQ hR hels (hp r hr)
end

/-! ## The 2.0 vector errata -/

/-- **A derivation of `simEnv20T B` with harmless quantifiers is one of `simEnv20V B`**, when the
`otherwise` premises it uses move. -/
theorem dderivesBS_toV {B : Builtins} (hR : ElseMoveS sideV (simEnv20T B) (simEnv20V B))
    {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (h : DDerivesBS sideV (simEnv20T B) (otherwiseB (simEnv20T B)) x op args v) :
    DDerivesB (simEnv20V B) (otherwiseB (simEnv20V B)) x op args v :=
  dderivesBS_move (envSameTV B) (fun _ _ _ _ hs hq => quantsOk_toV hq hs) hR h

/-- A step of `simEnv20T B` with harmless quantifiers. -/
def SStepBV (B : Builtins) (c c' : Value) : Prop :=
  DDerivesBS sideV (simEnv20T B) (otherwiseB (simEnv20T B)) "Step" "%~>%" [] (.tuple [c, c'])

/-- **A step of `simEnv20T B` with harmless quantifiers is a step of `simEnv20V B`**, when the
`otherwise` premises it uses move. -/
theorem sstepBS_toV {B : Builtins} (hR : ElseMoveS sideV (simEnv20T B) (simEnv20V B))
    {c c' : Value} (h : SStepBV B c c') : SStepB (simEnv20V B) c c' :=
  dderivesBS_toV hR h

end Silmaril.Wasm.SpecTec.Sim20.VecDer
