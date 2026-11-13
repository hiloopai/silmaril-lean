module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeEnv

/-!
# `otherwise` moves when the earlier rules read back

Generic in two environments `e₁`, `e₂` that the evaluator cannot tell apart (`EnvSame`) and whose
typing grows from `e₁` to `e₂` (`TypRepair`).

An `otherwise` premise of rule `i` holds at `v` when no earlier rule `j < i` fires on the left-hand
side of `v`. To move it from `e₁` to `e₂`, a firing of rule `j` in `e₂` has to be read back as one
in `e₁`. Evaluation agrees, so what is left is typing, which only grows. `PairBack e₁ e₂ ps args
ri rj` asks for that: wherever rule `i` holds in `e₁` and rule `j` concludes in `e₂` on the same
left-hand side, the quantifiers of `j` typed in `e₂` are typed in `e₁`, and the premises of `j`
consult no relation (`relFreeB`). A pair whose left-hand sides never meet satisfies it vacuously.

* `premW_back`, `premW_fwdNoElse`: relation-free premises move back; premises read through
  `DDerives · noElse` move forward.
* **`otherwiseAt_move`**: if every rule `i` with an `otherwise` premise is in `PairBack` with
  every earlier rule, then `otherwise` in `e₁`, at a point where the rest of rule `i` holds in
  `e₁` (`RuleCtx`), implies `otherwise` in `e₂`. The proof is a strong induction on `i`. The
  premise of an earlier `otherwise` rule `j` is read back through the earlier rules `j' < j`,
  which move forward by the induction hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (Interp ElseI PremW QuantsOk DDerives RuleBody SameLhs otherwise
  otherwiseAt noElse)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame TypRepair RuleCtx hasElseB evalExp_of
  evalDoms_of quantsOk_of dderives_of)

variable {e₁ e₂ : Env} {g : TypCase → TypCase}

/-- A premise that consults no relation. -/
def relFreeB : Prem → Bool
  | .rulePr _ _ _ _ => false
  | .iterPr pr _ => relFreeB pr
  | _ => true

/-- A rule with an `otherwise` premise. -/
def RuleHasElse : Rule → Prop
  | .ruleD _ _ _ _ prems => ∃ pr ∈ prems, hasElseB pr = true

/-- **Rule `j` reads back from `e₂` to `e₁` against rule `i`.** -/
def PairBack (e₁ e₂ : Env) (ps : List Param) (args : List ArgV) : Rule → Rule → Prop
  | .ruleD _ qsi _ ei _, .ruleD _ qsj _ ej premsj =>
    ∀ ρ₀ σ σ' v w, bindParams VarEnv.empty ps args = some ρ₀ →
      QuantsOk e₁ (ρ₀.bindVals σ) qsi → EvalExp e₁ (ρ₀.bindVals σ) ei v →
      EvalExp e₁ (ρ₀.bindVals σ') ej w → SameLhs v w → QuantsOk e₂ (ρ₀.bindVals σ') qsj →
      QuantsOk e₁ (ρ₀.bindVals σ') qsj ∧ premsj.all relFreeB = true

/-- A relation-free premise moves back, given its `otherwise` reading. -/
theorem premW_back (hS : EnvSame e₁ e₂) {D₁ D₂ : Interp} {els₁ els₂ : Prop} {ρ : VarEnv}
    {pr : Prem} (h : PremW e₂ D₂ els₂ ρ pr) (hp : relFreeB pr = true)
    (hel : hasElseB pr = true → els₂ → els₁) : PremW e₁ D₁ els₁ ρ pr := by
  induction h with
  | ifPr he => exact .ifPr (evalExp_of hS.symm he)
  | elsePr h => exact .elsePr (hel rfl h)
  | letPr h₁ h₂ => exact .letPr (evalExp_of hS.symm h₁) (evalExp_of hS.symm h₂)
  | rulePr => simp [relFreeB] at hp
  | iterOptNone hd hne hall => exact .iterOptNone (evalDoms_of hS.symm hd) hne hall
  | iterOptSome hd hne hs _ ih => exact .iterOptSome (evalDoms_of hS.symm hd) hne hs (ih hp hel)
  | iterList hit hd hne hdl hlen _ ih =>
    exact .iterList hit (evalDoms_of hS.symm hd) hne hdl hlen fun r hr => ih r hr hp hel
  | iterListN hd hn hk hdl hlen _ ih =>
    exact .iterListN (evalDoms_of hS.symm hd) (evalExp_of hS.symm hn) hk hdl hlen
      fun r hr => ih r hr hp hel

/-- A premise read through `DDerives · noElse` moves forward, given its `otherwise` reading. -/
theorem premW_fwdNoElse (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {els₁ els₂ : Prop}
    {ρ : VarEnv} {pr : Prem} (h : PremW e₁ (DDerives e₁ noElse) els₁ ρ pr)
    (hel : hasElseB pr = true → els₁ → els₂) : PremW e₂ (DDerives e₂ noElse) els₂ ρ pr := by
  induction h with
  | ifPr he => exact .ifPr (evalExp_of hS he)
  | elsePr h => exact .elsePr (hel rfl h)
  | letPr h₁ h₂ => exact .letPr (evalExp_of hS h₁) (evalExp_of hS h₂)
  | rulePr ha he hd =>
    exact .rulePr (StoreAgree.evalArgs_of hS ha) (evalExp_of hS he)
      (dderives_of hS hT (fun _ _ _ _ h _ => h) hd)
  | iterOptNone hd hne hall => exact .iterOptNone (evalDoms_of hS hd) hne hall
  | iterOptSome hd hne hs _ ih => exact .iterOptSome (evalDoms_of hS hd) hne hs (ih hel)
  | iterList hit hd hne hdl hlen _ ih =>
    exact .iterList hit (evalDoms_of hS hd) hne hdl hlen fun r hr => ih r hr hel
  | iterListN hd hn hk hdl hlen _ ih =>
    exact .iterListN (evalDoms_of hS hd) (evalExp_of hS hn) hk hdl hlen fun r hr => ih r hr hel

/-- `otherwiseAt`, unfolded once. -/
theorem otherwiseAt_unfold {env : Env} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value} :
    otherwiseAt env x args i v ↔ ∀ j, j < i → ∀ ps op t rules r,
      env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r → ∀ w, SameLhs v w →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x args j w) ps args op r w := by
  rw [otherwiseAt]

/-- A body of an earlier rule moves forward, given that its own `otherwise` does. -/
theorem body_fwd (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {x : IL.Id} {args : List ArgV}
    {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {j : Nat} {r : Rule}
    {w : Value} (hrel : e₁.findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    (ih : RuleCtx e₁ x args j w → otherwiseAt e₁ x args j w → otherwiseAt e₂ x args j w)
    (h : RuleBody e₁ (DDerives e₁ noElse) (otherwiseAt e₁ x args j w) ps args op r w) :
    RuleBody e₂ (DDerives e₂ noElse) (otherwiseAt e₂ x args j w) ps args op r w := by
  rcases r with ⟨nm, qs, op', e, prems⟩
  obtain ⟨rfl, ρ₀, σ, hps, hq, he, hp⟩ := h
  refine ⟨rfl, ρ₀, σ, hps, quantsOk_of hS hT hq, evalExp_of hS he, fun pr hm => ?_⟩
  refine premW_fwdNoElse hS hT (hp pr hm) fun hpe h₁ => ih ?_ h₁
  exact ⟨ps, op', t, rules, nm, qs, e, prems, ρ₀, σ, hrel, hr, ⟨pr, hm, hpe⟩, hps, hq, he⟩

/-- The `otherwise` of an earlier rule `j` reads back, through the rules before it, which move
forward. -/
theorem else_back (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {x : IL.Id} {args : List ArgV}
    {j : Nat} {w : Value}
    (ih : ∀ j' < j, ∀ w', RuleCtx e₁ x args j' w' → otherwiseAt e₁ x args j' w' →
      otherwiseAt e₂ x args j' w')
    (h₂ : otherwiseAt e₂ x args j w) : otherwiseAt e₁ x args j w := by
  refine otherwiseAt_unfold.2 fun j' hj' ps op t rules r hrel hr w' hsame hb => ?_
  have hrel₂ : e₂.findRel? x = some (ps, op, t, rules) := (hS.rels x).trans hrel
  exact otherwiseAt_unfold.1 h₂ j' hj' ps op t rules r hrel₂ hr w' hsame
    (body_fwd hS hT hrel hr (ih j' hj' w') hb)

/-- The context of a rule `i` at `v`, with the relation's table entry fixed. -/
def RuleAt (env : Env) (ps : List Param) (args : List ArgV) (ri : Rule) (v : Value) : Prop :=
  match ri with
  | .ruleD _ qs _ e _ => ∃ ρ₀ σ, bindParams VarEnv.empty ps args = some ρ₀ ∧
      QuantsOk env (ρ₀.bindVals σ) qs ∧ EvalExp env (ρ₀.bindVals σ) e v

/-- **A body of an earlier rule `j` reads back from `e₂` to `e₁`**, against a rule `i` whose
rest holds in `e₁` on the same left-hand side. -/
theorem body_back (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {x : IL.Id} {args : List ArgV}
    {ps : List Param} {op : MixopS} {ri r : Rule} {j : Nat} {v w : Value}
    (hpair : PairBack e₁ e₂ ps args ri r) (hC : RuleAt e₁ ps args ri v) (hsame : SameLhs v w)
    (ih : ∀ j' < j, ∀ w', RuleCtx e₁ x args j' w' → otherwiseAt e₁ x args j' w' →
      otherwiseAt e₂ x args j' w')
    (hb : RuleBody e₂ (DDerives e₂ noElse) (otherwiseAt e₂ x args j w) ps args op r w) :
    RuleBody e₁ (DDerives e₁ noElse) (otherwiseAt e₁ x args j w) ps args op r w := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases r with ⟨nmj, qsj, opj, ej, premsj⟩
  obtain ⟨ρ₀, σ, hps, hq, he⟩ := hC
  obtain ⟨hopj, ρ₀', σ', hps', hq', he', hpr'⟩ := hb
  have e₀ : ρ₀' = ρ₀ := Option.some.inj (hps'.symm.trans hps)
  rw [e₀] at hq' he' hpr'
  have he₁ : EvalExp e₁ (ρ₀.bindVals σ') ej w := evalExp_of hS.symm he'
  obtain ⟨hq₁, hrf⟩ := hpair ρ₀ σ σ' v w hps hq he he₁ hsame hq'
  refine ⟨hopj, ρ₀, σ', hps, hq₁, he₁, fun pr hm => ?_⟩
  exact premW_back hS (hpr' pr hm) (List.all_eq_true.1 hrf pr hm) fun _ h₂ => else_back hS hT ih h₂

/-- **`otherwise` moves from `e₁` to `e₂`** when every `otherwise` rule reads its earlier rules
back (`PairBack`). -/
theorem otherwiseAt_move (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {x : IL.Id}
    {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {args : List ArgV}
    (hrel : e₁.findRel? x = some (ps, op, t, rules))
    (hP : ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj → RuleHasElse ri →
      PairBack e₁ e₂ ps args ri rj) :
    ∀ i v, RuleCtx e₁ x args i v → otherwiseAt e₁ x args i v → otherwiseAt e₂ x args i v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro v hC hO
  obtain ⟨ps₁, op₁, t₁, rules₁, nm, qs, e, prems, ρ₀, σ, hrel₁, hri, hel, hps, hq, he⟩ := hC
  have h₁ : ps = ps₁ ∧ op = op₁ ∧ t = t₁ ∧ rules = rules₁ := by
    simpa [hrel] using hrel₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
  refine otherwiseAt_unfold.2 fun j hj ps' op' t' rules' r hrel₂ hr w hsame hb => ?_
  have h₂ : ps = ps' ∧ op = op' ∧ t = t' ∧ rules = rules' := by
    simpa [hS.rels x, hrel] using hrel₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h₂
  refine otherwiseAt_unfold.1 hO j hj ps op t rules r hrel hr w hsame ?_
  exact body_back hS hT (hP i j _ _ hj hri hr hel) ⟨ρ₀, σ, hps, hq, he⟩ hsame
    (fun j' hj' => ih j' (by omega)) hb

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
