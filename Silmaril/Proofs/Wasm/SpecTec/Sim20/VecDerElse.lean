module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerMove
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Thms

/-!
# `otherwise` moves both ways between two environments that type a rule alike

Round 4's `ElseAgree.otherwiseAt_move` and round 7's `Utf8Else.otherwiseAtB_moveU` move an
`otherwise` premise from `e₁` to `e₂` when typing only grows: an earlier rule's body moves forward
by monotonicity. Across the vector errata typing does not grow, so the earlier rules are read in
both directions instead, against a rule whose quantifiers are typed in both environments.

Generic in two environments that evaluate alike (`StoreAgree.EnvSame`).

* `Ctx2 e₁ e₂ x args i v`: rule `i` of `x` has an `otherwise` premise; its quantifiers are typed
  in both environments and one conclusion alternative evaluates to `v`.
* `PairSym e₁ e₂ ps args ri rj`: against the `otherwise` rule `ri` in such a context, an earlier
  rule `rj` concluding on the same left-hand side types its quantifiers alike in `e₁` and `e₂`, and
  its premises consult no relation. Symmetric under `EnvSame` (`pairSym_symm`).
* **`otherwiseAtB_sym`**: if every `otherwise` rule of `x` is in `PairSym` with every earlier rule,
  then under `Ctx2`, `otherwiseAtB e₁ x args i v ↔ otherwiseAtB e₂ x args i v`. Strong induction
  on `i`, both directions at once; an earlier rule's own `otherwise` is moved by the induction
  hypothesis at a `Ctx2` that the pair provides.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SameLhs noElse)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB conclAlts otherwiseAtB RuleBodyB)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame hasElseB evalExp_of)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (relFreeB premW_back)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (RuleHasElseB otherwiseAtB_unfold')

variable {e₁ e₂ : Env}

/-- **Rule `i` of `x` at `v` apart from its premises, typed in both environments.** -/
def Ctx2 (e₁ e₂ : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) : Prop :=
  ∃ ps op t rules nm qs e prems ρ₀ σ e', e₁.findRel? x = some (ps, op, t, rules) ∧
    rules[i]? = some (.ruleD nm qs op e prems) ∧ (∃ pr ∈ prems, hasElseB pr = true) ∧
    e' ∈ conclAlts e ∧ bindParams VarEnv.empty ps args = some ρ₀ ∧
    QuantsOk e₁ (ρ₀.bindVals σ) qs ∧ QuantsOk e₂ (ρ₀.bindVals σ) qs ∧
    EvalExp e₁ (ρ₀.bindVals σ) e' v

/-- **Rule `rj` types alike in `e₁` and `e₂` against the `otherwise` rule `ri`.** -/
def PairSym (e₁ e₂ : Env) (ps : List Param) (args : List ArgV) : Rule → Rule → Prop
  | .ruleD _ qsi _ ei _, .ruleD _ qsj _ ej premsj =>
    ∀ ρ₀ σ σ' v w ei' ej', ei' ∈ conclAlts ei → ej' ∈ conclAlts ej →
      bindParams VarEnv.empty ps args = some ρ₀ →
      QuantsOk e₁ (ρ₀.bindVals σ) qsi → QuantsOk e₂ (ρ₀.bindVals σ) qsi →
      EvalExp e₁ (ρ₀.bindVals σ) ei' v → EvalExp e₁ (ρ₀.bindVals σ') ej' w → SameLhs v w →
      (QuantsOk e₁ (ρ₀.bindVals σ') qsj ↔ QuantsOk e₂ (ρ₀.bindVals σ') qsj) ∧
        premsj.all relFreeB = true

theorem ctx2_symm (hS : EnvSame e₁ e₂) {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    (h : Ctx2 e₁ e₂ x args i v) : Ctx2 e₂ e₁ x args i v := by
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, he', hps, hq₁, hq₂, he⟩ :=
    h
  exact ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', (hS.rels x).trans hrel, hri, hel, he',
    hps, hq₂, hq₁, evalExp_of hS he⟩

theorem pairSym_symm (hS : EnvSame e₁ e₂) {ps : List Param} {args : List ArgV} {ri rj : Rule}
    (h : PairSym e₁ e₂ ps args ri rj) : PairSym e₂ e₁ ps args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' hps hq₂ hq₁ hev hew hsame
  obtain ⟨hiff, hrf⟩ :=
    h ρ₀ σ σ' v w ei' ej' hei' hej' hps hq₁ hq₂ (evalExp_of hS.symm hev) (evalExp_of hS.symm hew)
      hsame
  exact ⟨hiff.symm, hrf⟩

/-- **An earlier rule's body read in `e₂` is one in `e₁`**, against an `otherwise` rule typed in
both, given that the earlier rule's own `otherwise` reads back. -/
theorem body_back2 (hS : EnvSame e₁ e₂) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {args : List ArgV} (hrel : e₁.findRel? x = some (ps, op, t, rules))
    {nmi : IL.Id} {qsi : List Param} {ei ei' : Exp} {premsi : List Prem} {ρ₀ : VarEnv}
    {σ : List (IL.Id × Value)} {v w : Value} {j : Nat} {r : Rule}
    (hpair : PairSym e₁ e₂ ps args (.ruleD nmi qsi op ei premsi) r) (hr : rules[j]? = some r)
    (hei' : ei' ∈ conclAlts ei) (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (hq₁ : QuantsOk e₁ (ρ₀.bindVals σ) qsi) (hq₂ : QuantsOk e₂ (ρ₀.bindVals σ) qsi)
    (hev : EvalExp e₁ (ρ₀.bindVals σ) ei' v) (hsame : SameLhs v w)
    (ih : Ctx2 e₁ e₂ x args j w → otherwiseAtB e₂ x args j w → otherwiseAtB e₁ x args j w)
    (hb : RuleBodyB e₂ (DDerivesB e₂ noElse) (otherwiseAtB e₂ x args j w) ps args op r w) :
    RuleBodyB e₁ (DDerivesB e₁ noElse) (otherwiseAtB e₁ x args j w) ps args op r w := by
  rcases r with ⟨nmj, qsj, opj, ej, premsj⟩
  obtain ⟨ej', hej', rfl, ρ₀', σ', hps', hq', hew, hpr'⟩ := hb
  obtain rfl : ρ₀' = ρ₀ := Option.some.inj (hps'.symm.trans hps)
  have hew₁ : EvalExp e₁ (ρ₀'.bindVals σ') ej' w := evalExp_of hS.symm hew
  obtain ⟨hiff, hrf⟩ := hpair ρ₀' σ σ' v w ei' ej' hei' hej' hps hq₁ hq₂ hev hew₁ hsame
  have hqj₁ : QuantsOk e₁ (ρ₀'.bindVals σ') qsj := hiff.2 hq'
  refine ⟨ej', hej', rfl, ρ₀', σ', hps, hqj₁, hew₁, fun pr hm => ?_⟩
  refine premW_back hS (hpr' pr hm) (List.all_eq_true.1 hrf pr hm) fun hpe h₂ => ?_
  exact ih ⟨ps, _, t, rules, nmj, qsj, ej, premsj, ρ₀', σ', ej', hrel, hr, ⟨pr, hm, hpe⟩,
    hej', hps, hqj₁, hq', hew₁⟩ h₂

/-- **One direction**, given the other direction at earlier rules. -/
theorem else_dir (hS : EnvSame e₁ e₂) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {args : List ArgV} (hrel : e₁.findRel? x = some (ps, op, t, rules))
    (hP : ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj →
      RuleHasElseB ri → PairSym e₁ e₂ ps args ri rj)
    {i : Nat} {v : Value}
    (ih : ∀ j < i, ∀ w, Ctx2 e₁ e₂ x args j w → otherwiseAtB e₂ x args j w →
      otherwiseAtB e₁ x args j w)
    (hC : Ctx2 e₁ e₂ x args i v) (hO : otherwiseAtB e₁ x args i v) :
    otherwiseAtB e₂ x args i v := by
  obtain ⟨ps₁, op₁, t₁, rules₁, nm, qs, e, prems, ρ₀, σ, e', hrel₁, hri, hel, he', hps, hq₁, hq₂,
    hev⟩ := hC
  obtain ⟨rfl, rfl, rfl, rfl⟩ : ps = ps₁ ∧ op = op₁ ∧ t = t₁ ∧ rules = rules₁ := by
    simpa [hrel] using hrel₁
  refine otherwiseAtB_unfold'.2 fun j hj ps' op' t' rules' r hrel₂ hr w hsame hb => ?_
  obtain ⟨rfl, rfl, rfl, rfl⟩ : ps = ps' ∧ op = op' ∧ t = t' ∧ rules = rules' := by
    simpa [hS.rels x, hrel] using hrel₂
  refine otherwiseAtB_unfold'.1 hO j hj ps op t rules r hrel hr w hsame ?_
  exact body_back2 hS hrel (hP i j _ _ hj hri hr hel) hr he' hps hq₁ hq₂ hev hsame (ih j hj w) hb

/-- **`otherwise` agrees in `e₁` and `e₂`** at a rule typed in both, when every `otherwise` rule
types its earlier rules alike (`PairSym`). -/
theorem otherwiseAtB_sym (hS : EnvSame e₁ e₂) {x : IL.Id} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} {args : List ArgV}
    (hrel : e₁.findRel? x = some (ps, op, t, rules))
    (hP : ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj →
      RuleHasElseB ri → PairSym e₁ e₂ ps args ri rj) :
    ∀ i v, Ctx2 e₁ e₂ x args i v → (otherwiseAtB e₁ x args i v ↔ otherwiseAtB e₂ x args i v) := by
  have hrel₂ : e₂.findRel? x = some (ps, op, t, rules) := (hS.rels x).trans hrel
  have hP₂ : ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj →
      RuleHasElseB ri → PairSym e₂ e₁ ps args ri rj :=
    fun i j ri rj hj hi hj' he => pairSym_symm hS (hP i j ri rj hj hi hj' he)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro v hC
  constructor
  · exact else_dir hS hrel hP (fun j hj w hC' => (ih j hj w hC').2) hC
  · exact else_dir hS.symm hrel₂ hP₂ (fun j hj w hC' => (ih j hj w (ctx2_symm hS.symm hC')).1)
      (ctx2_symm hS hC)

end Silmaril.Wasm.SpecTec.Sim20.VecDer
