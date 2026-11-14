module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Basic

/-!
# `Match_args` never holds, so no call reduces

`5-reduction.spectec` writes `rule Match_args: S |- a* / {q*} a' => s -- … -- if a* =
$subst_arg(s, a')*`, with `a'` where `a'*` is meant. The frontend elaborates the conclusion's
`a'` as a one-element list and the premise as an iteration of `$subst_arg(s, a')` over **no**
domain, which `il/valid.ml` accepts (a domain-less iteration is only rejected on a right-hand
side). Such an iteration has no value (`Sem.evalIterE` requires a domain, as `eval.ml` does), so
the premise never holds and `Match_args` derives nothing (`not_matchArgs`), in both scripts. Every
use of it, `Step_exp/CALL-apply` and `Expand_typ/step` among them, is dead: read by our semantics,
their reduction never unfolds a function call or a type definition.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives RuleBody PremW)

set_option maxRecDepth 100000

/-- A list iteration over no domain has no value. -/
theorem not_evalIterE_list_nil {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} :
    ¬ EvalIterE env ρ e .list [] v := by
  rintro ⟨n, h⟩
  match n, h with
  | 0, h =>
    have e₀ : evalIterE 0 env ρ e .list [] = .error .outOfFuel := by with_unfolding_all rfl
    rw [e₀] at h; cases h
  | 1, h =>
    have e₁ : evalIterE 1 env ρ e .list [] = .error .outOfFuel := by with_unfolding_all rfl
    rw [e₁] at h; cases h
  | m + 2, h =>
    have e₂ : evalIterE (m + 2) env ρ e .list [] = .error .undef := by
      simp [evalIterE, evalDoms, Res.assert]
    rw [e₂] at h; cases h

/-- The domain-less premise of `Match_args`. -/
def matchArgsPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.iterE (.varE "a") (.mk .list [.mk "a" (.varE "a*")]))
    (.iterE (.callE "subst_arg" [.expA (.varE "s"), .expA (.varE "a'")]) (.mk .list [])))

theorem not_matchArgsPrem {env : Env} {D : Sim.Interp} {els : Prop} {ρ : VarEnv}
    (h : PremW env D els ρ matchArgsPrem) : False := by
  cases h with
  | ifPr he =>
    obtain ⟨-, w, -, hw, -⟩ := evalExp_cmpE_iff.1 he
    exact not_evalIterE_list_nil (evalExp_iterE_iff.1 hw)

/-- `Match_args` has one rule, whose second premise is `matchArgsPrem`. -/
theorem matchArgs_rules (env : Env) (h : env = envF ∨ env = envO) :
    ∃ t r, env.findRel? "Match_args" = some ([], "%|-%/{%}%=>%", t, [r]) ∧
      ∃ nm qs e p₁, r = .ruleD nm qs "%|-%/{%}%=>%" e [p₁, matchArgsPrem] := by
  rcases h with rfl | rfl
  · exact ⟨_, _, rfl, _, _, _, _, rfl⟩
  · exact ⟨_, _, rfl, _, _, _, _, rfl⟩

/-- **`Match_args` derives nothing**, in the fixed and in the original script. -/
theorem not_matchArgs {env : Env} (henv : env = envF ∨ env = envO) {O : Sim.ElseI}
    {op : MixopS} {args : List ArgV} {v : Value} :
    ¬ DDerives env O "Match_args" op args v := by
  intro h
  obtain ⟨ps, t, rules, i, r, hrel, hr, hb⟩ := Sim.dderives_iff.1 h
  obtain ⟨t', r', hrel', nm, qs, e, p₁, hr'⟩ := matchArgs_rules env henv
  rw [hrel'] at hrel
  have hrules : [r'] = rules := by simp only [Option.some.injEq, Prod.mk.injEq] at hrel; exact hrel.2.2.2
  subst hrules
  match i, hr with
  | 0, hr =>
    have hrr : r = .ruleD nm qs "%|-%/{%}%=>%" e [p₁, matchArgsPrem] :=
      (Option.some.inj hr).symm.trans hr'
    subst hrr
    obtain ⟨-, ρ₀, σ, -, -, -, hps⟩ := hb
    exact not_matchArgsPrem (hps _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- A `Match_args` premise. -/
def isMatchArgs : Prem → Bool
  | .rulePr x _ _ _ => x == "Match_args"
  | _ => false

/-- The premises of a rule. -/
def premsOf : Rule → List Prem
  | .ruleD _ _ _ _ prems => prems

/-- **A rule with a `Match_args` premise never fires.** -/
theorem dead_of_matchArgs_prem {env : Env} (henv : env = envF ∨ env = envO) {O : Sim.ElseI}
    {els : Prop} {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value}
    (hm : (premsOf r).any isMatchArgs = true) :
    ¬ RuleBody env (DDerives env O) els ps args op r v := by
  obtain ⟨nm, qs, op₀, e, prems⟩ := r
  rintro ⟨-, ρ₀, σ, -, -, -, hp⟩
  obtain ⟨p, hpm, hpi⟩ := List.any_eq_true.1 hm
  match p, hpi with
  | .rulePr x as₀ op' e', hx =>
    have hx' : x = "Match_args" := by simpa [isMatchArgs] using hx
    subst hx'
    cases hp _ hpm with
    | rulePr _ _ hd => exact not_matchArgs henv hd

/-- `Step_exp/CALL-apply` (rule 65 of the fixed script, 63 of the original) has a `Match_args`
premise, and so has `Expand_typ/step` (rule 2). -/
theorem callApply_matchArgs :
    (∃ r, (rulesOf envF "Step_exp")[65]? = some r ∧ (premsOf r).any isMatchArgs = true) ∧
      (∃ r, (rulesOf envO "Step_exp")[63]? = some r ∧ (premsOf r).any isMatchArgs = true) ∧
      ∃ r, (rulesOf envF "Expand_typ")[2]? = some r ∧ (premsOf r).any isMatchArgs = true :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end Silmaril.Wasm.SpecTec.Meta
