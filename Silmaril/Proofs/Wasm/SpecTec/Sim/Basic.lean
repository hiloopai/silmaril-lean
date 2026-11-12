module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# The declarative reading: inversion, and the six structural rules of `Step`

`dderives_iff` unfolds one step of `DDerives`; `ddrives_of_ruleAt` builds a derivation from a rule
the environment provably contains (`Equiv.Validation.HasRuleAt`). The six rules of `Step` that do
not touch the store (`pure`, `read`, `ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`)
are then constructed for arbitrary values of the right IL types: these are the context-lifting
lemmas the per-family work composes with.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (iterPat valsPat evalExp_iterPat evalExp_valsPat)

/-! ## Unfolding one step -/

/-- A premise of `DDerives` is a `PremW` premise over `DDerives` itself. -/
theorem dprem_toPremW {env : Env} {O : ElseI} :
    ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, DPrem env O els ρ pr →
      PremW env (DDerives env O) els ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, _, .elsePr h => .elsePr h
  | _, _, _, .letPr h₁ h₂ => .letPr h₁ h₂
  | _, _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, _, .iterOptNone hd hn hs => .iterOptNone hd hn hs
  | _, _, _, .iterOptSome hd hn hs h => .iterOptSome hd hn hs (dprem_toPremW h)
  | _, _, _, .iterList hit hd hn hl hk h =>
      .iterList hit hd hn hl hk fun r hr => dprem_toPremW (h r hr)
  | _, _, _, .iterListN hd he hk hl hlen h =>
      .iterListN hd he hk hl hlen fun r hr => dprem_toPremW (h r hr)

/-- One step of `DDerives`: some rule of the relation has a body that holds. -/
theorem dderives_iff {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} :
    DDerives env O x op args v ↔
      ∃ ps t rules i r, env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some r ∧
        RuleBody env (DDerives env O) (O x args i v) ps args op r v := by
  constructor
  · rintro (⟨hrel, hrule, hps, hq, he, hp⟩)
    refine ⟨_, _, _, _, _, hrel, hrule, rfl, _, _, hps, hq, he, fun pr hpr => ?_⟩
    exact dprem_toPremW (hp pr hpr)
  · rintro ⟨ps, t, rules, i, r, hrel, hrule, hb⟩
    obtain ⟨nm, qs, op', e, prems⟩ := r
    obtain ⟨rfl, ρ₀, σ, hps, hq, he, hp⟩ := hb
    exact DDerives.rule hrel hrule hps hq he fun pr hpr => premW_dprem (hp pr hpr)
where
  premW_dprem {els ρ pr} (h : PremW env (DDerives env O) els ρ pr) : DPrem env O els ρ pr := by
    induction h with
    | ifPr h => exact .ifPr h
    | elsePr h => exact .elsePr h
    | letPr h₁ h₂ => exact .letPr h₁ h₂
    | rulePr ha he hd => exact .rulePr ha he hd
    | iterOptNone hd hn hs => exact .iterOptNone hd hn hs
    | iterOptSome hd hn hs _ ih => exact .iterOptSome hd hn hs ih
    | iterList hit hd hn hl hk _ ih => exact .iterList hit hd hn hl hk ih
    | iterListN hd he hk hl hlen _ ih => exact .iterListN hd he hk hl hlen ih

/-- A relation without parameters, read declaratively, is the union of its rules' `Fires`. -/
theorem dderives_iff_fires {env : Env} {x : IL.Id} {v : Value} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some ([], "%~>%", t, rules)) :
    DDerives env (otherwise env) x "%~>%" [] v ↔ ∃ i, Fires env x i v := by
  rw [dderives_iff]
  constructor
  · rintro ⟨ps, t', rules', i, r, hrel', hrule, hb⟩
    rw [hrel] at hrel'
    obtain ⟨rfl, rfl, rfl⟩ : [] = ps ∧ t = t' ∧ rules = rules' := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
      exact ⟨hrel'.1, hrel'.2.2.1, hrel'.2.2.2⟩
    exact ⟨i, t, rules, r, hrel, hrule, hb⟩
  · rintro ⟨i, t', rules', r, hrel', hrule, hb⟩
    exact ⟨[], t', rules', i, r, hrel', hrule, hb⟩

/-- A derivation from a rule the environment contains, for an explicit assignment. -/
theorem dderives_of_ruleAt {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {k : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (h : HasRuleAt env x op k (.ruleD nm qs op e prems)) (σ : List (IL.Id × Value)) {v : Value}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, DPrem env O (O x [] k v) (VarEnv.empty.bindVals σ) pr) :
    DDerives env O x op [] v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact DDerives.rule hrel hk rfl hq he hp

/-! ## Evaluation helpers -/

/-- A two-component tuple. -/
theorem evalExp_tup2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂]) :=
  evalExp_tupE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

/-- A three-component tuple. -/
theorem evalExp_tup3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [v₁, v₂, v₃]) :=
  evalExp_tupE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)), rfl⟩

/-- A one-element list. -/
theorem evalExp_list1 {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} (h : EvalExp env ρ e v) :
    EvalExp env ρ (.listE [e]) (.list [v]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h evalExps_nil, rfl⟩

/-- A variant case. -/
theorem evalExp_case {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {v : Value}
    (h : EvalExp env ρ e v) : EvalExp env ρ (.caseE op e) (.case op v) :=
  evalExp_caseE_iff.2 ⟨_, h, rfl⟩

/-- A bound variable. -/
theorem evalExp_var {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value} (h : ρ.findVal? x = some v) :
    EvalExp env ρ (.varE x) v :=
  evalExp_varE_iff.2 h

/-- A concatenation of two lists. -/
theorem evalExp_cat {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {a b : List Value}
    (h₁ : EvalExp env ρ e₁ (.list a)) (h₂ : EvalExp env ρ e₂ (.list b)) :
    EvalExp env ρ (.catE e₁ e₂) (.list (a ++ b)) :=
  evalExp_catE_iff.2 ⟨_, _, h₁, h₂, rfl⟩

/-- `x* =/= []` for a non-empty list. -/
theorem evalExp_ne_nil {env : Env} {ρ : VarEnv} {e : Exp} {t : OpTyp} {a : List Value}
    (h : EvalExp env ρ e (.list a)) :
    EvalExp env ρ (.cmpE .neOp t e (.listE [])) (.bool (a ≠ [])) := by
  refine evalExp_cmpE_iff.2 ⟨_, _, h, evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩, ?_⟩
  cases a <;> simp [cmpValues]

/-- `p \/ q` on booleans. -/
theorem evalExp_or {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp} {p q : Prop}
    [Decidable p] [Decidable q]
    (h₁ : EvalExp env ρ e₁ (.bool (decide p))) (h₂ : EvalExp env ρ e₂ (.bool (decide q))) :
    EvalExp env ρ (.binE .orOp t e₁ e₂) (.bool (decide (p ∨ q))) := by
  refine evalExp_binE_iff.2 ⟨_, h₁, ?_⟩
  by_cases hp : p
  · exact .inl (by simp [boolShort, hp])
  · exact .inr ⟨by simp [boolShort, hp], _, h₂, by simp [binValues, boolBin, hp]⟩

/-! ## Assembling a rule instance -/

/-- No quantifiers. -/
theorem QuantsOk.nil {env : Env} {ρ : VarEnv} : QuantsOk env ρ [] := by
  intro _ _ h
  cases h

/-- One more quantifier, bound to a value of its type. -/
theorem QuantsOk.cons {env : Env} {ρ : VarEnv} {x : IL.Id} {t : Typ} {w : Value}
    {qs : List Param} (hx : ρ.findVal? x = some w) (ht : HasTyp env ρ t w)
    (hqs : QuantsOk env ρ qs) : QuantsOk env ρ (.expP x t :: qs) := by
  intro y u hm
  rcases List.mem_cons.1 hm with h | h
  · obtain ⟨rfl, rfl⟩ := Param.expP.inj h
    exact ⟨w, hx, ht⟩
  · exact hqs y u h

/-- A single premise. -/
theorem prems_one {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    (h : DPrem env O els ρ pr) : ∀ p ∈ [pr], DPrem env O els ρ p := by
  intro p hp
  rw [List.mem_singleton.1 hp]
  exact h

/-- Two premises. -/
theorem prems_two {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr₁ pr₂ : Prem}
    (h₁ : DPrem env O els ρ pr₁) (h₂ : DPrem env O els ρ pr₂) :
    ∀ p ∈ [pr₁, pr₂], DPrem env O els ρ p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₁
  · rw [List.mem_singleton.1 hp]
    exact h₂

end Silmaril.Wasm.SpecTec.Sim
