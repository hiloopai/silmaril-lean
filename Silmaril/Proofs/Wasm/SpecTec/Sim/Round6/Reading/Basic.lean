module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Basic

/-!
# Round 6: unfolding `DDerivesB`, and the extension of `DDerives`

* `dpremB_toPremW`, `dderivesB_iff`, `dderivesB_of_ruleAt`: the `DDerives` toolkit of
  `Sim/Basic.lean`, for `DDerivesB`.
* `conclAlts_of_not`: a conclusion without an empty-domain option iteration is its own only
  alternative; `ruleBodyB_iff_of_not`: such a rule's body reads the same under both readings.
* `dderivesB_of_dderives`: **every `DDerives` derivation is a `DDerivesB` derivation**, for any
  reading of `otherwise` that is weaker than the one the new derivation uses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

/-! ## Alternatives -/

/-- The conclusion itself is always an alternative. -/
theorem self_mem_conclAlts (e : Exp) : e ∈ conclAlts e := List.mem_cons_self ..

/-- **A conclusion without an empty-domain option iteration is its own only alternative.** -/
theorem conclAlts_of_not {e : Exp} (h : hasOptNil e = false) : conclAlts e = [e] := by
  simp [conclAlts, h]

/-- A rule whose conclusion has no empty-domain option iteration has the same body under both
readings, for every interpretation of its premises. -/
theorem ruleBodyB_iff_of_not {env : Env} {D : Interp} {els : Prop} {ps : List Param}
    {args : List ArgV} {op : MixopS} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
    {prems : List Prem} {v : Value} (h : hasOptNil e = false) :
    RuleBodyB env D els ps args op (.ruleD nm qs op' e prems) v ↔
      RuleBody env D els ps args op (.ruleD nm qs op' e prems) v := by
  simp only [RuleBodyB, conclAlts_of_not h, List.mem_singleton, exists_eq_left]

/-- Every rule body is a rule body under the new reading. -/
theorem ruleBodyB_of_ruleBody {env : Env} {D : Interp} {els : Prop} {ps : List Param}
    {args : List ArgV} {op : MixopS} {r : Rule} {v : Value}
    (h : RuleBody env D els ps args op r v) : RuleBodyB env D els ps args op r v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  exact ⟨e, self_mem_conclAlts e, h⟩

/-! ## Unfolding one step -/

/-- A premise of `DDerivesB` is a `PremW` premise over `DDerivesB` itself. -/
theorem dpremB_toPremW {env : Env} {O : ElseI} :
    ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, DPremB env O els ρ pr →
      PremW env (DDerivesB env O) els ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, _, .elsePr h => .elsePr h
  | _, _, _, .letPr h₁ h₂ => .letPr h₁ h₂
  | _, _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, _, .iterOptNone hd hn hs => .iterOptNone hd hn hs
  | _, _, _, .iterOptSome hd hn hs h => .iterOptSome hd hn hs (dpremB_toPremW h)
  | _, _, _, .iterList hit hd hn hl hk h =>
      .iterList hit hd hn hl hk fun r hr => dpremB_toPremW (h r hr)
  | _, _, _, .iterListN hd he hk hl hlen h =>
      .iterListN hd he hk hl hlen fun r hr => dpremB_toPremW (h r hr)

/-- A `PremW` premise over `DDerivesB` is a premise of `DDerivesB`. -/
theorem premW_toDPremB {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW env (DDerivesB env O) els ρ pr) : DPremB env O els ρ pr := by
  induction h with
  | ifPr h => exact .ifPr h
  | elsePr h => exact .elsePr h
  | letPr h₁ h₂ => exact .letPr h₁ h₂
  | rulePr ha he hd => exact .rulePr ha he hd
  | iterOptNone hd hn hs => exact .iterOptNone hd hn hs
  | iterOptSome hd hn hs _ ih => exact .iterOptSome hd hn hs ih
  | iterList hit hd hn hl hk _ ih => exact .iterList hit hd hn hl hk ih
  | iterListN hd he hk hl hlen _ ih => exact .iterListN hd he hk hl hlen ih

/-- **One step of `DDerivesB`**: some rule of the relation has a body that holds under the new
reading. -/
theorem dderivesB_iff {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} :
    DDerivesB env O x op args v ↔
      ∃ ps t rules i r, env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some r ∧
        RuleBodyB env (DDerivesB env O) (O x args i v) ps args op r v := by
  constructor
  · rintro ⟨hrel, hrule, halt, hps, hq, he, hp⟩
    exact ⟨_, _, _, _, _, hrel, hrule, _, halt, rfl, _, _, hps, hq, he,
      fun pr hpr => dpremB_toPremW (hp pr hpr)⟩
  · rintro ⟨ps, t, rules, i, ⟨nm, qs, op', e, prems⟩, hrel, hrule, e', halt, rfl, ρ₀, σ, hps,
      hq, he, hp⟩
    exact DDerivesB.rule hrel hrule halt hps hq he fun pr hpr => premW_toDPremB (hp pr hpr)

/-- A derivation under the new reading from a rule the environment contains, for an explicit
alternative of its conclusion and an explicit assignment. -/
theorem dderivesB_of_ruleAt {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {k : Nat}
    {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    (h : HasRuleAt env x op k (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (σ : List (IL.Id × Value)) {v : Value}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e' v)
    (hp : ∀ pr ∈ prems, DPremB env O (O x [] k v) (VarEnv.empty.bindVals σ) pr) :
    DDerivesB env O x op [] v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact DDerivesB.rule hrel hk halt rfl hq he hp

/-! ## `DDerivesB` extends `DDerives` -/

mutual
/-- **Every `DDerives` derivation is a `DDerivesB` derivation**, when the new derivation's
reading of `otherwise` is implied by the old one's. -/
theorem dderivesB_of_dderives {env : Env} {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerives env O x op args v → DDerivesB env O' x op args v
  | _, _, _, _, .rule hrel hrule hps hq he hp =>
      .rule hrel hrule (self_mem_conclAlts _) hps hq he fun pr hpr =>
        dpremB_of_dprem hO (hO _ _ _ _) (hp pr hpr)

/-- `dderivesB_of_dderives`, on premises. -/
theorem dpremB_of_dprem {env : Env} {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {els els' : Prop} {ρ : VarEnv} {pr : Prem}, (els → els') → DPrem env O els ρ pr →
      DPremB env O' els' ρ pr
  | _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, hel, .elsePr h => .elsePr (hel h)
  | _, _, _, _, _, .letPr h₁ h₂ => .letPr h₁ h₂
  | _, _, _, _, _, .rulePr ha he hd => .rulePr ha he (dderivesB_of_dderives hO hd)
  | _, _, _, _, _, .iterOptNone hd hn hs => .iterOptNone hd hn hs
  | _, _, _, _, hel, .iterOptSome hd hn hs h => .iterOptSome hd hn hs (dpremB_of_dprem hO hel h)
  | _, _, _, _, hel, .iterList hit hd hn hl hk h =>
      .iterList hit hd hn hl hk fun r hr => dpremB_of_dprem hO hel (h r hr)
  | _, _, _, _, hel, .iterListN hd he hk hl hlen h =>
      .iterListN hd he hk hl hlen fun r hr => dpremB_of_dprem hO hel (h r hr)
end

/-- `dderivesB_of_dderives` at one reading of `otherwise`. -/
theorem dderivesB_of_dderives' {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS}
    {args : List ArgV} {v : Value} (h : DDerives env O x op args v) :
    DDerivesB env O x op args v :=
  dderivesB_of_dderives (fun _ _ _ _ h => h) h

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
