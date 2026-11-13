module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerBind

/-!
# A derivation that avoids the six rules goes to `simEnv20V`

* `sideN`: the relation is `Step`, `Step_pure` or `Step_read`, and the rule is outside
  `patExcl` (the five operator-family rules and `call_addr`).
* **`toSideV`**: a `DDerivesBS sideN` derivation of `simEnv20T B` at a `VOk` value is a
  `DDerivesBS sideV` derivation: at each instance `QuantsV` holds by `quantsV_of_rule`, and each
  premise derivation is at a `VOk` value by `vOk_of_bldB` and the kernel's `premOkB` census.
* **`dderivesBN_toV`**, **`sstepBN_toV`**: so it is a derivation of `simEnv20V B`; in particular
  a `Step` of `simEnv20T B` between `VOk` configurations that uses none of the six rules is a
  `Step` of `simEnv20V B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (ElseI)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB conclAlts SStepB otherwiseB)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (relFreeB bindParams_nil)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (VOk)

/-- **The side condition of the source derivation**: a rule of the three relations outside
`patExcl`. -/
def sideN : SideC := fun x i _ _ => stepRelB x = true ∧ patExcl.contains (x, i) = false

/-- A relation-free premise keeps its derivation under any side condition. -/
theorem relFree_conv {S S' : SideC} {env : Env} {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, relFreeB pr = true → DPremBS S env O els ρ pr →
      DPremBS S' env O els ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, _, .elsePr h => .elsePr h
  | _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, hr, .rulePr _ _ _ => by simp [relFreeB] at hr
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, hr, .iterOptSome hd hne hs hp =>
      .iterOptSome hd hne hs (relFree_conv (by simpa [relFreeB] using hr) hp)
  | _, _, hr, .iterList hit hd hne hl hk hp =>
      .iterList hit hd hne hl hk fun r hm => relFree_conv (by simpa [relFreeB] using hr) (hp r hm)
  | _, _, hr, .iterListN hd he hk hl hlen hp =>
      .iterListN hd he hk hl hlen fun r hm =>
        relFree_conv (by simpa [relFreeB] using hr) (hp r hm)

/-- The three relations have no parameters, and their rules pass both censuses. -/
theorem census_of {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hx : stepRelB x = true)
    (hrel : (simEnv20T B).findRel? x = some (ps, op, t, rules)) :
    ps = [] ∧ (x = "Step" ∨ x = "Step_pure" ∨ x = "Step_read") ∧ censusP x rules = true := by
  simp only [stepRelB, Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with (rfl | rfl) | rfl
  · obtain ⟨t', rules', h', hc⟩ := premCensus_step B
    rw [hrel] at h'; cases h'; exact ⟨rfl, Or.inl rfl, hc⟩
  · obtain ⟨t', rules', h', hc⟩ := premCensus_pure B
    rw [hrel] at h'; cases h'; exact ⟨rfl, Or.inr (Or.inl rfl), hc⟩
  · obtain ⟨t', rules', h', hc⟩ := premCensus_read B
    rw [hrel] at h'; cases h'; exact ⟨rfl, Or.inr (Or.inr rfl), hc⟩

/-- `censusP` at one rule and one conclusion alternative. -/
theorem premOkB_of_census {x : String} {rules : List Rule} (h : censusP x rules = true) {i : Nat}
    {nm : IL.Id} {qs : List Param} {op : MixopS} {e ec : Exp} {prems : List Prem}
    (hr : rules[i]? = some (.ruleD nm qs op e prems)) (hx : patExcl.contains (x, i) = false)
    (hec : ec ∈ conclAlts e) : ∀ pr ∈ prems, premOkB ec pr = true := by
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.1 hr).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hlt)
  simp only [hx, hr, Bool.false_or, List.all_eq_true] at h₁
  exact h₁ ec hec

/-- `QuantsV` at an instance of a rule of `sideN`. -/
theorem quantsV_inst {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    {args : List ArgV} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)} {v : Value}
    (hs : stepRelB x = true ∧ patExcl.contains (x, i) = false)
    (hrel : (simEnv20T B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (he : EvalExp (simEnv20T B) (ρ₀.bindVals σ) e' v) (hv : VOk v) :
    QuantsV (ρ₀.bindVals σ) qs := by
  obtain ⟨rfl, hx3, -⟩ := census_of hs.1 hrel
  obtain rfl := bindParams_nil hps
  exact quantsV_of_rule hx3 hrel hrule hs.2 halt rfl he hv

/-- `premOkB` at a rule of `sideN`. -/
theorem premOk_inst {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    (hs : stepRelB x = true ∧ patExcl.contains (x, i) = false)
    (hrel : (simEnv20T B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e) :
    ∀ pr ∈ prems, premOkB e' pr = true :=
  premOkB_of_census (census_of hs.1 hrel).2.2 hrule hs.2 halt

mutual
/-- **A derivation avoiding the six rules, at a `VOk` value, binds harmlessly.** -/
theorem toSideV {B : Builtins} {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesBS sideN (simEnv20T B) O x op args v → VOk v →
        DDerivesBS sideV (simEnv20T B) O x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq hs he hp, hv =>
    .rule hrel hrule halt hps hq (quantsV_inst hs hrel hrule halt hps he hv) he
      fun pr hpr => premToSideV he hv (premOk_inst hs hrel hrule halt pr hpr) (hp pr hpr)

/-- `toSideV` for premises, against a `VOk` conclusion. -/
theorem premToSideV {B : Builtins} {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {ec : Exp} {vc : Value} {pr : Prem}, EvalExp (simEnv20T B) ρ ec vc → VOk vc →
      premOkB ec pr = true → DPremBS sideN (simEnv20T B) O els ρ pr →
        DPremBS sideV (simEnv20T B) O els ρ pr
  | _, _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, _, _, .elsePr h => .elsePr h
  | _, _, _, _, _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, ec, _, .rulePr _ _ _ ep, hc, hvc, hpo, .rulePr ha he hd => by
    have hb : bldB 64 ec ep = true := by
      simp only [premOkB, Bool.and_eq_true] at hpo
      exact hpo.2
    exact .rulePr ha he (toSideV hd (vOk_of_bldB hc hvc 64 hb he))
  | _, _, _, _, _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, _, _, _, _, hpo, .iterOptSome hd hne hs hp =>
      relFree_conv (by simpa [premOkB] using hpo) (.iterOptSome hd hne hs hp)
  | _, _, _, _, _, _, hpo, .iterList hit hd hne hl hk hp =>
      relFree_conv (by simpa [premOkB] using hpo) (.iterList hit hd hne hl hk hp)
  | _, _, _, _, _, _, hpo, .iterListN hd he hk hl hlen hp =>
      relFree_conv (by simpa [premOkB] using hpo) (.iterListN hd he hk hl hlen hp)
end

/-! ## To `simEnv20V` -/

/-- **A derivation of `simEnv20T B` that avoids the six rules, at a `VOk` value, is one of
`simEnv20V B`.** -/
theorem dderivesBN_toV {B : Builtins} {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (h : DDerivesBS sideN (simEnv20T B) (otherwiseB (simEnv20T B)) x op args v) (hv : VOk v) :
    DDerivesB (simEnv20V B) (otherwiseB (simEnv20V B)) x op args v :=
  dderivesBS_toV' (toSideV h hv)

/-- A step of `simEnv20T B` that uses none of the six rules. -/
def SStepBN (B : Builtins) (c c' : Value) : Prop :=
  DDerivesBS sideN (simEnv20T B) (otherwiseB (simEnv20T B)) "Step" "%~>%" [] (.tuple [c, c'])

/-- **A step of `simEnv20T B` between `VOk` configurations that uses none of the six rules is a
step of `simEnv20V B`.** -/
theorem sstepBN_toV {B : Builtins} {c c' : Value} (h : SStepBN B c c') (hc : VOk c)
    (hc' : VOk c') : SStepB (simEnv20V B) c c' :=
  dderivesBN_toV h (.tuple fun w hw => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl
    · exact hc
    · exact hc')

end Silmaril.Wasm.SpecTec.Sim20.VecDer
