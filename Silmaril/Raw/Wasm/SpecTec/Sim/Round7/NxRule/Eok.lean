module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxRule.Scope

/-!
# Round 7, REH route 2, part (a) at runtime: values in rule instances (unrefined)

* `eOk_of_closed`: in a rule instance whose quantifiers `Sim.QuantsOk` types, an expression
  closed over the quantifiers that passes the flow check evaluates to a value satisfying
  `NxFlow.EOk`, given that definitions conform (`NxSound.DefsVT`) at every fuel.
* `eOk_alt`, `eOk_ifPr`, `eOk_rulePr`: the conclusion alternatives and the top-level `if` and
  relation premises of a rule of a reachable relation.
* `nxB_site`: at a top-level comparison premise that is not one of the six binding sites, one
  operand is export-free at runtime.
* `scope_match`, `scope_prems`: when `Sem.derives` matches a rule of a relation of
  `NxSites.matchedRel` against a conforming value, the scope it builds conforms, and its premises
  keep it conforming.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxRule

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB)

variable {B : Builtins}

/-! ## Closed expressions -/

theorem typsNx_inst (σ : List (IL.Id × Value)) : TypsNx sigX.good (VarEnv.empty.bindVals σ) := by
  intro p hp
  simp [VarEnv.bindVals, VarEnv.empty, Map.empty] at hp

/-- **A closed, checked expression of a rule instance conforms.** -/
theorem eOk_of_closed (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) {qs : List Param}
    {σ : List (IL.Id × Value)} (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
    (hw : "_" ∉ quantNames qs) {e : Exp} {v : Value}
    (hc : varsIn (quantNames qs) (freeExp e) = true) (ht : tyOk sigX tsigFixed (quantsΓ qs) e = true)
    (ha : auxE ctx0 e = true) (hv : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e v) :
    EOk sigX tsigFixed (quantsΓ qs) e v := by
  obtain ⟨n, hn⟩ := hv
  rw [evalExp_agreeOn (agreeOn_qScope hc)] at hn
  have hs := scopeVT_qScope (typsNx_inst σ) hq hw
  have hC := callH_nil hD (ρ := qScope qs (VarEnv.empty.bindVals σ)) rfl rfl n
  exact (expAt _ n).exp sigX tsigFixed (quantsΓ qs) ctx0 _ e v hs hC ht ha hn

/-- An export-free expression has an export-free value. -/
theorem nxB_of_eOk {S : Sig} {T : TSig} {Γ : List (String × AT)} {e : Exp} {v : Value}
    (h : EOk S T Γ e v) (hn : nxE S Γ e = true) : nxB v = true :=
  h.nx (nxD_of_nxE e hn)

/-! ## Sets -/

theorem varsIn_union_left {K : List IL.Id} {s t : Sets} (h : varsIn K (s.union t) = true) :
    varsIn K s = true := by
  have h' := of_decide_eq_true h
  simp only [Sets.union, Finset.mem_union] at h'
  exact decide_eq_true fun x hx => h' x (.inl hx)

theorem varsIn_union_right {K : List IL.Id} {s t : Sets} (h : varsIn K (s.union t) = true) :
    varsIn K t = true := by
  have h' := of_decide_eq_true h
  simp only [Sets.union, Finset.mem_union] at h'
  exact decide_eq_true fun x hx => h' x (.inr hx)

/-! ## Sums -/

theorem foldl_add_eq_zero {α : Type} (f : α → Nat) :
    ∀ (l : List α) (k : Nat), l.foldl (fun k a => k + f a) k = 0 → k = 0 ∧ ∀ a ∈ l, f a = 0
  | [], k, h => ⟨h, fun _ ha => by simp at ha⟩
  | a :: l, k, h => by
    obtain ⟨h1, h2⟩ := foldl_add_eq_zero f l (k + f a) h
    refine ⟨by omega, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · exact h2 b hb

/-! ## The expressions of a rule instance -/

section Inst

variable (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) {x : IL.Id} {ps : List Param}
  {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param}
  {op' : MixopS} {e : Exp} {prems : List Prem} (hx : reach 0 x = true)
  (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
  (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
  (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
include hD hx hrel hrule hq

/-- **Every conclusion alternative conforms.** -/
theorem eOk_alt {e' : Exp} (he' : e' ∈ Round6.Reading.conclAlts e) {v : Value}
    (hv : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e' v) :
    EOk sigX tsigFixed (quantsΓ qs) e' v := by
  have hF := rFacts hx hrel hrule
  obtain ⟨ha, hc⟩ := hF.alts e' he'
  simp only [altOk, Bool.and_eq_true, beq_iff_eq] at ha
  exact eOk_of_closed hD hq hF.wild hc ha.1.1 ha.1.2 hv

/-- **The condition of a top-level `if` premise conforms.** -/
theorem eOk_ifPr {c : Exp} (hpr : Prem.ifPr c ∈ prems) {v : Value}
    (hv : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) c v) :
    EOk sigX tsigFixed (quantsΓ qs) c v := by
  have hF := rFacts hx hrel hrule
  obtain ⟨ht, ha, hc⟩ := hF.premsOk _ hpr
  exact eOk_of_closed hD hq hF.wild hc ht ha hv

/-- **The asserted instance of a top-level relation premise conforms**, and to the type of the
relation it names. -/
theorem eOk_rulePr {y : IL.Id} {args : List Arg} {opy : MixopS} {c : Exp}
    (hpr : Prem.rulePr y args opy c ∈ prems) {v : Value}
    (hv : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) c v) :
    EOk sigX tsigFixed (quantsΓ qs) c v ∧
      ∀ pys ty, tsigFixed.rels.lookup y = some (pys, ty) → vtB sigX ty v = true := by
  have hF := rFacts hx hrel hrule
  obtain ⟨ht, ha, hc⟩ := hF.premsOk _ hpr
  simp only [premTy, ckRulePr, Bool.and_eq_true] at ht
  simp only [premAuxR, Bool.and_eq_true] at ha
  have hc' : varsIn (quantNames qs) (freeExp c) = true := varsIn_union_right hc
  have hok := eOk_of_closed hD hq hF.wild hc' ht.1.2 ha.2 hv
  refine ⟨hok, fun pys ty hl => ?_⟩
  have h2 := ht.2
  rw [hl] at h2
  simp only [Bool.and_eq_true] at h2
  exact hok.ck ty h2.2

/-! ## The comparison sites of a rule instance -/

omit hD hq in
/-- **A top-level premise that is not a binding site has no failing comparison site.** -/
theorem badPr_zero {pr : Prem} (hpr : pr ∈ prems) (hb : bindSite sigX (quantsΓ qs) pr = false) :
    badPr sigX (quantsΓ qs) pr = 0 := by
  have hs := (rFacts hx hrel hrule).sites
  simp only [ruleSites, quantsΓ, List.append_nil] at hs
  have h0 := (foldl_add_eq_zero (badPr sigX (quantsΓ qs))
    (prems.filter fun pr => !bindSite sigX (quantsΓ qs) pr) 0 (by omega)).2 pr
    (List.mem_filter.2 ⟨hpr, by simp [hb]⟩)
  exact h0

/-- **Part (a) at a top-level comparison premise.** At an equality, inequality or membership
test `if e₁ op e₂` of a rule instance that is not one of the six binding sites, the value of one
operand is export-free. -/
theorem nxB_site {c e₁ e₂ : Exp} (hpr : Prem.ifPr c ∈ prems)
    (hc : (∃ o ty, (o = CmpOp.eqOp ∨ o = CmpOp.neOp) ∧ c = .cmpE o ty e₁ e₂) ∨ c = .memE e₁ e₂)
    (hb : bindSite sigX (quantsΓ qs) (.ifPr c) = false) {v₁ v₂ : Value}
    (hv₁ : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e₁ v₁)
    (hv₂ : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e₂ v₂) : nxB v₁ = true ∨ nxB v₂ = true := by
  have hF := rFacts hx hrel hrule
  have hbad := badPr_zero hx hrel hrule hpr hb
  obtain ⟨ht, ha, hcl⟩ := hF.premsOk _ hpr
  simp only [premTy] at ht
  simp only [premAuxR] at ha
  simp only [freePrem] at hcl
  have hsite : siteOk sigX (quantsΓ qs) e₁ e₂ = true ∧ tyOk sigX tsigFixed (quantsΓ qs) e₁ = true ∧
      tyOk sigX tsigFixed (quantsΓ qs) e₂ = true ∧ auxE ctx0 e₁ = true ∧ auxE ctx0 e₂ = true ∧
      varsIn (quantNames qs) (freeExp e₁) = true ∧ varsIn (quantNames qs) (freeExp e₂) = true := by
    rcases hc with ⟨o, ty, ho, rfl⟩ | rfl
    · simp only [badPr, badE, Nat.add_eq_zero_iff] at hbad
      simp only [tyOk, Bool.and_eq_true] at ht
      simp only [auxE, Bool.and_eq_true] at ha
      simp only [freeExp] at hcl
      refine ⟨?_, ht.1, ht.2, ha.1, ha.2, varsIn_union_left hcl, varsIn_union_right hcl⟩
      rcases ho with rfl | rfl <;>
        · simp only [rootBad] at hbad
          split at hbad
          · assumption
          · omega
    · simp only [badPr, badE, Nat.add_eq_zero_iff] at hbad
      simp only [tyOk, Bool.and_eq_true] at ht
      simp only [auxE, Bool.and_eq_true] at ha
      simp only [freeExp] at hcl
      refine ⟨?_, ht.1, ht.2, ha.1, ha.2, varsIn_union_left hcl, varsIn_union_right hcl⟩
      simp only [rootBad] at hbad
      split at hbad
      · assumption
      · omega
  obtain ⟨hs, ht₁, ht₂, ha₁, ha₂, hc₁, hc₂⟩ := hsite
  have h₁ := eOk_of_closed hD hq hF.wild hc₁ ht₁ ha₁ hv₁
  have h₂ := eOk_of_closed hD hq hF.wild hc₂ ht₂ ha₂ hv₂
  simp only [siteOk, Bool.or_eq_true] at hs
  rcases hs with hs | hs
  · exact .inl (nxB_of_eOk h₁ hs)
  · exact .inr (nxB_of_eOk h₂ hs)

end Inst

/-! ## Rules matched by `Sem.derives` -/

section Matched

variable (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) {x : IL.Id} {ps : List Param}
  {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param}
  {op' : MixopS} {e : Exp} {prems : List Prem} (hx : reach 0 x = true)
  (hmx : matchedRel x = true)
  (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
  (hrule : rules[i]? = some (.ruleD nm qs op' e prems))

include hx hmx hrel hrule in
/-- **Matching the conclusion against a conforming value gives a conforming scope.** -/
theorem scope_match {n : Nat} {v : Value} {ρ₁ : VarEnv} (hv : vtB sigX (toAT t) v = true)
    (hm : matchExp n (utf8Env B) VarEnv.empty e v = .ok ρ₁) :
    MatchOk sigX (quantsΓ qs) VarEnv.empty ρ₁ := by
  have hF := rFacts hx hrel hrule
  have hs := ScopeVT.empty sigX (quantsΓ qs)
  exact (matchAt _ n).exp sigX tsigFixed (quantsΓ qs) VarEnv.empty e (toAT t) v ρ₁ hs
    (hF.pat hmx) hv hm

include hD hx hrel hrule in
/-- **The premises keep the scope conforming.** -/
theorem scope_prems {n : Nat} {ρ₁ ρ₂ : VarEnv} (h₁ : MatchOk sigX (quantsΓ qs) VarEnv.empty ρ₁)
    (hp : premsHold n (utf8Env B) ρ₁ prems = .ok ρ₂) : MatchOk sigX (quantsΓ qs) ρ₁ ρ₂ := by
  have hF := rFacts hx hrel hrule
  refine prems_ok (c := ctx0) (fun ρ hd ht => callH_nil hD (by rw [hd, h₁.2.1]; rfl)
    (by rw [ht, h₁.2.2]; rfl) n) prems ρ₂ h₁.1 (fun pr hpr => ⟨(hF.premsOk pr hpr).1, ?_⟩) hp
  have ha := (hF.premsOk pr hpr).2.1
  cases pr with
  | letPr e₁ e₂ =>
    simp only [premAuxR, Bool.and_eq_true] at ha
    exact ha.2
  | _ => rfl

end Matched

end Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
