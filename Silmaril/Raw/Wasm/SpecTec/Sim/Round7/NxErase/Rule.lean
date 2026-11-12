module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxErase.StepRest
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.Assemble
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.Thms

/-!
# Round 7, REH route 2: rule instances commute with erasure, given the clause half (unrefined)

Parts (a) and the expression half of the copy, put together at the level of rule instances
(`Round6.Reading.DDerivesB`). In a rule instance of a reachable relation whose quantifiers
`Sim.QuantsOk` types, every conclusion alternative and every top-level `if` condition that is not
one of the six binding sites evaluates, on the erased scope, to the erased value, given that
clause bodies commute with erasure in the instance's quantifier scope (`CallE`, which
`Task.clauseErase` states for every such scope).

* `ruleX_of_rels`: the kernel check `xItems_fixed`, read at a rule.
* `eraseScope_qScope`: erasing and keeping the quantifier bindings commute.
* `erase_closed`: the general form, for a closed expression that passes the checks.
* `erase_alt`, `erase_ifPr`: at the conclusion alternatives and at the top-level `if` premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (ER BIErase DefsG eraseP xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-! ## The kernel check at a rule -/

mutual
theorem ruleX_of_rel : ∀ d : Def, xItem d = true → ∀ p ∈ relsOfDef d, reach 0 p.1 = true →
    ∀ r ∈ p.2.2.2.2, ruleX r = true
  | .relD x ps op t rules, hd, p, hp, hr, r, hrm => by
    simp only [relsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only [xItem, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at hd
      rcases hd with hd | hd
      · simp [hd] at hr
      · exact hd r hrm
  | .recD ds, hd, p, hp, hr, r, hrm => by
    simp only [xItem] at hd
    simp only [relsOfDef] at hp
    exact ruleX_of_rels ds hd p hp hr r hrm
  | .typD _ _ _, _, p, hp, _, _, _ => by simp [relsOfDef, Map.empty] at hp
  | .decD _ _ _ _, _, p, hp, _, _, _ => by simp [relsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, p, hp, _, _, _ => by simp [relsOfDef, Map.empty] at hp

theorem ruleX_of_rels : ∀ ds : List Def, xItems ds = true → ∀ p ∈ relsOfDefs ds,
    reach 0 p.1 = true → ∀ r ∈ p.2.2.2.2, ruleX r = true
  | [], _, p, hp, _, _, _ => by simp [relsOfDefs, Map.empty] at hp
  | d :: ds, hd, p, hp, hr, r, hrm => by
    simp only [xItems, Bool.and_eq_true] at hd
    simp only [relsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ruleX_of_rels ds hd.2 p hp hr r hrm
    · exact ruleX_of_rel d hd.1 p hp hr r hrm
end

theorem ruleX_at {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {r : Rule} (hx : reach 0 x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules)) (hr : r ∈ rules) :
    ruleX r = true := by
  rw [findRel?_utf8Env] at hrel
  exact ruleX_of_rels _ xItems_fixed _ (EraseAll.mem_rels_of_findRel' hrel) hx r hr

/-! ## Scopes -/

theorem eraseScope_qScope (qs : List Param) (ρ : VarEnv) :
    eraseScope (qScope qs ρ) = qScope qs (eraseScope ρ) := by
  simp only [eraseScope, qScope, List.filter_map, Function.comp_def]

/-- **A closed expression of a rule instance that passes the checks commutes with erasure**, given
that clause bodies commute with erasure in the instance's quantifier scope. -/
theorem erase_closed {B : Builtins} {gr gd : String → Bool}
    (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) (H : BIErase QT gd (utf8Env B))
    {qs : List Param} {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs) (hw : "_" ∉ quantNames qs)
    (hCE : ∀ k, CallE gd sigX tsigFixed ctx0 (utf8Env B) (qScope qs (VarEnv.empty.bindVals σ)) k)
    {e : Exp} (hc : varsIn (quantNames qs) (freeExp e) = true)
    (ht : tyOk sigX tsigFixed (quantsΓ qs) e = true) (ha : auxE ctx0 e = true)
    (hX : auxX ctx0 e = true) (hb : badE sigX (quantsΓ qs) e = 0) (hx : xExp gr gd e = true)
    (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) e := by
  have hρ := scopeVT_qScope (typsNx_inst σ) hq hw
  have hnc : NCalls gd sigX tsigFixed ctx0 (utf8Env B) (qScope qs (VarEnv.empty.bindVals σ)) n :=
    ⟨callH_nil hD rfl rfl n, hCE n, fun p hp => by
      simp [qScope, VarEnv.bindVals, VarEnv.empty, Map.empty] at hp⟩
  have he := ((nAt H n).exp sigX tsigFixed (quantsΓ qs) ctx0 _ e hρ hnc ht ha hX hb hx).1
  rw [evalExp_agreeOn (agreeOn_qScope (ρ := VarEnv.empty.bindVals σ) hc),
    evalExp_agreeOn (agreeOn_qScope (ρ := eraseScope (VarEnv.empty.bindVals σ)) hc),
    ← eraseScope_qScope]
  exact he

/-! ## At a rule instance -/

section Inst

variable {B : Builtins} {gr gd : String → Bool} (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m)
  (H : BIErase QT gd (utf8Env B)) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
  {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
  {prems : List Prem} (hx : reach 0 x = true)
  (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
  (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
  (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
  (hCE : ∀ k, CallE gd sigX tsigFixed ctx0 (utf8Env B) (qScope qs (VarEnv.empty.bindVals σ)) k)
include hD H hx hrel hrule hq hCE

/-- **Every conclusion alternative of a rule instance commutes with erasure.** -/
theorem erase_alt {e' : Exp} (he' : e' ∈ Round6.Reading.conclAlts e)
    (hxe : xExp gr gd e' = true) (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e' =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) e' := by
  have hF := rFacts hx hrel hrule
  obtain ⟨ha, hc⟩ := hF.alts e' he'
  simp only [altOk, Bool.and_eq_true, beq_iff_eq] at ha
  have hX := ruleX_at hx hrel (List.mem_of_getElem? hrule)
  simp only [ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  exact erase_closed hD H hq hF.wild hCE hc ha.1.1 ha.1.2 (hX.1 e' he') ha.2 hxe n

/-- **Every top-level `if` condition of a rule instance other than the six binding sites
commutes with erasure.** -/
theorem erase_ifPr {c : Exp} (hpr : Prem.ifPr c ∈ prems)
    (hbs : bindSite sigX (quantsΓ qs) (.ifPr c) = false) (hxc : xExp gr gd c = true) (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c := by
  have hF := rFacts hx hrel hrule
  obtain ⟨ht, ha, hc⟩ := hF.premsOk _ hpr
  have hb := badPr_zero hx hrel hrule hpr hbs
  have hX := ruleX_at hx hrel (List.mem_of_getElem? hrule)
  simp only [ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  have hXc := hX.2 _ hpr
  simp only [premX] at hXc
  simp only [premTy] at ht
  simp only [premAuxR] at ha
  simp only [badPr] at hb
  simp only [freePrem] at hc
  exact erase_closed hD H hq hF.wild hCE hc ht ha hXc hb hxc n

end Inst

/-- **`erase_ifPr` from `Task.clauseErase`**, with conforming primitives. -/
theorem erase_ifPr_of_task (hT : Task.clauseErase) {B : Builtins}
    (hB : BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT EraseAll.gdE (utf8Env B))
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : reach 0 x = true) (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs) {c : Exp}
    (hpr : Prem.ifPr c ∈ prems) (hbs : bindSite sigX (quantsΓ qs) (.ifPr c) = false)
    (hxc : xExp EraseAll.grE EraseAll.gdE c = true) (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c :=
  erase_ifPr (NxFlow.flowSound B hB) H hx hrel hrule hq
    (fun k => hT B hB H _ k rfl rfl) hpr hbs hxc n

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
