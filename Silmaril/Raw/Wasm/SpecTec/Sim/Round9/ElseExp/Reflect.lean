module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseExp.Core

/-!
# Round 9, RE: the backward firing at a rule with export-free relation premises (unrefined)

`reflect_coreR` is `ElseBwd.reflect_core` (rule `j` read backward from the erased left-hand side,
with its state quantifier rebound) for rules passing `simpleRuleR`. The new case is a relation
premise `y [] c`: its expression reads only the rule's quantifiers, so on the rebound instance it
evaluates, by `erase_rulePr`, to a value whose erasure is the erased-side value; that value is
export-free (`rulePr_self`), so it is the erased-side value, and the erased-side derivation of `y`
is reused as it is.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

section Reflect

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **The backward firing at a rule `j` that passes `simpleRuleR`**, given that its `otherwise`
premise, if it has one, goes back from the erased left-hand side (`hEl`). -/
theorem reflect_coreR {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    {ri : Rule} {nm : IL.Id} {qs : List Param} {opj : MixopS} {e : Exp} {prems : List Prem}
    {a b c' : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hr : rules[j]? = some (.ruleD nm qs opj e prems))
    (hli : lhsRule ri = true) (hsj : simpleRuleR (.ruleD nm qs opj e prems) = true)
    (hFi : Round8.NxElse.Fired (utf8Env B) "Step_read" [] i (.tuple [a, b]))
    (hEl : Prem.elsePr ∈ prems → ∀ c,
      otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [eraseV a, c']) →
      otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [a, c]))
    (hbody : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [eraseV a, c'])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [eraseV a, c'])) :
    ∃ c, RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [a, c])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [a, c]) := by
  have hrd : reach 0 "Step_read" = true := by decide
  have hsr : Script.stepReach.contains (0, "Step_read") = true := by decide
  have hD := NxFlow.flowSound B hB
  -- rule i
  obtain ⟨ps', op', t', rules', nmi, qsi, ei, premsi, ei', ρ₀i, σi, hrel', hrulei, -, halti, hpsi,
    hqi, hevi⟩ := hFi
  rw [hrel] at hrel'
  cases hrel'
  rw [hrulei] at hri
  cases hri
  have hFi := NxRule.rFacts hrd hrel hrulei
  obtain ⟨-, hρi⟩ := EraseDer.bindParams_nil_args (hFi.params ▸ hpsi)
  subst hρi
  simp only [lhsRule, List.all_eq_true, Bool.and_eq_true] at hli
  obtain ⟨zv, lv, rfl, hlv, hzt⟩ := fired_cfg hB H hrel hrulei halti (hli _ halti).1
    (hli _ halti).2 hqi hevi
  -- rule j, on the erased side
  obtain ⟨e'', halt'', hop, ρ₀, σ', hps, hq', hev', hpr'⟩ := hbody
  have hFj := NxRule.rFacts hrd hrel hr
  obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args (hFj.params ▸ hps)
  subst hρ
  simp only [simpleRuleR, Bool.and_eq_true, List.all_eq_true] at hsj
  obtain ⟨hsc, hsp⟩ := hsj
  have hsc' := hsc e'' halt''
  split at hsc'
  case h_2 => cases hsc'
  rename_i z l hcfg
  simp only [Bool.and_eq_true] at hsc'
  obtain ⟨⟨hok, hqn⟩, hxe⟩ := hsc'
  obtain ⟨z', l', hcfg', hsq, hl, hzn⟩ := lhsOk_parts hok
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨r0, rfl⟩ := cfgVar_some hcfg
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨k, zv', lv', rv', hk, hw, hz', hl'⟩ := eval_cfg hn
  simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true, hlv] at hw
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
  -- the new instance
  have hzw : z ≠ "_" := fun h => hFj.wild (h ▸ stateQ_mem hsq)
  let σj := σ' ++ [(z, zv)]
  have hfz : (VarEnv.empty.bindVals σj).findVal? z = some zv := findVal_snoc_self hzw zv
  have hfo : ∀ y, y ≠ z → (VarEnv.empty.bindVals σj).findVal? y =
      (VarEnv.empty.bindVals σ').findVal? y := fun y hy => findVal_snoc_ne hy zv
  have hnx : ∀ y ty, Param.expP y ty ∈ qs → y ≠ z → Round8.NxTyp.nxT ty = true := by
    intro y ty hy hyz
    simp only [quantsNx, List.all_eq_true] at hqn
    have := hqn _ hy
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hyz
  have hval : ∀ y ty, Param.expP y ty ∈ qs → y ≠ z → ∃ w,
      (VarEnv.empty.bindVals σ').findVal? y = some w ∧ nxB w = true := fun y ty hy hyz =>
    NxSites.nxB_of_quantsOk (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ') hq' hy
      (hnx y ty hy hyz)
  have hagr : Round8.NxTyp.Agr (Round8.NxTyp.nxNames qs) (VarEnv.empty.bindVals σ')
      (VarEnv.empty.bindVals σj) :=
    ⟨fun y hy => hfo y (fun h => hzn (h ▸ hy)), rfl, rfl, rfl⟩
  have hqj : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σj) qs := by
    intro y ty hy
    by_cases hyz : y = z
    · subst hyz
      have := stateQ_type hsq hy
      subst this
      exact ⟨zv, hfz, hasTyp_varT_scope rfl rfl hzt⟩
    · obtain ⟨w, hw, hty⟩ := hq' y ty hy
      obtain ⟨w', hw', hnw⟩ := hval y ty hy hyz
      rw [hw] at hw'
      cases hw'
      refine ⟨w, (hfo y hyz).trans hw, ?_⟩
      have h := Round8.NxTyp.hasTyp_fwd Round8.NxTyp.envN_utf8Env (NxSites.envNx_utf8Env B) hagr
        (Round8.NxTyp.typsTP_inst σ') (Round8.NxTyp.nTy_quant hsr hrel hr hy) hty
      rwa [Swap.eraseV_of_nxB _ hnw] at h
  -- the erased new instance agrees with `σ'` on the quantifiers
  have hag : ∀ s, EraseDer.varsIn (quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals σj)) (VarEnv.empty.bindVals σ') := by
    intro s hs
    refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [Erase.find?_eraseScope]
    by_cases hyz : y = z
    · subst hyz; rw [hfz, hz']; rfl
    · obtain ⟨ty, hty⟩ := mem_quantNames (EraseDer.varsIn_mem hs y hy)
      obtain ⟨w, hw, hnw⟩ := hval y ty hty hyz
      rw [hfo y hyz, hw]
      simp [Swap.eraseV_of_nxB _ hnw]
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σj)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  -- the conclusion on the original side
  have hE := NxErase.erase_alt hD H hrd hrel hr hqj hCE halt'' hxe n
  rw [evalExp_agreeOn (hag _ (hFj.alts _ halt'').2), hn] at hE
  obtain ⟨u, hu, hue⟩ := map_eq_ok hE.symm
  obtain ⟨k₂, zv₂, lv₂, rv₂, hk₂, rfl, hz₂, hl₂⟩ := eval_cfg hu
  have hkk : k₂ = k := by omega
  subst hkk
  rw [hfz] at hz₂
  cases hz₂
  have hagl : VarEnv.AgreeOn (freeExp l) (VarEnv.empty.bindVals σ') (VarEnv.empty.bindVals σj) :=
    Round8.NxElse.agreeOn_of_agr hagr hl
  rw [← evalExp_agreeOn hagl, hl'] at hl₂
  cases hl₂
  refine ⟨rv₂, _, halt'', hop, VarEnv.empty, σj, hps, hqj, ⟨n, hu⟩, fun pr hpr => ?_⟩
  -- the premises on the original side
  have hspr := hsp pr hpr
  cases pr with
  | ifPr c₀ =>
    simp only [premR, Bool.and_eq_true, Bool.not_eq_true'] at hspr
    obtain ⟨hxc, hbs⟩ := hspr
    cases hpr' _ hpr with
    | ifPr h =>
      obtain ⟨n₀, hn₀⟩ := h
      have hE₀ := NxErase.erase_ifPr hD H hrd hrel hr hqj hCE hpr hbs hxc n₀
      rw [evalExp_agreeOn (hag _ (hFj.premsOk _ hpr).2.2), hn₀] at hE₀
      obtain ⟨u₀, hu₀, hue₀⟩ := map_eq_ok hE₀.symm
      exact .ifPr ⟨n₀, by rw [hu₀, eraseV_eq_bool hue₀]⟩
  | elsePr =>
    cases hpr' _ hpr with
    | elsePr h => exact .elsePr (hEl hpr _ h)
  | rulePr y args o c₀ =>
    obtain ⟨rfl, hxc, hnx⟩ := premR_rulePr hspr
    cases hpr' _ hpr with
    | rulePr hav hev hd =>
      obtain ⟨n₀, hn₀⟩ := hev
      have hfc : EraseDer.varsIn (quantNames qs) (freeExp c₀) = true := by
        have h := (hFj.premsOk _ hpr).2.2
        simp only [freePrem] at h
        exact NxRule.varsIn_union_right h
      rw [← evalExp_agreeOn (hag _ hfc)] at hn₀
      exact .rulePr (evalArgs_nil hav)
        ⟨n₀, rulePr_self hD H hrd hrel hr hqj hCE hpr hxc hnx hn₀⟩ hd
  | letPr _ _ => simp [premR] at hspr
  | iterPr _ _ => simp [premR] at hspr

end Reflect

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
