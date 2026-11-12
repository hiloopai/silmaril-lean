module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Grow

/-!
# Round 7, moving derivations across erasure: the grow rules commute with erasure (unrefined)

* `growConcl`: the conclusion `(l, (%;% ($W(z, y₂, y₃), r)))` of a grow rule evaluates across
  erasure in both directions, when `z` is bound to a state whose store has no `EXPORTS` field.
* `ruleFwd_grow`, `ruleBwd_grow`: **`table.grow-succeed` and `memory.grow-succeed` satisfy
  `RuleFwd` and `RuleBwd`.** The quantifier `z : state` is typed on the side being read, so
  `state_inv` supplies the state.
* `stepExc_of_stepHost : Task.stepHost → Task.stepExc`: of the four rules outside the check, only
  the two host-call rules are left; hence `stepErase_of_stepHost`, `swapEquiv_of_stepHost` and
  `wholeStepValidREI_of_stepHost`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (QuantsP Hyps xExp eraseP grE gdE grB gdB InAI DefsG
  defsG_empty defsG_bindVals aiOn_ruleK)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (detFacts quantNames)
open Round6.Reading (DPremB conclAlts otherwiseB)

variable {Q : Value → Prop}

/-! ## The conclusion -/

theorem evalExp_growE_iff {env : Env} {ρ : VarEnv} {l r : Exp} {w y₂ y₃ : IL.Id} {v : Value} :
    EvalExp env ρ (growE l w y₂ y₃ r) v ↔ ∃ vl u vr, EvalExp env ρ l vl ∧
      EvalExp env ρ (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) u ∧
      EvalExp env ρ r vr ∧ v = .tuple [vl, .case "%;%" (.tuple [u, vr])] := by
  simp only [growE, evalExp_tupE_iff, evalExps_cons_iff, evalExps_nil_iff, evalExp_caseE_iff]
  constructor
  · rintro ⟨_, ⟨vl, _, hl, ⟨c, _, ⟨_, ⟨_, ⟨u, _, hu, ⟨vr, _, hr, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl,
      rfl⟩, rfl⟩, rfl⟩
    exact ⟨vl, u, vr, hl, hu, hr, rfl⟩
  · rintro ⟨vl, u, vr, hl, hu, hr, rfl⟩
    exact ⟨_, ⟨vl, _, hl, ⟨_, _, ⟨_, ⟨_, ⟨u, _, hu, ⟨vr, _, hr, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl,
      rfl⟩, rfl⟩, rfl⟩

section Concl

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **The conclusion of a grow rule goes across erasure**, both ways. -/
theorem growConcl (HE : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host)))
    (HB : Hyps Q grB gdB (utf8Env (Round4Int.BI P hn host))) {l r : Exp} {w y₂ y₃ : IL.Id}
    (hw : w = "with_tableinst" ∨ w = "with_meminst") (hxl : xExp grB gdB l = true)
    (hxr : xExp grB gdB r = true) {ρ ρ' : VarEnv}
    (hR : ErRel Q gdB (freeExp (growE l w y₂ y₃ r)) ρ ρ') (hd : ρ.defs = []) {S F : Value}
    (hz : ρ.findVal? "z" = some (stV S F)) (hS : ∀ gs, S = .struct gs → hasExp gs = false)
    (hza : AllIn Q (stV S F)) :
    (∀ v, EvalExp (utf8Env (Round4Int.BI P hn host)) ρ (growE l w y₂ y₃ r) v →
      EvalExp (utf8Env (Round4Int.BI P hn host)) ρ' (growE l w y₂ y₃ r) (eraseV v) ∧
        AllIn Q v) ∧
    (∀ v', EvalExp (utf8Env (Round4Int.BI P hn host)) ρ' (growE l w y₂ y₃ r) v' →
      ∃ v, EvalExp (utf8Env (Round4Int.BI P hn host)) ρ (growE l w y₂ y₃ r) v ∧
        eraseV v = v' ∧ AllIn Q v) := by
  have hl : freeExp l ⊆ freeExp (growE l w y₂ y₃ r) := Sets.subset_union_left _ _
  have hc : freeExp (.caseE "%;%" (.tupE [.callE w [.expA (.varE "z"), .expA (.varE y₂),
      .expA (.varE y₃)], r])) ⊆ freeExp (growE l w y₂ y₃ r) :=
    Sets.Subset.trans (Sets.subset_union_left _ _) (Sets.subset_union_right _ _)
  have hcall : freeExp (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) ⊆
      freeExp (growE l w y₂ y₃ r) := Sets.Subset.trans (Sets.subset_union_left _ _) hc
  have hr : freeExp r ⊆ freeExp (growE l w y₂ y₃ r) :=
    Sets.Subset.trans (Sets.Subset.trans (Sets.subset_union_left _ _) (Sets.subset_union_right _ _))
      hc
  have hW := callW_er P hn host HE hw (hR.mono hcall) hd hz hS hza
  refine ⟨fun v hv => ?_, fun v' hv' => ?_⟩
  · obtain ⟨vl, u, vr, hvl, hu, hvr, rfl⟩ := evalExp_growE_iff.1 hv
    obtain ⟨hl', hla⟩ := evalExp_fwd HB (hR.mono hl) hxl hvl
    obtain ⟨hr', hra⟩ := evalExp_fwd HB (hR.mono hr) hxr hvr
    obtain ⟨hu', hua⟩ := hW.1 u hu
    refine ⟨?_, ?_⟩
    · have he := evalExp_growE_iff.2 ⟨_, _, _, hl', hu', hr', rfl⟩
      simpa [eraseV, eraseVs_eq_map] using he
    · exact EraseAll.ai_tuple.2 (by simp [hla, hua, hra])
  · obtain ⟨vl', u', vr', hvl, hu, hvr, rfl⟩ := evalExp_growE_iff.1 hv'
    obtain ⟨vl, hl', rfl, hla⟩ := evalExp_bwd HB (hR.mono hl) hxl hvl
    obtain ⟨vr, hr', rfl, hra⟩ := evalExp_bwd HB (hR.mono hr) hxr hvr
    obtain ⟨u, hu', rfl, hua⟩ := hW.2 u' hu
    refine ⟨_, evalExp_growE_iff.2 ⟨_, _, _, hl', hu', hr', rfl⟩, by simp [eraseV, eraseVs_eq_map],
      ?_⟩
    exact EraseAll.ai_tuple.2 (by simp [hla, hua, hra])

end Concl

/-! ## The two rules -/

section Rules

set_option linter.unusedSectionVars false

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
  (HE : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host)))
  (HB : Hyps Q grB gdB (utf8Env (Round4Int.BI P hn host)))
  (H' : Hyps (EImg Q) grB gdB (utf8Env (Round4Int.BI P hn host)))
  (hT : TypFwd Q gdB (utf8Env (Round4Int.BI P hn host)))
  (hTb : TypBwd Q gdB (utf8Env (Round4Int.BI P hn host))) (hQA : ∀ r, Q r → AllIn Q r)
include HE HB H' hT hTb hQA

/-- **The grow rules go to the erased side.** -/
theorem ruleFwd_grow {nm : IL.Id} (hnm : nm ∈ growNames) :
    RuleFwd Q (utf8Env (Round4Int.BI P hn host)) nm := by
  intro ps op t rules i qs e e' prems σ v hrel hrule halt hq he hp hin
  have hG := growFacts hrel hrule hnm
  have hee : e' = e := by rw [hG.alts] at halt; exact List.mem_singleton.1 halt
  subst hee
  obtain ⟨l, w, y₂, y₃, r, rfl, hw, hxl, hxr⟩ := growShape_inv hG.shape
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hFd := detFacts step_reach hrel' hrule
  obtain ⟨-, hqK, -, hpK⟩ := hFd.concl _ halt
  have hD : DefsG gdB (VarEnv.empty.bindVals σ) := defsG_bindVals defsG_empty σ
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ) := typsOk_of_typs (typsOk_empty tyA) rfl
  have hpf := fun pr (hpr : pr ∈ prems) =>
    premFwdGen HB H' hT hTb hQA (hG.prems pr hpr).1.1 (hG.prems pr hpr).1.2 (hp pr hpr)
  have hK₀ := aiOn_ruleK HB hD hT0 hq he hin (fun pr hpr => (hG.prems pr hpr).1.1)
    (fun pr hpr => (hpf pr hpr).1)
  have hxq : QuantsP (AllIn Q) (VarEnv.empty.bindVals σ) qs := fun y _ w hy hw =>
    hK₀ y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
      w hw
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel Q gdB S (VarEnv.empty.bindVals σ) (VarEnv.empty.bindVals (σ.map eraseP)) :=
    fun S hS' => erRel_inst (ai_of_varsIn hxq hS')
  obtain ⟨zv, hzv, hzt⟩ := hq "z" _ hG.zq
  obtain ⟨S, F, rfl, hS⟩ := state_inv rfl hzt
  obtain ⟨he', hv⟩ := (growConcl P hn host HE HB hw hxl hxr (hR _ hG.closed) rfl hzv hS
    (hxq "z" _ _ hG.zq hzv)).1 v he
  refine ⟨hv, σ.map eraseP, fun y ty hy => ?_, he', fun pr hpr => ?_⟩
  · obtain ⟨w', hw', hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hG.quants y ty hy
    exact ⟨eraseV w', by rw [findVal?_inst, hw']; rfl,
      hT _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht (hxq y ty w' hy hw') hty⟩
  · exact (hpf pr hpr).2 (hpK pr hpr) hK₀ hD (hR _ (hG.prems pr hpr).2)

/-- **The grow rules come back from the erased side.** -/
theorem ruleBwd_grow {nm : IL.Id} (hnm : nm ∈ growNames) :
    RuleBwd Q (utf8Env (Round4Int.BI P hn host)) nm := by
  intro ps op t rules i qs e e' prems σ' v' hrel hrule halt hq he hp hin
  have hG := growFacts hrel hrule hnm
  have hee : e' = e := by rw [hG.alts] at halt; exact List.mem_singleton.1 halt
  subst hee
  obtain ⟨l, w, y₂, y₃, r, rfl, hw, hxl, hxr⟩ := growShape_inv hG.shape
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hFd := detFacts step_reach hrel' hrule
  obtain ⟨-, hqK, -, hpK⟩ := hFd.concl _ halt
  have hD : DefsG gdB (VarEnv.empty.bindVals σ') := defsG_bindVals defsG_empty σ'
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ') := typsOk_of_typs (typsOk_empty tyA) rfl
  have hpf := fun pr (hpr : pr ∈ prems) =>
    premBwdGen HB H' hT hTb hQA (hG.prems pr hpr).1.1 (hG.prems pr hpr).1.2 (hp pr hpr)
  have hK₀ := aiOn_ruleK H' hD hT0 hq he hin (fun pr hpr => (hG.prems pr hpr).1.1)
    (fun pr hpr => (hpf pr hpr).1)
  have hxq : QuantsP (AllIn (EImg Q)) (VarEnv.empty.bindVals σ') qs := fun y _ w hy hw =>
    hK₀ y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
      w hw
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel Q gdB S (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) (VarEnv.empty.bindVals σ') :=
    fun S hS' => erRel_unerase hQA (ai_of_varsIn hxq hS')
  have hqO : QuantsOk (utf8Env (Round4Int.BI P hn host))
      (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) qs := by
    intro y ty hy
    obtain ⟨w', hw', hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hG.quants y ty hy
    obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA w' (hxq y ty w' hy hw')
    exact ⟨unerase Q w', by rw [findVal?_uninst, hw']; rfl,
      hTb _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht hu₁ (by rw [hu₂]; exact hty)⟩
  obtain ⟨zv, hzv, hzt⟩ := hqO "z" _ hG.zq
  have hza : AllIn Q zv := by
    rw [findVal?_uninst] at hzv
    obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.1 hzv
    exact (unerase_eImg hQA z' (hxq "z" _ z' hG.zq hz')).1
  obtain ⟨S, F, rfl, hS⟩ := state_inv rfl hzt
  obtain ⟨v, hv, hve, hva⟩ := (growConcl P hn host HE HB hw hxl hxr (hR _ hG.closed) rfl hzv hS
    hza).2 v' he
  have hvu : unerase Q v' = v := hve ▸ unerase_eraseV HB.inj v hva
  refine ⟨hve ▸ allIn_eImg_eraseV v hva, σ'.map (uneraseP Q), hqO, hvu ▸ hv, fun pr hpr => ?_⟩
  exact (hpf pr hpr).2 (hpK pr hpr) hK₀ hD (hR _ (hG.prems pr hpr).2)

end Rules

/-! ## At a configuration -/

theorem mem_excNames {nm : IL.Id} (h : nm ∈ excNames) : nm ∈ hostNames ∨ nm ∈ growNames := by
  simp only [excNames, hostNames, growNames, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h <;> simp [h]

/-- **`Task.stepExc` from the host-call rules alone**: the grow rules are proved. -/
theorem stepExc_of_stepHost (hH : Task.stepHost) : Task.stepExc := by
  intro H hn hinj host hf hok hb hp nd r c ts hc hs hi nm hnm
  rcases mem_excNames hnm with hh | hg
  · exact hH H hn hinj host hf hok hb hp nd r c ts hc hs hi nm hh
  · have HE := EraseAll.hyps_BI hi (Silmaril.Wasm.Numerics.Profile.spec nd r) hn host
    have HB := EraseAll.hyps_B hi (Silmaril.Wasm.Numerics.Profile.spec nd r) hn host
    have H' := hyps_eImg_B hi (Silmaril.Wasm.Numerics.Profile.spec nd r) hn host
    obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI (Silmaril.Wasm.Numerics.Profile.spec nd r) hn host) hs.2
    have hT := typFwd_gd (gd' := gdB) (typFwd_utf8Env HE)
    have hTb := typBwd_gd (gd' := gdB) (typBwd_utf8Env HE hK)
    exact ⟨ruleFwd_grow HE HB H' hT hTb hQA_QC hg, ruleBwd_grow HE HB H' hT hTb hQA_QC hg⟩

/-- **`Round7.Swap.Task.stepErase` from the host-call rules.** -/
theorem stepErase_of_stepHost (hH : Task.stepHost) : Task.stepErase :=
  stepErase_of_stepExc (stepExc_of_stepHost hH)

/-- **`Round7.Task.swapEquiv` from the host-call rules.** -/
theorem swapEquiv_of_stepHost (hH : Task.stepHost) : Round7.Task.swapEquiv :=
  swapEquiv_of_stepExc (stepExc_of_stepHost hH)

/-- **`Round7.Task.wholeStepValidREI` from the host-call rules.** -/
theorem wholeStepValidREI_of_stepHost (hH : Task.stepHost) : Round7.Task.wholeStepValidREI :=
  wholeStepValidREI_of_stepExc (stepExc_of_stepHost hH)

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
