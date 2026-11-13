module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostMods.Basic

/-!
# REI without `HostExportParam`: the host-call rules of `Step` (unrefined)

`ruleFwd_hostM`, `ruleBwd_hostM` are `Round7.EraseDer.ruleFwd_host` and `ruleBwd_host`
(`Raw/…/Round7/EraseDer/HostRule.lean`) with the host hypothesis `HostExportParam` replaced by
`HostModsSub`. The originals use `HostExportParam` only to call
`Round7.Swap.allIn_outcomeV_of_host`; the copies call `allIn_outcomeV_of_mods` instead. Every
other line is unchanged, so the proofs stay unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (QuantsP Hyps xExp eraseP grE gdE grB gdB InAI AIOn
  DefsG defsG_empty defsG_bindVals aiOn_ruleK aiOn_invVars ArgIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames ruleK)
open Round6.Reading (DPremB conclAlts otherwiseB)

open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

section Rules

set_option linter.unusedSectionVars false

variable {Q : Value → Prop} {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {hn : H → String}
  {host : HostSemantics H}
  (HB : Hyps Q grB gdB (utf8Env (Round4Int.BI P hn host)))
  (H' : Hyps (EImg Q) grB gdB (utf8Env (Round4Int.BI P hn host)))
  (hT : TypFwd Q gdB (utf8Env (Round4Int.BI P hn host)))
  (hTb : TypBwd Q gdB (utf8Env (Round4Int.BI P hn host))) (hQA : ∀ r, Q r → AllIn Q r)
  (hinj : Function.Injective hn) (hf : HostFinite host) (hm : HostModsSub host)
  (hb : Round7.HostExportBlind host)
include HB H' hT hTb hQA hinj hf hm hb

/-- **The host-call rules go to the erased side.** -/
theorem ruleFwd_hostM {nm : IL.Id} (hnm : nm ∈ hostNames) :
    RuleFwd Q (utf8Env (Round4Int.BI P hn host)) nm := by
  intro ps op t rules i qs e e' prems σ v hrel hrule halt hq he hps hin
  have hG := hostFacts hrel hrule hnm
  have hee : e' = e := by rw [hG.alts] at halt; exact List.mem_singleton.1 halt
  subst hee
  obtain ⟨ps₃, pat, a₁, z, a₃, hS⟩ := hG.shape
  have heq := hS.eq
  subst heq
  have hD : DefsG gdB (VarEnv.empty.bindVals σ) := defsG_bindVals defsG_empty σ
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ) := typsOk_of_typs (typsOk_empty tyA) rfl
  have hpf := fun pr (hpr : pr ∈ ps₃) =>
    premFwdGen HB H' hT hTb hQA (hS.checked pr hpr).1.1 (hS.checked pr hpr).1.2
      (hps pr (List.mem_append_left _ hpr))
  have hK₃ := aiOn_ruleK HB hD hT0 hq he hin (fun pr hpr => (hS.checked pr hpr).1.1)
    (fun pr hpr => (hpf pr hpr).1)
  -- the `$hostcall` premise on the original side
  have hH := hps _ (mem_hostPr pat a₁ z a₃)
  unfold hostPr at hH
  obtain ⟨v₁, ws, l, hv₁, hws, hcall, hmem⟩ : ∃ v₁ ws l,
      EvalExp (utf8Env (Round4Int.BI P hn host)) (VarEnv.empty.bindVals σ) pat v₁ ∧
      EvalArgs (utf8Env (Round4Int.BI P hn host)) (VarEnv.empty.bindVals σ)
        (hostArgsE a₁ z a₃) ws ∧
      Prims.hostcallCall hn host ws = some (.list l) ∧ v₁ ∈ l := by
    cases hH with
    | ifPr h => exact (evalExp_hostMem_iff P hn host rfl).1 h
  obtain ⟨h₀, s₀, vs₀, os, rfl, hos, hl⟩ := hostcallCall_inv hcall
  obtain rfl := Value.list.inj hl
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hmem
  -- the arguments go across
  have hRa : ErRel Q gdB (freeArgs (hostArgsE a₁ z a₃)) (VarEnv.empty.bindVals σ)
      (VarEnv.empty.bindVals (σ.map eraseP)) :=
    erRel_inst fun x hx w hw => hK₃ x (varsIn_mem hS.argsK x hx) w hw
  obtain ⟨hws', hwsA⟩ := evalArgs_fwd HB hRa hS.args hws
  have hsA : AllIn Q (storeV hn s₀) := by
    have := hwsA (.val (storeV hn s₀)) (by simp [Prims.hostArgs])
    simpa [ArgIn] using this
  have hoA : AllIn Q (outcomeV hn o) :=
    allIn_outcomeV_of_mods hn hm (q_of_allIn_storeV hn hsA) ((hos o).2 ho)
  -- every quantifier is in the swap set
  have hKp := aiOn_invVars hv₁ hoA
  have hxq : QuantsP (AllIn Q) (VarEnv.empty.bindVals σ) qs := fun y ty w hy hw => by
    rcases hS.quants y (List.mem_filterMap.2 ⟨_, hy, rfl⟩) with h | h
    · exact hK₃ y h w hw
    · exact hKp y h w hw
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel Q gdB S (VarEnv.empty.bindVals σ) (VarEnv.empty.bindVals (σ.map eraseP)) :=
    fun S hS' => erRel_inst (ai_of_varsIn hxq hS')
  have hqO : QuantsOk (utf8Env (Round4Int.BI P hn host))
      (VarEnv.empty.bindVals (σ.map eraseP)) qs := by
    intro y ty hy
    obtain ⟨w', hw', hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hG.quants y ty hy
    exact ⟨eraseV w', by rw [findVal?_inst, hw']; rfl,
      hT _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht (hxq y ty w' hy hw') hty⟩
  obtain ⟨he', hv⟩ := evalExp_fwd HB (hR _ hG.closed) hG.concl he
  refine ⟨hv, σ.map eraseP, hqO, he', fun pr hpr' => ?_⟩
  rcases List.mem_append.1 hpr' with hpr' | hpr'
  · exact (hpf pr hpr').2 (hS.checked pr hpr').2 hK₃ hD
      (hR _ (hG.premsClosed pr (List.mem_append_left _ hpr')))
  obtain rfl := List.mem_singleton.1 hpr'
  -- the stripped store has one preimage
  obtain ⟨w₁, sv, w₃, hz, hwe⟩ := evalArgs_var2 hws
  have hsv : sv = storeV hn s₀ := by
    simp only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq] at hwe
    exact hwe.2.1.symm
  subst hsv
  obtain ⟨wz, hwz, htz⟩ := hqO z _ hS.store
  rw [findVal?_inst, hz] at hwz
  obtain rfl := (Option.some.inj hwz).symm
  rw [eraseV_storeV, mapStore_stripModule] at htz
  have hu' := storeV_uniq_typed P hinj htz (ExpEnc.storeNE_stripStore s₀)
  obtain ⟨os', hos', hcall'⟩ := hostcallCall_at hn hinj hf (h := h₀) (vs := vs₀) hu'
  -- the premise on the erased side
  have hpat := (evalExp_fwd HB ((hR _ (hG.premsClosed _ (mem_hostPr pat a₁ z a₃))).mono
    (freePrem_hostPr_pat pat a₁ z a₃)) hS.xpat hv₁).1
  have hws'' := hws'
  rw [eraseA_hostArgs] at hws''
  refine .ifPr ((evalExp_hostMem_iff P hn host rfl).2 ⟨_, _, _, hpat, hws'', hcall', ?_⟩)
  rw [eraseV_outcomeV]
  exact List.mem_map_of_mem ((hos' _).1 (hb.1 h₀ s₀ vs₀ o ((hos o).2 ho)))

end Rules

section Bwd

set_option linter.unusedSectionVars false

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {hn : H → String}
  {host : HostSemantics H} {c : Config H}
  (HB : Hyps (QC c) grB gdB (utf8Env (Round4Int.BI P hn host)))
  (H' : Hyps (EImg (QC c)) grB gdB (utf8Env (Round4Int.BI P hn host)))
  (hT : TypFwd (QC c) gdB (utf8Env (Round4Int.BI P hn host)))
  (hTb : TypBwd (QC c) gdB (utf8Env (Round4Int.BI P hn host)))
  (hQA : ∀ r, QC c r → AllIn (QC c) r) (hsi : StripInj c)
  (hinj : Function.Injective hn) (hf : HostFinite host) (hm : HostModsSub host)
  (hb : Round7.HostExportBlind host)
include HB H' hT hTb hQA hsi hinj hf hm hb

/-- **The host-call rules come back from the erased side**, at the swap set `QC c`. -/
theorem ruleBwd_hostM {nm : IL.Id} (hnm : nm ∈ hostNames) :
    RuleBwd (QC c) (utf8Env (Round4Int.BI P hn host)) nm := by
  intro ps op t rules i qs e e' prems σ' v' hrel hrule halt hq he hps hin
  have hG := hostFacts hrel hrule hnm
  have hee : e' = e := by rw [hG.alts] at halt; exact List.mem_singleton.1 halt
  subst hee
  obtain ⟨ps₃, pat, a₁, z, a₃, hS⟩ := hG.shape
  have heq := hS.eq
  subst heq
  have hD : DefsG gdB (VarEnv.empty.bindVals σ') := defsG_bindVals defsG_empty σ'
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ') := typsOk_of_typs (typsOk_empty tyA) rfl
  have hpf := fun pr (hpr : pr ∈ ps₃) =>
    premBwdGen HB H' hT hTb hQA (hS.checked pr hpr).1.1 (hS.checked pr hpr).1.2
      (hps pr (List.mem_append_left _ hpr))
  have hK₃ := aiOn_ruleK H' hD hT0 hq he hin (fun pr hpr => (hS.checked pr hpr).1.1)
    (fun pr hpr => (hpf pr hpr).1)
  -- the `$hostcall` premise on the erased side
  have hH := hps _ (mem_hostPr pat a₁ z a₃)
  unfold hostPr at hH
  obtain ⟨v₁', ws', l', hv₁', hws', hcall', hmem'⟩ : ∃ v₁ ws l,
      EvalExp (utf8Env (Round4Int.BI P hn host)) (VarEnv.empty.bindVals σ') pat v₁ ∧
      EvalArgs (utf8Env (Round4Int.BI P hn host)) (VarEnv.empty.bindVals σ')
        (hostArgsE a₁ z a₃) ws ∧
      Prims.hostcallCall hn host ws = some (.list l) ∧ v₁ ∈ l := by
    cases hH with
    | ifPr h => exact (evalExp_hostMem_iff P hn host rfl).1 h
  obtain ⟨h₁, s₁, vs₁, os₁, rfl, hos₁, hl⟩ := hostcallCall_inv hcall'
  obtain rfl := Value.list.inj hl
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hmem'
  -- the erased store
  obtain ⟨w₁', sv', w₃', hz', hwe'⟩ := evalArgs_var2 hws'
  have hsv' : sv' = storeV hn s₁ := by
    simp only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq] at hwe'
    exact hwe'.2.1.symm
  subst hsv'
  have hs₁A : AllIn (EImg (QC c)) (storeV hn s₁) := hK₃ z hS.storeK _ hz'
  have hne := storeNE_of_eImg hQA hn hs₁A
  have hu₁ : ∀ s, storeV hn s = storeV hn s₁ → s = s₁ := by
    obtain ⟨wz, hwz, htz⟩ := hq z _ hS.store
    rw [hz'] at hwz
    obtain rfl := (Option.some.inj hwz).symm
    exact storeV_uniq_typed P hinj htz hne
  have hoA' : AllIn (EImg (QC c)) (outcomeV hn o') :=
    allIn_outcomeV_of_mods hn hm (q_of_allIn_storeV hn hs₁A) ((hos₁ o').2 ho')
  -- every quantifier is in the erased swap set
  have hKp := aiOn_invVars hv₁' hoA'
  have hxq : QuantsP (AllIn (EImg (QC c))) (VarEnv.empty.bindVals σ') qs := fun y ty w hy hw => by
    rcases hS.quants y (List.mem_filterMap.2 ⟨_, hy, rfl⟩) with h | h
    · exact hK₃ y h w hw
    · exact hKp y h w hw
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel (QC c) gdB S (VarEnv.empty.bindVals (σ'.map (uneraseP (QC c))))
        (VarEnv.empty.bindVals σ') :=
    fun S hS' => erRel_unerase hQA (ai_of_varsIn hxq hS')
  have hqO : QuantsOk (utf8Env (Round4Int.BI P hn host))
      (VarEnv.empty.bindVals (σ'.map (uneraseP (QC c)))) qs := by
    intro y ty hy
    obtain ⟨w', hw', hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hG.quants y ty hy
    obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA w' (hxq y ty w' hy hw')
    exact ⟨unerase (QC c) w', by rw [findVal?_uninst, hw']; rfl,
      hTb _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht hu₁ (by rw [hu₂]; exact hty)⟩
  obtain ⟨v, hv, hve, hva⟩ := evalExp_bwd HB (hR _ hG.closed) hG.concl he
  have hvu : unerase (QC c) v' = v := hve ▸ unerase_eraseV HB.inj v hva
  refine ⟨hve ▸ allIn_eImg_eraseV v hva, σ'.map (uneraseP (QC c)), hqO, hvu ▸ hv,
    fun pr hpr' => ?_⟩
  rcases List.mem_append.1 hpr' with hpr' | hpr'
  · exact (hpf pr hpr').2 (hS.checked pr hpr').2 hK₃ hD
      (hR _ (hG.premsClosed pr (List.mem_append_left _ hpr')))
  obtain rfl := List.mem_singleton.1 hpr'
  -- the arguments come back
  have hRa : ErRel (QC c) gdB (freeArgs (hostArgsE a₁ z a₃))
      (VarEnv.empty.bindVals (σ'.map (uneraseP (QC c)))) (VarEnv.empty.bindVals σ') :=
    erRel_unerase hQA fun x hx w hw => hK₃ x (varsIn_mem hS.argsK x hx) w hw
  obtain ⟨ws, hws, hwsE, hwsA⟩ := evalArgs_bwd HB hRa hS.args hws'
  obtain ⟨w₁, sv, w₃, hz, rfl⟩ := evalArgs_var2 hws
  simp only [Prims.hostArgs, List.map_cons, List.map_nil, List.cons.injEq] at hwsE
  obtain ⟨hw₁, hsvE, hw₃, -⟩ := hwsE
  obtain rfl := eq_of_eraseA_nxB hw₁ (nxB_hostfunc _)
  obtain rfl := eq_of_eraseA_nxB hw₃ (nxB_vals _)
  simp only [eraseA, ArgV.val.injEq] at hsvE
  have hsvA : AllIn (QC c) sv := by
    have := hwsA (.val sv) (by simp)
    simpa [ArgIn] using this
  have hsv := storeV_unstrip hn hsi hne hsvA hsvE
  subst hsv
  -- the original call
  obtain ⟨l₀, hcall₀⟩ := hostcallCall_some hn hf h₁ (mapStore (unstrip c) s₁) vs₁
  obtain ⟨h₀, s₀, vs₀, os₀, hargs, hos₀, hl₀⟩ := hostcallCall_inv hcall₀
  obtain ⟨hh, hst, hvs⟩ := hostArgs_inj hinj hargs
  subst hh hvs
  have hstrip : stripStore s₀ = s₁ := by
    refine hu₁ _ ?_
    rw [← mapStore_stripModule, ← eraseV_storeV, ← hst]
    exact hsvE
  have ho'' := (hos₁ o').2 ho'
  rw [← hstrip] at ho''
  obtain ⟨o, ho, rfl⟩ := hb.2 _ s₀ _ o' ho''
  have hoA : AllIn (QC c) (outcomeV hn o) :=
    allIn_outcomeV_of_mods hn hm (q_of_allIn_storeV hn (hst ▸ hsvA)) ho
  -- the pattern
  obtain ⟨v₁, hv₁, hv₁e, hv₁A⟩ := evalExp_bwd HB ((hR _ (hG.premsClosed _
    (mem_hostPr pat a₁ z a₃))).mono (freePrem_hostPr_pat pat a₁ z a₃)) hS.xpat hv₁'
  have hv₁o : v₁ = outcomeV hn o :=
    eraseV_inj HB.inj hv₁A hoA (by rw [hv₁e, eraseV_outcomeV])
  subst hv₁o
  refine .ifPr ((evalExp_hostMem_iff P hn host rfl).2 ⟨_, _, _, hv₁, hws, hcall₀, ?_⟩)
  rw [Value.list.inj hl₀]
  exact List.mem_map_of_mem ((hos₀ o).1 ho)

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
