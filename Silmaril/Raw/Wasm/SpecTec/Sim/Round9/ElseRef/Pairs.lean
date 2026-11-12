module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseRef.RefOk

/-!
# Round 9, RE: the backward firing at the four `Ref_ok` pairs (unrefined)

* `eval_cfgSF`: a conclusion `((s; f); L, R)` evaluates componentwise.
* `fired_cfgSF`: where an `otherwise` rule with left-hand side `s; f; L` fires, the left-hand side
  is `(sv; fv); lv` with `lv` export-free, `sv` a store and `fv` a frame.
* `reflect_SF`: the backward firing of a rule `s; f; L ~> R -- Ref_ok: (s, e₂, e₃)`
  (`refRuleJ`): `s` and `f` are rebound to `sv` and `fv`, the conclusion goes back by round 7's
  equation `NxErase.erase_alt`, and the `Ref_ok` premise by `refBwd`.
* `pairReflect_ref`: `PairReflectB` along `eraseV` at `(3, 2)`, `(5, 4)`, `(66, 65)`, `(68, 67)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

theorem cfgSF_some {e : Exp} {s f : IL.Id} {l : Exp} (h : cfgSF e = some (s, f, l)) :
    ∃ r, e = .tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE s, .varE f]), l]), r] := by
  unfold cfgSF at h
  split at h
  · rename_i op op' s' f' l' r
    split at h
    · rename_i hop
      cases h
      exact ⟨r, by rw [hop.1, hop.2]⟩
    · cases h
  · cases h

/-- **A conclusion `((s; f); L, R)` evaluates componentwise.** -/
theorem eval_cfgSF {n : Nat} {env : Env} {ρ : VarEnv} {s f : IL.Id} {l r : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE s, .varE f]),
      l]), r]) = .ok w) :
    ∃ k sv fv lv rv, n = k + 5 ∧
      w = .tuple [.case "%;%" (.tuple [.case "%;%" (.tuple [sv, fv]), lv]), rv] ∧
      ρ.findVal? s = some sv ∧ ρ.findVal? f = some fv ∧ evalExp k env ρ l = .ok lv := by
  obtain ⟨k₁, a, rv, hn₁, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k₂, a₀, hn₂, ha₀, rfl⟩ := evalExp_caseE ha
  obtain ⟨k₃, cv, lv, hn₃, hc, hl, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨k₄, c₀, -, hc₀, rfl⟩ := evalExp_caseE hc
  obtain ⟨k₅, sv, fv, -, hs, hf, rfl⟩ := Round8.NxElse.evalExp_pair hc₀
  exact ⟨k₃, sv, fv, lv, rv, by omega, rfl, evalExp_varE hs, evalExp_varE hf, hl⟩

/-- The parts of `lhsOkSF`. -/
theorem lhsOkSF_parts {qs : List Param} {e : Exp} (h : lhsOkSF qs e = true) :
    ∃ s f l, cfgSF e = some (s, f, l) ∧ typQ qs s "store" = true ∧ typQ qs f "frame" = true ∧
      s ≠ f ∧ nxIn qs l = true ∧ s ∉ Round8.NxTyp.nxNames qs ∧
      f ∉ Round8.NxTyp.nxNames qs := by
  unfold lhsOkSF at h
  split at h
  · rename_i s f l hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have h5' : s ∉ Round8.NxTyp.nxNames qs := fun hm => by
      rw [List.contains_iff_mem.2 hm] at h5; cases h5
    have h6' : f ∉ Round8.NxTyp.nxNames qs := fun hm => by
      rw [List.contains_iff_mem.2 hm] at h6; cases h6
    exact ⟨s, f, l, hc, h1, h2, h3, h4, h5', h6'⟩
  · cases h

theorem refPremJ_inv {qs : List Param} {s : IL.Id} {pr : Prem} (h : refPremJ qs s pr = true) :
    ∃ o e₂ e₃, pr = .rulePr "Ref_ok" [] o (.tupE [.varE s, e₂, e₃]) ∧ nxIn qs e₂ = true ∧
      closedNx qs e₃ = true := by
  unfold refPremJ at h
  split at h
  · rename_i y o s' e₂ e₃
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, h₂⟩, h₃⟩ := h
    exact ⟨o, e₂, e₃, rfl, h₂, h₃⟩
  · cases h

section SF

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **The left-hand side of a firing of a rule `s; f; L`** is `(sv; fv); lv` with `lv`
export-free, `sv` a store and `fv` a frame. -/
theorem fired_cfgSF {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} {e' : Exp}
    {σ : List (IL.Id × Value)} {a b : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hok : lhsOkSF qs e' = true) (hxe : xExp grE gdE e' = true)
    (hq : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
    (hev : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e' (.tuple [a, b])) :
    ∃ sv fv lv, a = .case "%;%" (.tuple [.case "%;%" (.tuple [sv, fv]), lv]) ∧ eraseV lv = lv ∧
      HasTyp (utf8Env B) VarEnv.empty (.varT "store" []) sv ∧
      HasTyp (utf8Env B) VarEnv.empty (.varT "frame" []) fv := by
  have hr : reach 0 "Step_read" = true := by decide
  obtain ⟨s, f, l, hc, hsq, hfq, -, hl, -, -⟩ := lhsOkSF_parts hok
  obtain ⟨r, rfl⟩ := cfgSF_some hc
  obtain ⟨n, hn⟩ := hev
  obtain ⟨k, sv, fv, lv, rv, hk, hw, hs, hf, hlv⟩ := eval_cfgSF hn
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw
  obtain ⟨rfl, -⟩ := hw
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hE := NxErase.erase_alt (NxFlow.flowSound B hB) H hr hrel hrule hq hCE halt hxe n
  rw [hn] at hE
  obtain ⟨k', sv', fv', lv', rv', hk', hw', -, -, hlv'⟩ := eval_cfgSF hE
  have hkk : k' = k := by omega
  subst hkk
  rw [← evalExp_agreeOn (Round8.NxElse.agreeOn_of_agr (Round8.NxTyp.agr_inst hq) hl), hlv]
    at hlv'
  cases hlv'
  have hty : ∀ {z : IL.Id} {nme : String} {v : Value}, typQ qs z nme = true →
      (VarEnv.empty.bindVals σ).findVal? z = some v →
      HasTyp (utf8Env B) VarEnv.empty (.varT nme []) v := by
    intro z nme v hzq hz
    obtain ⟨tz, htz⟩ := mem_quantNames (typQ_mem hzq)
    have htz' := typQ_type hzq htz
    subst htz'
    obtain ⟨w, hw, hty⟩ := hq z _ htz
    rw [hz] at hw
    cases hw
    exact hasTyp_varT_scope rfl rfl hty
  refine ⟨sv, fv, lv, rfl, ?_, hty hsq hs, hty hfq hf⟩
  simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq,
    Value.case.injEq, true_and, and_true] at hw'
  exact hw'.1.2

/-- **The backward firing at a rule `s; f; L ~> R -- Ref_ok: (s, e₂, e₃)`.** -/
theorem reflect_SF {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    {ri : Rule} {nm : IL.Id} {qs : List Param} {opj : MixopS} {e : Exp} {prems : List Prem}
    {a b c' : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hr : rules[j]? = some (.ruleD nm qs opj e prems))
    (hli : lhsRuleSF ri = true) (hsj : refRuleJ (.ruleD nm qs opj e prems) = true)
    (hFi : Round8.NxElse.Fired (utf8Env B) "Step_read" [] i (.tuple [a, b]))
    (hbody : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [eraseV a, c'])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [eraseV a, c'])) :
    ∃ c, RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [a, c])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [a, c]) := by
  have hrd : reach 0 "Step_read" = true := by decide
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
  simp only [lhsRuleSF, List.all_eq_true, Bool.and_eq_true] at hli
  obtain ⟨sv, fv, lv, rfl, hlv, hsvt, hfvt⟩ := fired_cfgSF hB H hrel hrulei halti
    (hli _ halti).1 (hli _ halti).2 hqi hevi
  -- rule j, on the erased side
  obtain ⟨e'', halt'', hop, ρ₀, σ', hps, hq', hev', hpr'⟩ := hbody
  have hFj := NxRule.rFacts hrd hrel hr
  obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args (hFj.params ▸ hps)
  subst hρ
  simp only [refRuleJ, List.all_eq_true] at hsj
  have hsc' := hsj e'' halt''
  split at hsc'
  case h_2 => cases hsc'
  rename_i s f l hcfg
  simp only [Bool.and_eq_true, List.all_eq_true] at hsc'
  obtain ⟨⟨⟨⟨hok, hqn⟩, hqv⟩, hxe⟩, hpp⟩ := hsc'
  obtain ⟨s', f', l', hcfg', hsq, hfq, hsf, hl, hsn, hfn⟩ := lhsOkSF_parts hok
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨r0, rfl⟩ := cfgSF_some hcfg
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨k, sv', fv', lv', rv', hk, hw, hs', hf', hl'⟩ := eval_cfgSF hn
  simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true, hlv] at hw
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hw
  -- the new instance
  have hsw : s ≠ "_" := fun h => hFj.wild (h ▸ typQ_mem hsq)
  have hfw : f ≠ "_" := fun h => hFj.wild (h ▸ typQ_mem hfq)
  have hfs : (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])).findVal? s = some sv :=
    (findVal_snoc_ne hsf fv).trans (findVal_snoc_self hsw sv)
  have hff : (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])).findVal? f = some fv :=
    findVal_snoc_self hfw fv
  have hfo : ∀ y, y ≠ s → y ≠ f →
      (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])).findVal? y =
        (VarEnv.empty.bindVals σ').findVal? y := fun y hys hyf =>
    (findVal_snoc_ne hyf fv).trans (findVal_snoc_ne hys sv)
  have hval : ∀ y ty, Param.expP y ty ∈ qs → y ≠ s → y ≠ f → ∃ w,
      (VarEnv.empty.bindVals σ').findVal? y = some w ∧ nxB w = true := fun y ty hy hys hyf =>
    NxSites.nxB_of_quantsOk (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ') hq' hy
      (quantsNxL_mem hqn hy (by simp [hys, hyf]))
  have hagr : Round8.NxTyp.Agr (Round8.NxTyp.nxNames qs) (VarEnv.empty.bindVals σ')
      (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])) :=
    ⟨fun y hy => hfo y (fun h => hsn (h ▸ hy)) (fun h => hfn (h ▸ hy)), rfl, rfl, rfl⟩
  have hqj : QuantsOk (utf8Env B) (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])) qs := by
    intro y ty hy
    by_cases hys : y = s
    · subst hys
      have := typQ_type hsq hy
      subst this
      exact ⟨sv, hfs, hasTyp_varT_scope rfl rfl hsvt⟩
    by_cases hyf : y = f
    · subst hyf
      have := typQ_type hfq hy
      subst this
      exact ⟨fv, hff, hasTyp_varT_scope rfl rfl hfvt⟩
    obtain ⟨w, hw, hty⟩ := hq' y ty hy
    obtain ⟨m, rfl⟩ := quantsVar_mem hqv hy
    exact ⟨w, (hfo y hys hyf).trans hw, hasTyp_var_inst hty⟩
  have hag : ∀ st, EraseDer.varsIn (quantNames qs) st = true →
      VarEnv.AgreeOn st (eraseScope (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])))
        (VarEnv.empty.bindVals σ') := by
    intro st hst
    refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [Erase.find?_eraseScope]
    by_cases hys : y = s
    · subst hys; rw [hfs, hs']; rfl
    by_cases hyf : y = f
    · subst hyf; rw [hff, hf']; rfl
    obtain ⟨ty, hty⟩ := mem_quantNames (EraseDer.varsIn_mem hst y hy)
    obtain ⟨w, hw, hnw⟩ := hval y ty hty hys hyf
    rw [hfo y hys hyf, hw]
    simp [Swap.eraseV_of_nxB _ hnw]
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)]))) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  -- the conclusion on the original side
  have hE := NxErase.erase_alt hD H hrd hrel hr hqj hCE halt'' hxe n
  rw [evalExp_agreeOn (hag _ (hFj.alts _ halt'').2), hn] at hE
  obtain ⟨u, hu, hue⟩ := map_eq_ok hE.symm
  obtain ⟨k₂, sv₂, fv₂, lv₂, rv₂, hk₂, rfl, hs₂, hf₂, hl₂⟩ := eval_cfgSF hu
  have hkk : k₂ = k := by omega
  subst hkk
  rw [hfs] at hs₂
  cases hs₂
  rw [hff] at hf₂
  cases hf₂
  have hagl : VarEnv.AgreeOn (freeExp l) (VarEnv.empty.bindVals σ')
      (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])) :=
    Round8.NxElse.agreeOn_of_agr hagr hl
  rw [← evalExp_agreeOn hagl, hl'] at hl₂
  cases hl₂
  refine ⟨rv₂, _, halt'', hop, VarEnv.empty, σ' ++ [(s, sv)] ++ [(f, fv)], hps, hqj, ⟨n, hu⟩,
    fun pr hpr => ?_⟩
  -- the `Ref_ok` premise on the original side
  obtain ⟨o, e₂, e₃, rfl, h₂, h₃⟩ := refPremJ_inv (hpp pr hpr)
  cases hpr' _ hpr with
  | rulePr hav hev hd =>
    obtain ⟨n₀, hn₀⟩ := hev
    obtain ⟨k₀, sv₀, r₀, t₀, rfl, hs₀, hr₀, ht₀, rfl⟩ := evalExp_triple' hn₀
    have hsv₀ := (evalExp_varE hs₀).symm.trans hs'
    cases hsv₀
    have hcx : closedX qs e₃ = true := by
      simp only [closedNx, Bool.and_eq_true] at h₃; exact h₃.1
    rw [← evalExp_agreeOn (hag _ (closedX_parts hcx).1)] at ht₀
    have hr₀' : evalExp k₀ (utf8Env B) (VarEnv.empty.bindVals (σ' ++ [(s, sv)] ++ [(f, fv)])) e₂ =
        .ok r₀ := by
      rw [← evalExp_agreeOn (Round8.NxElse.agreeOn_of_agr hagr h₂)]; exact hr₀
    exact .rulePr (ElseExp.evalArgs_nil hav)
      ⟨k₀ + 2, evalExp_triple_mk (evalExp_varE_swap hs₀ hfs) hr₀'
        (closedNx_self hD H hqj hCE h₃ ht₀)⟩
      (refBwd hB H hd rfl sv r₀ t₀ rfl hsvt)

end SF

/-- The kernel check `refPairs_fixed`, read at a pair. -/
theorem refPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ ElseExp.refPairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRuleSF ri = true ∧
      refRuleJ rj = true := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 refPairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h _ hij
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2⟩
  · cases h'

section Pairs

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **The backward firing at a `Ref_ok` pair.** -/
theorem pairReflect_ref {i j : Nat} (hij : (i, j) ∈ ElseExp.refPairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj⟩ := refPairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  exact reflect_SF hB H hrel hri hr hli hsj hFi hbody

/-- **`ElseBwdBRef` holds.** -/
theorem elseBwdBRef_holds : ElseExp.ElseBwdBRef (utf8Env B) :=
  fun _ hp => pairReflect_ref hB H hp

/-- **`ElseBwdB` holds**: the backward firing at all 94 pairs of `elsePairs`. -/
theorem elseBwdB_holds : ElseBwdB (utf8Env B) :=
  elseBwdB_of_rest hB H (elseBwdBRest_of_left (elseBwdBLeft_of_left' hB H
    (elseBwdBLeft'_of_left'' hB H (ElseExp.elseBwdBLeft''_of_left3 hB H
      (ElseExp.elseBwdBLeft3_of_ref (elseBwdBRef_holds hB H))))))

end Pairs

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
