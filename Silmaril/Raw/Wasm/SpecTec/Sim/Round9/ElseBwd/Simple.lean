module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.CheckSimple

/-!
# Round 9, RE: the backward firing at the simple pairs (unrefined)

`pairReflect_simple`: `PairReflectB` along `eraseV` at every pair of `simplePairs`.

Rule `i` fired at `(a, b)`, with `a = z; L` (`lhsOk`), so `a = (zv; lv)` where `lv` is
export-free (`fired_cfg`). The simple rule `j` fires on the erased side at `(eraseV a, c')` in an
instance `σ'`; its state quantifier `z` is bound to `eraseV zv`, and its other quantifiers have
export-free values. Rebinding `z` to `zv` gives an instance `σ'.z := zv` whose erasure agrees with
`σ'` on every quantifier. Round 7's equation forms (`NxErase.erase_alt`, `erase_ifPr`) then read
the conclusion and the `if` premises of rule `j` on the original side: the conclusion evaluates to
`(a, c)` for some `c`, and each condition to `true`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

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
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-! ## Small facts -/

/-- At a named type without arguments, typing does not read the scope's values. -/
theorem hasTyp_varT_scope {env : Env} {ρ ρ' : VarEnv} (hρ : ρ.typs = []) (hρ' : ρ'.typs = [])
    {x : IL.Id} {v : Value} (h : HasTyp env ρ (.varT x []) v) : HasTyp env ρ' (.varT x []) v := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ]
  have hl' : localTyp? ρ' x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ']
  rcases n with _ | _ | n
  · simp only [hasTyp] at hn ⊢; exact hn
  · simp only [hasTyp, hl, hl'] at hn ⊢
    simp [evalArgs] at hn
  · simp only [hasTyp, hl, hl'] at hn ⊢
    simpa [evalArgs] using hn

theorem map_eq_ok {α β : Type} {f : α → β} {r : Res α} {b : β} (h : f <$> r = .ok b) :
    ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, by cases h; rfl⟩

theorem eraseV_eq_bool {u : Value} {c : Bool} (h : eraseV u = .bool c) : u = .bool c := by
  cases u with
  | opt o => cases o <;> simp [eraseV] at h
  | bool _ => simpa [eraseV] using h
  | _ => simp [eraseV] at h

theorem evalExp_varE {n : Nat} {env : Env} {ρ : VarEnv} {z : IL.Id} {w : Value}
    (h : evalExp n env ρ (.varE z) = .ok w) : ρ.findVal? z = some w := by
  rcases n with _ | n
  · simp [evalExp] at h
  · simpa [evalExp] using h

theorem cfgVar_some {e : Exp} {z : IL.Id} {l : Exp} (h : cfgVar e = some (z, l)) :
    ∃ r, e = .tupE [.caseE "%;%" (.tupE [.varE z, l]), r] := by
  unfold cfgVar at h
  split at h
  · rename_i op z' l' r
    split at h
    · rename_i hop
      cases h
      exact ⟨r, by rw [hop]⟩
    · cases h
  · cases h

/-- **A conclusion `(z; L, R)` evaluates componentwise**, at a fuel fixed by `n`. -/
theorem eval_cfg {n : Nat} {env : Env} {ρ : VarEnv} {z : IL.Id} {l r : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [.caseE "%;%" (.tupE [.varE z, l]), r]) = .ok w) :
    ∃ k zv lv rv, n = k + 5 ∧ w = .tuple [.case "%;%" (.tuple [zv, lv]), rv] ∧
      ρ.findVal? z = some zv ∧ evalExp k env ρ l = .ok lv := by
  obtain ⟨k₁, a, rv, hn₁, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k₂, a₀, hn₂, ha₀, rfl⟩ := evalExp_caseE ha
  obtain ⟨k₃, zv, lv, hn₃, hz, hl, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  exact ⟨k₃, zv, lv, rv, by omega, rfl, evalExp_varE hz, hl⟩

theorem findVal_snoc_self {σ : List (IL.Id × Value)} {z : IL.Id} (hz : z ≠ "_") (u : Value) :
    (VarEnv.empty.bindVals (σ ++ [(z, u)])).findVal? z = some u := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, List.foldl_append, hz]

theorem findVal_snoc_ne {σ : List (IL.Id × Value)} {z y : IL.Id} (hy : y ≠ z) (u : Value) :
    (VarEnv.empty.bindVals (σ ++ [(z, u)])).findVal? y = (VarEnv.empty.bindVals σ).findVal? y := by
  simp only [VarEnv.bindVals, VarEnv.findVal?, Map.binds, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [Map.find?_bind]
  simp [Ne.symm hy]

theorem mem_quantNames {qs : List Param} {x : IL.Id} (h : x ∈ quantNames qs) :
    ∃ t, Param.expP x t ∈ qs := by
  simp only [quantNames, List.mem_filterMap] at h
  obtain ⟨q, hq, hx⟩ := h
  cases q with
  | expP y t => cases hx; exact ⟨t, hq⟩
  | _ => cases hx

theorem stateQ_type {qs : List Param} {z : IL.Id} (h : stateQ qs z = true) {t : Typ}
    (ht : Param.expP z t ∈ qs) : t = .varT "state" [] := by
  simp only [stateQ, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.2 _ ht
  simp only [bne_self_eq_false, Bool.false_or] at h'
  unfold isStateT at h'
  split at h'
  · rename_i x; simp only [beq_iff_eq] at h'; rw [h']
  · cases h'

theorem stateQ_mem {qs : List Param} {z : IL.Id} (h : stateQ qs z = true) : z ∈ quantNames qs := by
  simp only [stateQ, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1

/-- The parts of `lhsOk`. -/
theorem lhsOk_parts {qs : List Param} {e : Exp} (h : lhsOk qs e = true) :
    ∃ z l, cfgVar e = some (z, l) ∧ stateQ qs z = true ∧
      EraseDer.varsIn (Round8.NxTyp.nxNames qs) (freeExp l) = true ∧
      z ∉ Round8.NxTyp.nxNames qs := by
  unfold lhsOk at h
  split at h
  · rename_i z l hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have h2 : (Round8.NxTyp.nxNames qs).contains z = false := h.2
    exact ⟨z, l, hc, h.1.1, h.1.2, fun hm => by rw [List.contains_iff_mem.2 hm] at h2; cases h2⟩
  · cases h

section Simple

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **The left-hand side of a firing of rule `i`** is `(zv; lv)` with `lv` export-free and `zv`
of type `state`. -/
theorem fired_cfg {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} {e' : Exp}
    {σ : List (IL.Id × Value)} {a b : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hok : lhsOk qs e' = true) (hxe : xExp grE gdE e' = true)
    (hq : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
    (hev : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e' (.tuple [a, b])) :
    ∃ zv lv, a = .case "%;%" (.tuple [zv, lv]) ∧ eraseV lv = lv ∧
      HasTyp (utf8Env B) (VarEnv.empty.bindVals σ) (.varT "state" []) zv := by
  have hr : reach 0 "Step_read" = true := by decide
  obtain ⟨z, l, hc, hsq, hl, -⟩ := lhsOk_parts hok
  obtain ⟨r, rfl⟩ := cfgVar_some hc
  obtain ⟨n, hn⟩ := hev
  obtain ⟨k, zv, lv, rv, hk, hw, hz, hlv⟩ := eval_cfg hn
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw
  obtain ⟨rfl, -⟩ := hw
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hE := NxErase.erase_alt (NxFlow.flowSound B hB) H hr hrel hrule hq hCE halt hxe n
  rw [hn] at hE
  obtain ⟨k', zv', lv', rv', hk', hw', -, hlv'⟩ := eval_cfg hE
  have hkk : k' = k := by omega
  subst hkk
  rw [← evalExp_agreeOn (Round8.NxElse.agreeOn_of_agr (Round8.NxTyp.agr_inst hq) hl), hlv]
    at hlv'
  cases hlv'
  refine ⟨zv, lv, rfl, ?_, ?_⟩
  · simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq,
      Value.case.injEq, true_and, and_true] at hw'
    exact hw'.1.2
  · obtain ⟨tz, htz⟩ := mem_quantNames (stateQ_mem hsq)
    have htz' := stateQ_type hsq htz
    subst htz'
    obtain ⟨w, hw, hty⟩ := hq z _ htz
    rw [hz] at hw
    cases hw
    exact hty

/-- **The backward firing at a rule `j` that passes `simpleRuleE`**, given that its `otherwise`
premise, if it has one, goes back from the erased left-hand side (`hEl`). -/
theorem reflect_core {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    {ri : Rule} {nm : IL.Id} {qs : List Param} {opj : MixopS} {e : Exp} {prems : List Prem}
    {a b c' : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hr : rules[j]? = some (.ruleD nm qs opj e prems))
    (hli : lhsRule ri = true) (hsj : simpleRuleE (.ruleD nm qs opj e prems) = true)
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
  simp only [simpleRuleE, Bool.and_eq_true, List.all_eq_true] at hsj
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
  split at hspr
  case h_3 => cases hspr
  case h_2 =>
    cases hpr' _ hpr with
    | elsePr h => exact .elsePr (hEl hpr _ h)
  rename_i c₀
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hspr
  obtain ⟨hxc, hbs⟩ := hspr
  cases hpr' _ hpr with
  | ifPr h =>
    obtain ⟨n₀, hn₀⟩ := h
    have hE₀ := NxErase.erase_ifPr hD H hrd hrel hr hqj hCE hpr hbs hxc n₀
    rw [evalExp_agreeOn (hag _ (hFj.premsOk _ hpr).2.2), hn₀] at hE₀
    obtain ⟨u₀, hu₀, hue₀⟩ := map_eq_ok hE₀.symm
    exact .ifPr ⟨n₀, by rw [hu₀, eraseV_eq_bool hue₀]⟩

/-- `simpleRule` is `simpleRuleE` without `otherwise`. -/
theorem simpleRule_parts {r : Rule} (h : simpleRule r = true) :
    simpleRuleE r = true ∧ ∀ nm qs op e prems, r = .ruleD nm qs op e prems →
      Prem.elsePr ∉ prems := by
  obtain ⟨nm, qs, op, e, prems⟩ := r
  simp only [simpleRule, simpleRuleE, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1, fun pr hpr => ?_⟩, ?_⟩
  · have := h.2 pr hpr
    cases pr <;> simp_all
  · rintro nm' qs' op' e' prems' heq hel
    cases heq
    simpa using h.2 _ hel

/-- The kernel check `simplePairs_fixed`, read at a pair. -/
theorem simplePairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ simplePairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRule ri = true ∧
      simpleRule rj = true := by
  have hm : simplePairsOf rules elsePairs = simplePairs := by
    rw [findRel?_utf8Env] at hrel
    have h := List.all_eq_true.1 simplePairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
    simpa using h
  rw [← hm] at hij
  simp only [simplePairsOf, List.mem_filter] at hij
  obtain ⟨-, hij⟩ := hij
  split at hij
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at hij
    exact ⟨ri, rj, hri, hrj, hij.1, hij.2⟩
  · cases hij

/-- **The backward firing at a simple pair.** -/
theorem pairReflect_simple {i j : Nat} (hij : (i, j) ∈ simplePairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj⟩ := simplePairs_at hB H hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨hsE, hne⟩ := simpleRule_parts hB H hsj
  exact reflect_core hB H hrel hri hr hli hsE hFi
    (fun hel => absurd hel (hne _ _ _ _ _ rfl)) hbody

/-- **`ElseBwdB` from the pairs outside `simplePairs`.** -/
theorem elseBwdB_of_rest (hR : ElseBwdBRest (utf8Env B)) : ElseBwdB (utf8Env B) := by
  intro p hp
  by_cases hs : p ∈ simplePairs
  · exact pairReflect_simple hB H hs
  · exact hR p hp hs

end Simple

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
