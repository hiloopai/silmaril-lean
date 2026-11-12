module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Img

/-!
# Round 7, moving derivations across erasure: the backward direction (unrefined)

`dderivesB_bwd`: a derivation on the erased side of a checked relation, whose rule instances bind
every quantifier to a value of the erased swap set (`DDerivesBQ (AllIn (EImg Q))`, as
`Round7.EraseAll.dderivesB_AI` at `EImg Q` produces), comes back as a derivation of `unerase Q`
of its value, provided typing comes back (`TypBwd`) and every `otherwise` premise read on the
erased side is read on the original side (`hO`).

At a rule instance the erased scope binds `σ'`; the original scope binds `σ'` un-erased. On the
quantifiers the two are related (`erRel_unerase`), because `unerase Q` is a right inverse of
`eraseV` landing in the swap set (`unerase_eImg`). Values computed on the original side are the
un-erasures of those on the erased side by injectivity (`Swap.unerase_eraseV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope find?_eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP Hyps xPrem xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {Q : Value → Prop}

/-- `unerase Q` on the value of a binding. -/
noncomputable def uneraseP (Q : Value → Prop) (p : IL.Id × Value) : IL.Id × Value :=
  (p.1, unerase Q p.2)

theorem find?_mapV (f : Value → Value) : ∀ (m : Map Value) (x : IL.Id),
    Map.find? (m.map fun p => (p.1, f p.2)) x = (Map.find? m x).map f
  | [], _ => rfl
  | (y, v) :: m, x => by
    simp only [List.map_cons, Map.find?]
    split
    · rfl
    · exact find?_mapV f m x

theorem binds_mapV (f : Value → Value) : ∀ (xs : List (IL.Id × Value)) (m : Map Value),
    (Map.binds m xs).map (fun p => (p.1, f p.2)) =
      Map.binds (m.map fun p => (p.1, f p.2)) (xs.map fun p => (p.1, f p.2))
  | [], _ => rfl
  | (y, u) :: xs, m => by
    have ih := binds_mapV f xs (m.bind y u)
    simp only [Map.binds, List.foldl_cons, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    unfold Map.bind
    split <;> simp

theorem findVal?_uninst (σ' : List (IL.Id × Value)) (x : IL.Id) :
    (VarEnv.empty.bindVals (σ'.map (uneraseP Q))).findVal? x =
      ((VarEnv.empty.bindVals σ').findVal? x).map (unerase Q) := by
  have h₁ : (VarEnv.empty.bindVals (σ'.map (uneraseP Q))).vals =
      (VarEnv.empty.bindVals σ').vals.map fun p => (p.1, unerase Q p.2) := by
    simp only [VarEnv.bindVals, VarEnv.empty, Map.empty]
    exact (binds_mapV (unerase Q) σ' []).symm
  simp only [VarEnv.findVal?, h₁, find?_mapV]

/-- **At a rule instance on the erased side**, the scope binding `σ'` un-erased and the scope
binding `σ'` are related on every set of identifiers whose term variables are bound to values of
the erased swap set. -/
theorem erRel_unerase {gd : String → Bool} (hQA : ∀ r, Q r → AllIn Q r) {S : Sets}
    {σ' : List (IL.Id × Value)}
    (hS : ∀ x ∈ S.varid, ∀ w, (VarEnv.empty.bindVals σ').findVal? x = some w → AllIn (EImg Q) w) :
    ErRel Q gd S (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) (VarEnv.empty.bindVals σ') := by
  have hai : ∀ x ∈ S.varid, ∀ w,
      (VarEnv.empty.bindVals (σ'.map (uneraseP Q))).findVal? x = some w → AllIn Q w := by
    intro x hx w hw
    rw [findVal?_uninst] at hw
    obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hw
    exact (unerase_eImg hQA w' (hS x hx w' hw')).1
  refine ⟨⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    ⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ hp => by cases hp⟩
  · exact (EraseAll.find?_filter_ai _ (hai x hx)).symm
  · show _ = (eraseScope (aiPart Q _)).findVal? x
    rw [find?_eraseScope]
    show _ = Option.map eraseV (Map.find? (List.filter _ _) x)
    rw [EraseAll.find?_filter_ai _ (hai x hx)]
    show _ = Option.map eraseV ((VarEnv.empty.bindVals (σ'.map (uneraseP Q))).findVal? x)
    rw [findVal?_uninst, Option.map_map]
    cases hw : (VarEnv.empty.bindVals σ').findVal? x with
    | none => rfl
    | some w' =>
      simp only [Option.map_some, Function.comp_apply]
      rw [(unerase_eImg hQA w' (hS x hx w' hw)).2]

/-! ## The backward transfer -/

section Bwd

set_option linter.unusedSectionVars false

variable {gr gd : String → Bool} {env : Env}
variable (H : Hyps Q gr gd env) (hF : AllRFacts gr gd env) (hT : TypBwd Q gd env)
  (hQA : ∀ r, Q r → AllIn Q r) {O₂ O : ElseI}
  (hO : ∀ x args i v', O₂ x args i v' → args = [] → AllIn (EImg Q) v' →
    O x [] i (unerase Q v'))
include H hF hT hQA hO

mutual
/-- **A derivation on the erased side comes back.** -/
theorem dderivesB_bwd :
    ∀ {x : IL.Id} {op : MixopS} {args' : List ArgV} {v' : Value}, gr x = true →
      DDerivesBQ (AllIn (EImg Q)) env O₂ x op args' v' →
      args' = [] ∧ DDerivesB env O x op [] (unerase Q v')
  | _, _, args', _, hx, .rule (σ := σ') (ρ₀ := ρ₀) (qs := qs) (ps := ps) hrel hrule halt hps hq
      hxq he hp => by
    have hF := hF hx hrel hrule
    have hargs : args' = [] := (bindParams_nil_args (hF.params ▸ hps)).1
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil_args (hF.params ▸ hps)).2
    have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
        ErRel Q gd S (ρ₀.bindVals (σ'.map (uneraseP Q))) (ρ₀.bindVals σ') := by
      intro S hS
      subst hρ
      exact erRel_unerase hQA (ai_of_varsIn hxq hS)
    have hpar : bindParams VarEnv.empty ps [] = some ρ₀ := by
      rw [hargs] at hps; exact hps
    obtain ⟨hxe, hfe⟩ := hF.alts _ halt
    obtain ⟨v, hv, hve, hva⟩ := evalExp_bwd H (hR _ hfe) hxe he
    have hvu : unerase Q _ = v := hve ▸ unerase_eraseV H.inj v hva
    refine ⟨hargs, .rule (σ := σ'.map (uneraseP Q)) hrel hrule halt hpar ?_ (hvu ▸ hv)
      fun pr hpr => ?_⟩
    · intro y ty hy
      obtain ⟨w', hw', hty⟩ := hq y ty hy
      obtain ⟨ht, hft⟩ := hF.quants y ty hy
      have hw'i := hxq y ty w' hy hw'
      obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA w' hw'i
      refine ⟨unerase Q w', ?_,
        hT _ _ _ _ (hR _ hft) rfl (by subst hρ; rfl) (by subst hρ; rfl) rfl rfl ht hu₁ (by rw [hu₂]; exact hty)⟩
      have h₁ := findVal?_uninst (Q := Q) σ' y
      rw [← hρ] at h₁
      rw [h₁, hw']; rfl
    · exact dpremB_bwd (hF.prems pr hpr).1 (hR _ (hF.prems pr hpr).2)
        (fun h => hO _ _ _ _ h hargs (hve ▸ allIn_eImg_eraseV v hva)) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A premise on the erased side comes back.** -/
theorem dpremB_bwd :
    ∀ {els' els : Prop} {ρ ρ' : VarEnv} {pr : Prem}, xPrem gr gd pr = true →
      ErRel Q gd (freePrem pr) ρ ρ' → (els' → els) →
      DPremBQ (AllIn (EImg Q)) env O₂ els' ρ' pr → DPremB env O els ρ pr
  | _, _, _, _, _, hX, hR, _, .ifPr h => by
    simp only [xPrem] at hX
    obtain ⟨v, hv, hve, -⟩ := evalExp_bwd H hR hX h
    exact .ifPr (EraseAll.eraseV_eq_bool.1 hve ▸ hv)
  | _, _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, hX, hR, _, .letPr h₂ h₁ => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨v₂, hv₂, he₂, ha₂⟩ := evalExp_bwd H (hR.mono (sub_let_right _ _)) hX.2 h₂
    obtain ⟨v₁, hv₁, he₁, ha₁⟩ := evalExp_bwd H (hR.mono (sub_let_left _ _)) hX.1 h₁
    have h₁₂ : v₁ = v₂ := eraseV_inj H.inj ha₁ ha₂ (he₁.trans he₂.symm)
    exact .letPr hv₂ (h₁₂ ▸ hv₁)
  | _, _, _, _, .rulePr x args op e, hX, hR, _, .rulePr ha he hd => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨hnil, hd'⟩ := dderivesB_bwd hX.1.1 hd
    obtain ⟨avs, havs, havse, -⟩ := evalArgs_bwd H (hR.mono (sub_rule_args x args op e)) hX.1.2 ha
    obtain ⟨w, hw, hwe, hwa⟩ := evalExp_bwd H (hR.mono (sub_rule_exp x args op e)) hX.2 he
    have havs' : avs = [] := by
      rw [hnil] at havse; exact List.map_eq_nil_iff.1 havse
    have hwu : unerase Q _ = w := hwe ▸ unerase_eraseV H.inj w hwa
    exact .rulePr (havs' ▸ havs) (hwu ▸ hw) hd'
  | _, _, _, _, .iterPr pr (.mk _ ds), hX, hR, _, .iterOptNone hd hne hall => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨xvs, hxvs, rfl, -⟩ := evalDoms_bwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    refine .iterOptNone hxvs hne fun p hp => ?_
    exact EraseAll.eraseV_eq_optNone.1 (hall (eraseP p) (List.mem_map_of_mem hp))
  | _, _, _, _, .iterPr pr (.mk _ ds), hX, hR, hels, .iterOptSome (xvs := xvs') (row := row') hd
      hne hs hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨xvs, hxvs, hxe, hai⟩ := evalDoms_bwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    subst hxe
    rw [domSomes_erase] at hs
    obtain ⟨row, hrow, hrow'⟩ := Option.map_eq_some_iff.1 hs
    have hrowa := EraseAll.ai_domSomes hai hrow
    have hkeys : row.map Prod.fst = ds.map domVar ++ ([] : List IL.Id) := by
      rw [map_fst_domSomes hrow, map_fst_EvalDoms hxvs, List.append_nil]
    have hR' := hR.bindVals hrowa (bound_sub_rowSet hkeys (boundIter_plain (.inl rfl)))
      (sub_iter_body pr _)
    rw [hrow'] at hR'
    exact .iterOptSome hxvs hne hrow (dpremB_bwd hX.1.1 hR' hels hp)
  | _, _, _, _, .iterPr pr (.mk it ds), hX, hR, hels,
      .iterList (xvs := xvs') (dls := dls') (k := k) hit hd hne hl hlen hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨xvs, hxvs, hxe, hai⟩ := evalDoms_bwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    subst hxe
    rw [domLists_erase] at hl
    obtain ⟨dls, hdls, hdls'⟩ := Option.map_eq_some_iff.1 hl
    refine .iterList hit hxvs hne hdls (lens_unerase (hdls' ▸ hlen)) fun r hr => ?_
    have hrowa := EraseAll.ai_rows hai hdls none k r hr
    have hkeys : r.map Prod.fst = ds.map domVar ++ ([] : List IL.Id) := by
      rw [map_fst_row (lens_unerase (hdls' ▸ hlen)) hr, map_fst_domLists hdls,
        map_fst_EvalDoms hxvs]; rfl
    have hplain : it = .opt ∨ it = .list ∨ it = .list1 := by
      rcases hit with h | ⟨h, _⟩ <;> simp [h]
    have hR' := hR.bindVals hrowa (bound_sub_rowSet hkeys (boundIter_plain hplain))
      (sub_iter_body pr _)
    have hr' : r.map eraseP ∈ iterRows dls' none k := by
      rw [← hdls', EraseAll.iterRows_erase]; exact List.mem_map_of_mem hr
    exact dpremB_bwd hX.1.1 hR' hels (hp _ hr')
  | _, _, _, _, .iterPr pr (.mk (.listN eₙ ido) ds), hX, hR, hels,
      .iterListN (xvs := xvs') (dls := dls') (k := k) hd he hk hl hlen hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨xvs, hxvs, hxe, hai⟩ := evalDoms_bwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    subst hxe
    have hXn : xExp gr gd eₙ = true := by simpa [EraseAll.xIter] using hX.1.2
    obtain ⟨kv, hkv, hkve, -⟩ := evalExp_bwd H (hR.mono (sub_iter_n pr eₙ ido ds)) hXn he
    rw [domLists_erase] at hl
    obtain ⟨dls, hdls, hdls'⟩ := Option.map_eq_some_iff.1 hl
    refine .iterListN hxvs hkv (by rw [← hkve, asNat?_eraseV] at hk; exact hk) hdls
      (lens_unerase (hdls' ▸ hlen)) fun r hr => ?_
    have hrowa := EraseAll.ai_rows hai hdls ido k r hr
    have hkeys : r.map Prod.fst = ds.map domVar ++ ido.toList := by
      rw [map_fst_row (lens_unerase (hdls' ▸ hlen)) hr, map_fst_domLists hdls,
        map_fst_EvalDoms hxvs]
    have hR' := hR.bindVals hrowa
      (bound_sub_rowSet hkeys (EvalFree.boundIter_listN_subset_keySet eₙ ido))
      (sub_iter_body pr _)
    have hr' : r.map eraseP ∈ iterRows dls' ido k := by
      rw [← hdls', EraseAll.iterRows_erase]; exact List.mem_map_of_mem hr
    exact dpremB_bwd hX.1.1 hR' hels (hp _ hr')
termination_by structural _ _ _ _ _ _ _ _ hd => hd
end

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
