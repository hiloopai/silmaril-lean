module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.EStepMatch2

/-!
# Round 8 (copy  for `EXPORTS` fields), the whole-evaluator erasure: calls, premises and relations, one step (unrefined)

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

`callDef`, `tryClauses`, `premHolds`, `premsHold`, `premIter`, `premRounds`, `derives` and
`anyRule` at fuel `n + 1`, from `EraseAt … n` and `Hyps`. This is where the hypotheses on the
environment enter: the clauses of a `gd` definition and the rules of a `gr` relation pass the
syntactic check (`Hyps.defs`, `Hyps.rels`), and the builtins of `gd` names commute with erasure
(`Hyps.builtins`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope ScopeIn find?_eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env} {n : Nat}

/-! ## Relation parameters -/

theorem bindParams_erase : ∀ (ρ : VarEnv) (ps : List Param) (ws : List ArgV),
    bindParams (eraseScope ρ) ps (ws.map eraseA) = (bindParams ρ ps ws).map eraseScope
  | ρ, [], [] => rfl
  | ρ, [], _ :: _ => rfl
  | ρ, .expP x _ :: ps, [] => rfl
  | ρ, .typP x :: ps, [] => rfl
  | ρ, .defP x _ _ :: ps, [] => rfl
  | ρ, .gramP x _ _ :: ps, [] => rfl
  | ρ, p :: ps, w :: ws => by
    cases p <;> cases w <;> simp only [List.map_cons, eraseA, bindParams, Option.map_none]
    · rw [← eraseScope_bindVal]; exact bindParams_erase _ ps ws
    · rw [← eraseScope_bindTyp]; exact bindParams_erase _ ps ws
    · rw [← eraseScope_bindDef]; exact bindParams_erase _ ps ws
    · rw [← eraseScope_bindGram]; exact bindParams_erase _ ps ws

theorem bindParams_sg : ∀ {ρ ρ' : VarEnv} {ps : List Param} {ws : List ArgV}, SG Q gd ρ →
    (∀ w ∈ ws, ArgIn Q gd w) → bindParams ρ ps ws = some ρ' → SG Q gd ρ'
  | ρ, ρ', [], [], hρ, _, h => by simp only [bindParams, Option.some.injEq] at h; exact h ▸ hρ
  | ρ, ρ', [], _ :: _, _, _, h => by simp [bindParams] at h
  | ρ, ρ', _ :: _, [], _, _, h => by cases ‹Param› <;> simp [bindParams] at h
  | ρ, ρ', p :: ps, w :: ws, hρ, hw, h => by
    have hw₁ := hw w (List.mem_cons_self ..)
    have hws : ∀ u ∈ ws, ArgIn Q gd u := fun u hu => hw u (List.mem_cons_of_mem _ hu)
    cases p <;> cases w <;> simp only [bindParams] at h <;> try cases h
    · exact bindParams_sg (hρ.bindVal hw₁) hws h
    · exact bindParams_sg (hρ.bindTyp _ _) hws h
    · exact bindParams_sg (hρ.bindDef hw₁) hws h
    · exact bindParams_sg (hρ.bindGram _ _) hws h

theorem ER.isOk {α : Type} {f : α → α} {P : α → Prop} {r r' : Res α} (h : ER f P r r') :
    r'.isOk = r.isOk := by
  rw [h.1]; cases r <;> rfl

/-! ## Calls -/

theorem step_callDef (H : Hyps Q gr gd env) (ih : EraseAt Q gr gd env n) :
    ∀ ρ x l, SG Q gd ρ → gd x = true → xArgs gr gd l = true →
      ER swapX (AllIn Q) (Sem.callDef (n + 1) env ρ x l)
        (Sem.callDef (n + 1) env (eraseScope ρ) x l) := by
  intro ρ x l hρ hx hl
  simp only [Sem.callDef, eraseScope_findDef]
  refine ER.bind (ih.args ρ l hρ hl) fun ws _ hws => ?_
  have hx' := hρ.defName hx
  cases hd : env.findDef? ((ρ.findDef? x).getD x) with
  | none => exact ER.error _
  | some d =>
    simp only [Res.ofOption_some, bind, Except.bind]
    refine ER.elimUndef (ih.tryClauses d.2.2 ws (H.defs _ d hx' hd) hws)
      (fun v _ hv => ER.ok hv) fun _ => ?_
    obtain ⟨hb, hbA⟩ := H.builtins _ ws hx' hws
    exact ER.ofOption hb hbA

theorem step_tryClauses (ih : EraseAt Q gr gd env n) :
    ∀ cs ws, (∀ c ∈ cs, xClause gr gd c = true) → (∀ w ∈ ws, ArgIn Q gd w) →
      ER swapX (AllIn Q) (Sem.tryClauses (n + 1) env cs ws)
        (Sem.tryClauses (n + 1) env cs (ws.map eraseA)) := by
  intro cs ws hcs hws
  cases cs with
  | nil => simp only [Sem.tryClauses]; exact ER.error _
  | cons c cs =>
    obtain ⟨qs, pats, e, prems⟩ := c
    have hc := hcs _ (List.mem_cons_self ..)
    simp only [xClause, Bool.and_eq_true] at hc
    simp only [Sem.tryClauses]
    have hm := ih.matchArgs VarEnv.empty pats ws sg_empty hc.1.1 hws
    rw [eraseScope_empty] at hm
    refine ER.elimUndef (ER.bind hm fun ρ₀ _ hρ₀ => ih.premsHold ρ₀ prems hρ₀ hc.2)
      (fun ρ₁ _ hρ₁ => ih.exp ρ₁ e hρ₁ hc.1.2) fun _ => ?_
    exact ih.tryClauses cs ws (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hws

/-! ## Premises -/

theorem step_premHolds (ih : EraseAt Q gr gd env n) :
    ∀ ρ pr, SG Q gd ρ → xPrem gr gd pr = true →
      ER eraseScope (SG Q gd) (Sem.premHolds (n + 1) env ρ pr)
        (Sem.premHolds (n + 1) env (eraseScope ρ) pr) := by
  intro ρ pr hρ hx
  cases pr with
  | ifPr e =>
    simp only [xPrem] at hx
    simp only [Sem.premHolds]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ _ => ?_
    exact ER.assert swapX_eq_bool.symm fun _ => ER.ok hρ
  | elsePr => simp only [Sem.premHolds]; exact ER.ok hρ
  | letPr e₁ e₂ =>
    simp only [xPrem, Bool.and_eq_true] at hx
    simp only [Sem.premHolds]
    refine ER.bind (ih.exp ρ e₂ hρ hx.2) fun v _ hv => ?_
    exact ih.matchExp ρ e₁ v hρ hx.1 hv
  | rulePr x args op e =>
    simp only [xPrem, Bool.and_eq_true] at hx
    simp only [Sem.premHolds]
    refine ER.bind (ih.args ρ args hρ hx.1.2) fun ws _ hws =>
      ER.bind (ih.exp ρ e hρ hx.2) fun v _ hv => ?_
    rw [ih.derives x op ws v hx.1.1 hws hv]
    split
    · exact ER.ok hρ
    · exact ER.error _
  | iterPr pr it =>
    obtain ⟨it, ds⟩ := it
    simp only [xPrem, Bool.and_eq_true] at hx
    simp only [Sem.premHolds]
    exact ih.premIter ρ pr it ds hρ hx.1.1 hx.1.2 hx.2

theorem step_premsHold (ih : EraseAt Q gr gd env n) :
    ∀ ρ prs, SG Q gd ρ → xPrems gr gd prs = true →
      ER eraseScope (SG Q gd) (Sem.premsHold (n + 1) env ρ prs)
        (Sem.premsHold (n + 1) env (eraseScope ρ) prs) := by
  intro ρ prs hρ hx
  simp only [Sem.premsHold]
  exact ER.foldlM prs hρ fun σ pr hpr hσ => ih.premHolds σ pr hσ (xPrems_mem hx pr hpr)

theorem step_premRounds (ih : EraseAt Q gr gd env n) :
    ∀ ρ pr xvs ido k, SG Q gd ρ → xPrem gr gd pr = true → (∀ p ∈ xvs, AllIn Q p.2) →
      ER eraseScope (SG Q gd) (Sem.premRounds (n + 1) env ρ pr xvs ido k)
        (Sem.premRounds (n + 1) env (eraseScope ρ) pr (xvs.map eraseP) ido k) := by
  intro ρ pr xvs ido k hρ hx hxv
  simp only [Sem.premRounds, mapM_asList_erase]
  cases hds : (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) with
  | none => exact ER.error _
  | some ds =>
    simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
    refine ER.assert (by simp [List.all_map, Function.comp_def]) fun _ => ?_
    rw [iterRows_erase]
    have hrows := allIn_iterRows (allIn_asLists hxv hds) ido k
    refine ER.bind (ER.mapM (f := eraseScope) (P := SG Q gd) (h := List.map eraseP) _
      fun r hr => ?_) fun _ _ _ => ER.ok hρ
    rw [← eraseScope_bindVals]
    exact ih.premHolds _ pr (hρ.bindVals (hrows r hr)) hx

theorem step_premIter (ih : EraseAt Q gr gd env n) :
    ∀ ρ pr it ds, SG Q gd ρ → xPrem gr gd pr = true → xIter gr gd it = true →
      xDoms gr gd ds = true →
      ER eraseScope (SG Q gd) (Sem.premIter (n + 1) env ρ pr it ds)
        (Sem.premIter (n + 1) env (eraseScope ρ) pr it ds) := by
  intro ρ pr it ds hρ hx hit hds
  cases it with
  | opt =>
    simp only [Sem.premIter]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [mapM_asOpt_erase]
    cases hos : (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) with
    | none => exact ER.error _
    | some os =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      have hn : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map swapX)).all
          fun p => p.2.isNone) = os.all fun p => p.2.isNone := by
        simp [List.all_map, Function.comp_def]
      have hs : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map swapX)).all
          fun p => p.2.isSome) = os.all fun p => p.2.isSome := by
        simp [List.all_map, Function.comp_def]
      rw [hn, hs, filterMap_opt_erase]
      split
      · exact ER.ok hρ
      · split
        · rw [← eraseScope_bindVals]
          exact ER.bind (ih.premHolds _ pr (hρ.bindVals (allIn_asOpts hxv hos)) hx)
            fun _ _ _ => ER.ok hρ
        · exact ER.error _
  | list =>
    simp only [Sem.premIter]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.premRounds ρ pr xvs none k hρ hx hxv
  | list1 =>
    simp only [Sem.premIter]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ => ih.premRounds ρ pr xvs none k hρ hx hxv
  | listN eₙ ido =>
    simp only [xIter] at hit
    simp only [Sem.premIter]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv =>
      ER.bind (ih.exp ρ eₙ hρ hit) fun kv _ _ => ?_
    rw [asNat?_eraseC]
    cases kv.asNat? with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.premRounds ρ pr xvs ido k hρ hx hxv

/-! ## Relations -/

theorem step_derives (H : Hyps Q gr gd env) (ih : EraseAt Q gr gd env n) :
    ∀ x op ws v, gr x = true → (∀ w ∈ ws, ArgIn Q gd w) → AllIn Q v →
      Sem.derives (n + 1) env x op (ws.map eraseA) (swapX v) = Sem.derives (n + 1) env x op ws v := by
  intro x op ws v hx hws hv
  simp only [Sem.derives]
  cases hr : env.findRel? x with
  | none => rfl
  | some d =>
    obtain ⟨ps, op', t, rules⟩ := d
    simp only
    rw [ih.anyRule op ps ws v rules (H.rels x _ hx hr) hws hv]

theorem step_anyRule (ih : EraseAt Q gr gd env n) :
    ∀ op ps ws v rs, (∀ r ∈ rs, xRule gr gd r = true) → (∀ w ∈ ws, ArgIn Q gd w) → AllIn Q v →
      Sem.anyRule (n + 1) env op ps (ws.map eraseA) (swapX v) rs =
        Sem.anyRule (n + 1) env op ps ws v rs := by
  intro op ps ws v rs hrs hws hv
  cases rs with
  | nil => simp only [Sem.anyRule]
  | cons r rs =>
    obtain ⟨nm, qs, op', e, prems⟩ := r
    have hr := hrs _ (List.mem_cons_self ..)
    simp only [xRule, Bool.and_eq_true] at hr
    simp only [Sem.anyRule]
    have hbp := bindParams_erase VarEnv.empty ps ws
    rw [eraseScope_empty] at hbp
    have hER : ER eraseScope (SG Q gd)
        (do
          let ρ₀ ← Res.ofOption (bindParams VarEnv.empty ps ws)
          let ρ₁ ← Sem.matchExp n env ρ₀ e v
          Sem.premsHold n env ρ₁ prems)
        (do
          let ρ₀ ← Res.ofOption (bindParams VarEnv.empty ps (ws.map eraseA))
          let ρ₁ ← Sem.matchExp n env ρ₀ e (swapX v)
          Sem.premsHold n env ρ₁ prems) := by
      rw [hbp]
      refine ER.bind (ER.ofOption rfl fun ρ₀ h => bindParams_sg sg_empty hws h) fun ρ₀ _ hρ₀ => ?_
      exact ER.bind (ih.matchExp ρ₀ e v hρ₀ hr.1 hv) fun ρ₁ _ hρ₁ => ih.premsHold ρ₁ prems hρ₁ hr.2
    rw [hER.isOk, ih.anyRule op ps ws v rs (fun r hr' => hrs r (List.mem_cons_of_mem _ hr')) hws hv]

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
