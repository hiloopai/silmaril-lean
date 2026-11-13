module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.EStepMatch

/-!
# Round 8 (copy  for `EXPORTS` fields), the whole-evaluator erasure: `matchExp` and iterated and argument matching (unrefined)

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

`matchExp`, `matchIterE`, `matchIterList`, `matchRounds`, `matchArg` and `matchArgs` at fuel
`n + 1`, from `EraseAt … n`.
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

/-- Matching a list value, in the form the erased side presents it. -/
theorem matchList_er (ih : EraseAt Q gr gd env n) {ρ : VarEnv} {e : Exp} {l : List Value}
    (hρ : SG Q gd ρ) (hx : xExp gr gd e = true) (hl : ∀ v ∈ l, AllIn Q v) :
    ER eraseScope (SG Q gd) (Sem.matchExp n env ρ e (.list l))
      (Sem.matchExp n env (eraseScope ρ) e (.list (l.map swapX))) := by
  have := ih.matchExp ρ e (.list l) hρ hx (allIn_list_of hl)
  rwa [swapX_list'] at this

/-- One split of a concatenation pattern, both halves matched in turn. -/
theorem matchPair_er (ih : EraseAt Q gr gd env n) {ρ : VarEnv} {e₁ e₂ : Exp} {a b : List Value}
    (hρ : SG Q gd ρ) (h₁ : xExp gr gd e₁ = true) (h₂ : xExp gr gd e₂ = true)
    (ha : ∀ v ∈ a, AllIn Q v) (hb : ∀ v ∈ b, AllIn Q v) :
    ER eraseScope (SG Q gd)
      (Sem.matchExp n env ρ e₁ (.list a) >>= fun ρ' => Sem.matchExp n env ρ' e₂ (.list b))
      (Sem.matchExp n env (eraseScope ρ) e₁ (.list (a.map swapX)) >>= fun ρ' =>
        Sem.matchExp n env ρ' e₂ (.list (b.map swapX))) :=
  ER.bind (matchList_er ih hρ h₁ ha) fun _ _ hρ' => matchList_er ih hρ' h₂ hb

theorem ER.res_id {α : Type} (r : Res α) : ER id (fun _ => True) r r :=
  ⟨by cases r <;> rfl, fun _ _ => trivial⟩

theorem step_matchExp (H : Hyps Q gr gd env) (ih : EraseAt Q gr gd env n) :
    ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
      ER eraseScope (SG Q gd) (Sem.matchExp (n + 1) env ρ e v)
        (Sem.matchExp (n + 1) env (eraseScope ρ) e (swapX v)) := by
  have hQ := H.inj
  intro ρ e v hρ hx hv
  have hmd := ih.matchDefault ρ e v hρ hx hv
  cases e with
  | varE x =>
    simp only [Sem.matchExp, find?_eraseScope]
    cases hf : ρ.findVal? x with
    | none =>
      simp only [Option.map_none]
      rw [← eraseScope_bindVal]
      exact ER.ok (hρ.bindVal hv)
    | some w =>
      simp only [Option.map_some]
      have hw := hρ.find? hf
      by_cases h : w = v
      · subst h; simp only [ite_true]; exact ER.ok hρ
      · have h' : swapX w ≠ swapX v := fun h' => h (swapX_inj hQ hw hv h')
        simp only [h, h', ite_false]; exact ER.error _
  | boolE b =>
    simp only [Sem.matchExp]
    exact ER.assert swapX_eq_bool.symm fun _ => ER.ok hρ
  | numE m =>
    simp only [Sem.matchExp]
    exact ER.assert swapX_eq_num.symm fun _ => ER.ok hρ
  | textE t =>
    simp only [Sem.matchExp]
    exact ER.assert swapX_eq_text.symm fun _ => ER.ok hρ
  | unE op t e =>
    have hx' : xExp gr gd e = true := by simpa only [xExp] using hx
    cases op <;> rcases v with b | m | t' | vs | ⟨op', w⟩ | gs | vs | (_ | w) <;>
      simp only [Sem.matchExp, swapX_bool, swapX_num, swapX_text, swapX_tuple, swapX_case,
        swapX_struct, swapX_list, swapX_opt_none, swapX_opt_some] at hmd ⊢ <;>
      first
        | exact hmd
        | exact ER.assert Iff.rfl fun _ => ih.matchExp ρ e (.num m) hρ hx' trivial
        | exact ER.assert Iff.rfl fun _ => ER.bind (ER.res_id _) fun m' _ _ =>
            ih.matchExp ρ e (.num m') hρ hx' trivial
  | tupE es =>
    simp only [xExp] at hx
    simp only [Sem.matchExp, asTuple?_eraseC]
    cases ht : v.asTuple? with
    | none => exact ER.error _
    | some vs =>
      exact ih.matchExps ρ es vs hρ hx (Erase.allIn_asTuple hv ht)
  | projE e i =>
    have hx' : xExp gr gd e = true := by simpa only [xExp] using hx
    simp only [Sem.matchExp]
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      have := ih.matchExp ρ e (.tuple [v]) hρ hx' (allIn_tuple_of (by simpa using hv))
      rw [swapX_tuple'] at this
      exact this
    · simp only [hi, ite_false]
      simpa only [Sem.matchExp, hi, ite_false] using hmd
  | caseE op e =>
    simp only [xExp] at hx
    simp only [Sem.matchExp, asCase?_eraseC]
    cases ht : v.asCase? with
    | none => exact ER.error _
    | some p =>
      obtain ⟨op', w⟩ := p
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ => ih.matchExp ρ e w hρ hx (Erase.allIn_asCase hv ht)
  | uncaseE e op =>
    simp only [xExp] at hx
    simp only [Sem.matchExp]
    exact ih.matchExp ρ e (.case op v) hρ hx hv
  | optE eo =>
    cases eo with
    | none =>
      simp only [Sem.matchExp]
      exact ER.assert swapX_eq_optNone.symm fun _ => ER.ok hρ
    | some e =>
      simp only [xExp, xOExp] at hx
      simp only [Sem.matchExp, asOpt?_eraseC]
      cases ht : v.asOpt? with
      | none => exact ER.error _
      | some o =>
        simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
        cases o with
        | none => exact ER.error _
        | some w =>
          exact ih.matchExp ρ e w hρ hx (Erase.allIn_asOpt hv ht w rfl)
  | strE fs =>
    simp only [xExp] at hx
    simp only [Sem.matchExp, asStruct?_eraseC]
    cases v with
    | struct gs =>
      exact ih.matchExpFields ρ fs gs hρ hx (allIn_struct_fields hv)
    | opt o => cases o <;> exact ER.error _
    | _ => exact ER.error _
  | listE es =>
    simp only [xExp] at hx
    simp only [Sem.matchExp, asList?_eraseC]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs =>
      have hvs : ∀ w ∈ vs, AllIn Q w := by
        cases v with
        | list l => simp only [Value.asList?, Option.some.injEq] at ht; subst ht; exact allIn_list_mem hv
        | opt o => cases o <;> simp [Value.asList?] at ht
        | _ => simp [Value.asList?] at ht
      exact ih.matchExps ρ es vs hρ hx hvs
  | catE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [Sem.matchExp, asList?_eraseC]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs =>
      have hvs : ∀ w ∈ vs, AllIn Q w := by
        cases v with
        | list l => simp only [Value.asList?, Option.some.injEq] at ht; subst ht; exact allIn_list_mem hv
        | opt o => cases o <;> simp [Value.asList?] at ht
        | _ => simp [Value.asList?] at ht
      have htk : ∀ k, ∀ w ∈ vs.take k, AllIn Q w := fun k w hw => hvs w (List.mem_of_mem_take hw)
      have hdk : ∀ k, ∀ w ∈ vs.drop k, AllIn Q w := fun k w hw => hvs w (List.mem_of_mem_drop hw)
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind,
        ih.patLen ρ e₁ hρ hx.1, ih.patLen ρ e₂ hρ hx.2, List.length_map, ← List.map_take,
        ← List.map_drop]
      refine ER.elimUndef (ER.res_id _) (fun k _ _ => ?_) fun _ => ?_
      · exact ER.assert Iff.rfl fun _ => matchPair_er ih hρ hx.1 hx.2 (htk k) (hdk k)
      · refine ER.elimUndef (ER.res_id _) (fun k _ _ => ?_) fun _ => ?_
        · exact ER.assert Iff.rfl fun _ =>
            matchPair_er ih hρ hx.1 hx.2 (htk _) (hdk _)
        · exact ER.scan (fun j => matchPair_er ih hρ hx.1 hx.2 (htk j) (hdk j)) _ _
  | iterE e it =>
    obtain ⟨it, ds⟩ := it
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [Sem.matchExp]
    exact ih.matchIterE ρ e it ds v hρ hx.1.1 hx.1.2 hx.2 hv
  | cvtE e t₁ t₂ =>
    have hx' : xExp gr gd e = true := by simpa only [xExp] using hx
    rcases v with b | m | t' | vs | ⟨op', w⟩ | gs | vs | (_ | w) <;>
      simp only [Sem.matchExp, swapX_bool, swapX_num, swapX_text, swapX_tuple, swapX_case,
        swapX_struct, swapX_list, swapX_opt_none, swapX_opt_some] at hmd ⊢ <;>
      first
        | exact hmd
        | exact ER.bind (ER.res_id _) fun m' _ _ => ih.matchExp ρ e (.num m') hρ hx' trivial
  | subE e t₁ t₂ =>
    simp only [xExp] at hx
    simp only [Sem.matchExp]
    exact ih.matchExp ρ e v hρ hx hv
  | _ => simp only [Sem.matchExp]; simpa only [Sem.matchExp] using hmd

theorem asList_allIn {v : Value} {vs : List Value} (hv : AllIn Q v) (ht : v.asList? = some vs) :
    ∀ w ∈ vs, AllIn Q w := by
  cases v with
  | list l => simp only [Value.asList?, Option.some.injEq] at ht; subst ht; exact allIn_list_mem hv
  | opt o => cases o <;> simp [Value.asList?] at ht
  | _ => simp [Value.asList?] at ht

theorem step_matchIterE (ih : EraseAt Q gr gd env n) :
    ∀ ρ e it ds v, SG Q gd ρ → xExp gr gd e = true → xIter gr gd it = true →
      xDoms gr gd ds = true → AllIn Q v →
      ER eraseScope (SG Q gd) (Sem.matchIterE (n + 1) env ρ e it ds v)
        (Sem.matchIterE (n + 1) env (eraseScope ρ) e it ds (swapX v)) := by
  intro ρ e it ds v hρ hx hit hds hv
  have hsrc := xDoms_src hds
  cases it with
  | opt =>
    simp only [Sem.matchIterE, asOpt?_eraseC]
    cases ht : v.asOpt? with
    | none => exact ER.error _
    | some o =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      cases o with
      | none =>
        have := ih.matchExps ρ (ds.map domSrc) (ds.map fun _ => Value.opt none) hρ hsrc
          (fun w hw => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw; trivial)
        simpa [List.map_map, Function.comp_def] using this
      | some w =>
        simp only [Option.map_some]
        refine ER.bind (ih.matchExp ρ e w hρ hx (Erase.allIn_asOpt hv ht w rfl)) fun ρ' _ hρ' => ?_
        rw [findVals?_eraseScope]
        cases hf : ρ'.findVals? (ds.map domVar) with
        | none => exact ER.error _
        | some ws =>
          simp only [Option.map_some, Res.ofOption_some]
          have := ih.matchExps ρ (ds.map domSrc) (ws.map fun u => Value.opt (some u)) hρ hsrc
            (fun u hu => by
              obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
              exact (hρ'.findVals? hf a ha : AllIn Q a))
          simpa [List.map_map, Function.comp_def] using this
  | list =>
    simp only [Sem.matchIterE, asList?_eraseC]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      exact ih.matchIterList ρ e ds none vs hρ hx hds (asList_allIn hv ht)
  | list1 =>
    simp only [Sem.matchIterE, asList?_eraseC]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      exact ER.assert (by simp) fun _ => ih.matchIterList ρ e ds none vs hρ hx hds (asList_allIn hv ht)
  | listN eₙ ido =>
    simp only [xIter] at hit
    simp only [Sem.matchIterE, asList?_eraseC]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind, List.length_map]
      refine ER.bind (ih.matchExp ρ eₙ (.num (.natN vs.length)) hρ hit trivial) fun ρ₀ _ hρ₀ => ?_
      exact ih.matchIterList ρ₀ e ds ido vs hρ₀ hx hds (asList_allIn hv ht)

theorem step_matchIterList (ih : EraseAt Q gr gd env n) :
    ∀ ρ e ds ido vs, SG Q gd ρ → xExp gr gd e = true → xDoms gr gd ds = true →
      (∀ v ∈ vs, AllIn Q v) →
      ER eraseScope (SG Q gd) (Sem.matchIterList (n + 1) env ρ e ds ido vs)
        (Sem.matchIterList (n + 1) env (eraseScope ρ) e ds ido (vs.map swapX)) := by
  intro ρ e ds ido vs hρ hx hds hvs
  simp only [Sem.matchIterList]
  refine ER.bind (ih.matchRounds ρ e (ds.map domVar) ido 0 vs hρ hx hvs) fun rows _ hrows => ?_
  rw [iterCols_erase]
  exact ih.matchExps ρ (ds.map domSrc) _ hρ (xDoms_src hds) (allIn_iterCols hrows _)

theorem step_matchRounds (ih : EraseAt Q gr gd env n) :
    ∀ ρ e xs ido i vs, SG Q gd ρ → xExp gr gd e = true → (∀ v ∈ vs, AllIn Q v) →
      ER (List.map (List.map swapX)) (fun rows => ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u)
        (Sem.matchRounds (n + 1) env ρ e xs ido i vs)
        (Sem.matchRounds (n + 1) env (eraseScope ρ) e xs ido i (vs.map swapX)) := by
  intro ρ e xs ido i vs hρ hx hvs
  cases vs with
  | nil => simp only [List.map_nil, Sem.matchRounds]; exact ER.ok (by simp)
  | cons v vs =>
    simp only [List.map_cons]
    have key : ∀ ρ₁, SG Q gd ρ₁ →
        ER (List.map (List.map swapX)) (fun rows => ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u)
          (do
            let ρ' ← Sem.matchExp n env ρ₁ e v
            let row ← Res.ofOption (ρ'.findVals? xs)
            let rest ← Sem.matchRounds n env ρ e xs ido (i + 1) vs
            .ok (row :: rest))
          (do
            let ρ' ← Sem.matchExp n env (eraseScope ρ₁) e (swapX v)
            let row ← Res.ofOption (ρ'.findVals? xs)
            let rest ← Sem.matchRounds n env (eraseScope ρ) e xs ido (i + 1) (vs.map swapX)
            .ok (row :: rest)) := by
      intro ρ₁ h₁
      refine ER.bind (ih.matchExp _ e v h₁ hx (hvs v (List.mem_cons_self ..))) fun ρ' _ hρ' => ?_
      rw [findVals?_eraseScope]
      cases hf : ρ'.findVals? xs with
      | none => exact ER.error _
      | some row =>
        simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
        refine ER.bind (ih.matchRounds ρ e xs ido (i + 1) vs hρ hx
          fun w hw => hvs w (List.mem_cons_of_mem _ hw)) fun rest _ hrest => ?_
        refine ⟨rfl, fun rows hr => ?_⟩
        simp only [Except.ok.injEq] at hr
        subst hr
        intro r hr u hu
        rcases List.mem_cons.1 hr with rfl | hr
        · exact hρ'.findVals? hf u hu
        · exact hrest r hr u hu
    cases ido with
    | none => simp only [Sem.matchRounds]; exact key ρ hρ
    | some y =>
      simp only [Sem.matchRounds]
      have := key _ (hρ.bindVal (x := y) (v := .num (.natN i)) trivial)
      rw [eraseScope_bindVal] at this
      exact this

theorem step_matchArg (ih : EraseAt Q gr gd env n) :
    ∀ ρ a w, SG Q gd ρ → xArg gr gd a = true → ArgIn Q gd w →
      ER eraseScope (SG Q gd) (Sem.matchArg (n + 1) env ρ a w)
        (Sem.matchArg (n + 1) env (eraseScope ρ) a (eraseA w)) := by
  intro ρ a w hρ hx hw
  cases a with
  | expA e =>
    simp only [xArg] at hx
    cases w with
    | val v =>
      simp only [eraseA, Sem.matchArg, argSubOk_erase]
      split
      · exact ih.matchExp ρ e v hρ hx hw
      · exact ER.error _
    | _ => simp only [eraseA, Sem.matchArg]; exact ER.error _
  | typA t' =>
    cases w with
    | typ t =>
      simp only [eraseA, Sem.matchArg, matchTypV_erase]
      exact ⟨rfl, fun ρ' h => matchTypV_sg hρ h⟩
    | _ => simp only [eraseA, Sem.matchArg]; exact ER.error _
  | defA y =>
    cases w with
    | defName x =>
      simp only [eraseA, Sem.matchArg]
      rw [← eraseScope_bindDef]
      exact ER.ok (hρ.bindDef hw)
    | _ => simp only [eraseA, Sem.matchArg]; exact ER.error _
  | gramA g' =>
    cases w with
    | gram g =>
      simp only [eraseA, Sem.matchArg, matchSymV_erase]
      exact ⟨rfl, fun ρ' h => matchSymV_sg hρ h⟩
    | _ => simp only [eraseA, Sem.matchArg]; exact ER.error _

theorem step_matchArgs (ih : EraseAt Q gr gd env n) :
    ∀ ρ l ws, SG Q gd ρ → xArgs gr gd l = true → (∀ w ∈ ws, ArgIn Q gd w) →
      ER eraseScope (SG Q gd) (Sem.matchArgs (n + 1) env ρ l ws)
        (Sem.matchArgs (n + 1) env (eraseScope ρ) l (ws.map eraseA)) := by
  intro ρ l ws hρ hx hws
  cases l with
  | nil =>
    cases ws with
    | nil => simp only [List.map_nil, Sem.matchArgs]; exact ER.ok hρ
    | cons _ _ => simp only [List.map_cons, Sem.matchArgs]; exact ER.error _
  | cons a l =>
    cases ws with
    | nil => simp only [List.map_nil, Sem.matchArgs]; exact ER.error _
    | cons w ws =>
      simp only [xArgs, Bool.and_eq_true] at hx
      simp only [List.map_cons, Sem.matchArgs]
      refine ER.bind (ih.matchArg ρ a w hρ hx.1 (hws w (List.mem_cons_self ..))) fun ρ' _ hρ' => ?_
      exact ih.matchArgs ρ' l ws hρ' hx.2 fun u hu => hws u (List.mem_cons_of_mem _ hu)

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
