module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.StepExp

/-!
# Round 7, the whole-evaluator erasure: lists, arguments, iteration and paths, one step (unrefined)

`evalExps`, `evalExpFields`, `evalArg`, `evalArgs`, `evalDoms`, `evalIterE`, `evalIterList`,
`evalRounds`, `pathGet`, `pathSet` and `patLen` at fuel `n + 1`, from `EraseAt … n`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env} {n : Nat}

theorem step_exps (ih : EraseAt Q gr gd env n) : ∀ ρ es, SG Q gd ρ → xExps gr gd es = true →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalExps (n + 1) env ρ es) (evalExps (n + 1) env (eraseScope ρ) es) := by
  intro ρ es hρ hx
  simp only [evalExps]
  exact ER.mapM' es fun e he => ih.exp ρ e hρ (xExps_mem hx e he)

theorem step_expFields (ih : EraseAt Q gr gd env n) : ∀ ρ fs, SG Q gd ρ →
    xFields gr gd fs = true →
    ER (List.map eraseP) (fun gs => ∀ p ∈ gs, AllIn Q p.2 ∧ p.1 ≠ "EXPORTS")
      (evalExpFields (n + 1) env ρ fs) (evalExpFields (n + 1) env (eraseScope ρ) fs) := by
  intro ρ fs hρ hx
  simp only [evalExpFields]
  refine ER.mapM' fs fun f hf => ?_
  obtain ⟨a, e⟩ := f
  obtain ⟨ha, he⟩ := xFields_mem hx a e hf
  exact ER.map (fun v => (a, v)) (fun _ _ => rfl) (fun v hv => ⟨hv, ha⟩) (ih.exp ρ e hρ he)

theorem resolveTyp_eraseScope (ρ : VarEnv) (t : Typ) :
    resolveTyp (eraseScope ρ) t = resolveTyp ρ t := by
  unfold resolveTyp; split <;> rfl

theorem resolveSym_eraseScope (ρ : VarEnv) (g : Sym) :
    resolveSym (eraseScope ρ) g = resolveSym ρ g := by
  unfold resolveSym; split <;> rfl

theorem step_arg (ih : EraseAt Q gr gd env n) : ∀ ρ a, SG Q gd ρ → xArg gr gd a = true →
    ER eraseA (ArgIn Q gd) (evalArg (n + 1) env ρ a) (evalArg (n + 1) env (eraseScope ρ) a) := by
  intro ρ a hρ hx
  cases a with
  | expA e =>
    simp only [xArg] at hx
    simp only [evalArg]
    exact ER.map ArgV.val (fun _ _ => rfl) (fun _ h => h) (ih.exp ρ e hρ hx)
  | typA t =>
    simp only [evalArg, resolveTyp_eraseScope]
    exact ER.ok (a := ArgV.typ _) trivial
  | defA x =>
    simp only [xArg] at hx
    simp only [evalArg, eraseScope_findDef]
    exact ER.ok (a := ArgV.defName _) (hρ.defName hx)
  | gramA g =>
    simp only [evalArg, resolveSym_eraseScope]
    exact ER.ok (a := ArgV.gram _) trivial

theorem step_args (ih : EraseAt Q gr gd env n) : ∀ ρ l, SG Q gd ρ → xArgs gr gd l = true →
    ER (List.map eraseA) (fun ws => ∀ w ∈ ws, ArgIn Q gd w)
      (evalArgs (n + 1) env ρ l) (evalArgs (n + 1) env (eraseScope ρ) l) := by
  intro ρ l hρ hx
  simp only [evalArgs]
  exact ER.mapM' l fun a ha => ih.arg ρ a hρ (xArgs_mem hx a ha)

theorem step_doms (ih : EraseAt Q gr gd env n) : ∀ ρ ds, SG Q gd ρ → xDoms gr gd ds = true →
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn Q p.2)
      (evalDoms (n + 1) env ρ ds) (evalDoms (n + 1) env (eraseScope ρ) ds) := by
  intro ρ ds hρ hx
  simp only [evalDoms]
  refine ER.mapM' ds fun d hd => ?_
  exact ER.map (fun v => (domVar d, v)) (fun _ _ => rfl) (fun _ h => h)
    (ih.exp ρ _ hρ (xDoms_mem hx d hd))

theorem headLen_erase (xvs : List (IL.Id × Value)) :
    ((xvs.map eraseP).head?.bind fun p => p.2.asList?.map List.length) =
      (xvs.head?.bind fun p => p.2.asList?.map List.length) := by
  cases xvs with
  | nil => rfl
  | cons p _ =>
    simp only [List.map_cons, List.head?_cons, Option.bind_some, eraseP, asList?_eraseV]
    cases p.2.asList? <;> simp

theorem step_iterList (ih : EraseAt Q gr gd env n) : ∀ ρ e xvs ido k, SG Q gd ρ →
    xExp gr gd e = true → (∀ p ∈ xvs, AllIn Q p.2) →
    ER eraseV (AllIn Q) (evalIterList (n + 1) env ρ e xvs ido k)
      (evalIterList (n + 1) env (eraseScope ρ) e (xvs.map eraseP) ido k) := by
  intro ρ e xvs ido k hρ hx hxv
  simp only [evalIterList, mapM_asList_erase]
  cases hds : (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) with
  | none => exact ER.error _
  | some ds =>
    simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
    refine ER.assert (by simp [List.all_map, Function.comp_def]) fun _ => ?_
    rw [iterRows_erase]
    refine ER.bind (ih.rounds ρ e _ hρ hx (allIn_iterRows (allIn_asLists hxv hds) ido k))
      fun vs _ hvs => ?_
    have h := ER.ok (f := eraseV) (allIn_list_of hvs)
    rw [eraseV_list'] at h
    exact h

theorem step_iterE (ih : EraseAt Q gr gd env n) : ∀ ρ e it ds, SG Q gd ρ → xExp gr gd e = true →
    xIter gr gd it = true → xDoms gr gd ds = true →
    ER eraseV (AllIn Q) (evalIterE (n + 1) env ρ e it ds)
      (evalIterE (n + 1) env (eraseScope ρ) e it ds) := by
  intro ρ e it ds hρ hx hit hds
  cases it with
  | opt =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [mapM_asOpt_erase]
    cases hos : (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) with
    | none => exact ER.error _
    | some os =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      have hn : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
          fun p => p.2.isNone) = os.all fun p => p.2.isNone := by
        simp [List.all_map, Function.comp_def]
      have hs : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
          fun p => p.2.isSome) = os.all fun p => p.2.isSome := by
        simp [List.all_map, Function.comp_def]
      rw [hn, hs, filterMap_opt_erase]
      split
      · exact ER.ok (a := Value.opt none) trivial
      · split
        · rw [← eraseScope_bindVals]
          refine ER.bind (ih.exp _ e (hρ.bindVals (allIn_asOpts hxv hos)) hx) fun v _ hv => ?_
          exact ER.ok (a := Value.opt (some v)) hv
        · exact ER.error _
  | list =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList ρ e xvs none k hρ hx hxv
  | list1 =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ => ih.iterList ρ e xvs none k hρ hx hxv
  | listN eₙ ido =>
    simp only [xIter] at hit
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hρ hds) fun xvs _ hxv =>
      ER.bind (ih.exp ρ eₙ hρ hit) fun kv _ _ => ?_
    rw [asNat?_eraseV]
    cases kv.asNat? with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList ρ e xvs ido k hρ hx hxv

theorem step_rounds (ih : EraseAt Q gr gd env n) : ∀ ρ e rs, SG Q gd ρ → xExp gr gd e = true →
    (∀ r ∈ rs, ∀ p ∈ r, AllIn Q p.2) →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalRounds (n + 1) env ρ e rs)
      (evalRounds (n + 1) env (eraseScope ρ) e (rs.map (List.map eraseP))) := by
  intro ρ e rs hρ hx hrs
  simp only [evalRounds]
  refine ER.mapM rs fun r hr => ?_
  rw [← eraseScope_bindVals]
  exact ih.exp _ e (hρ.bindVals (hrs r hr)) hx

theorem step_pathGet (ih : EraseAt Q gr gd env n) : ∀ ρ v p, SG Q gd ρ → xPath gr gd p = true →
    AllIn Q v →
    ER eraseV (AllIn Q) (pathGet (n + 1) env ρ v p) (pathGet (n + 1) env (eraseScope ρ) (eraseV v) p) := by
  intro ρ v p hρ hx hv
  cases p with
  | rootP => simp only [pathGet]; exact ER.ok hv
  | idxP p e =>
    simp only [xPath, Bool.and_eq_true] at hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet ρ v p hρ hx.1 hv) fun u _ hu =>
      ER.bind (ih.exp ρ e hρ hx.2) fun iv _ _ => ?_
    rw [asNat?_eraseV]
    cases iv.asNat? with
    | none => exact ER.error _
    | some i =>
      show ER eraseV (AllIn Q) (Res.ofOption (u.idx? i)) (Res.ofOption ((eraseV u).idx? i))
      exact ER.ofOption (idx?_eraseV u i) fun w hw => hu.idx? hw
  | sliceP p e₁ e₂ =>
    simp only [xPath, Bool.and_eq_true] at hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet ρ v p hρ hx.1.1 hv) fun u _ hu =>
      ER.bind (ih.exp ρ e₁ hρ hx.1.2) fun x _ _ => ER.bind (ih.exp ρ e₂ hρ hx.2) fun y _ _ => ?_
    rw [asNat?_eraseV, asNat?_eraseV]
    cases x.asNat? with
    | none => exact ER.error _
    | some i =>
      cases y.asNat? with
      | none => exact ER.error _
      | some k =>
        show ER eraseV (AllIn Q) (Res.ofOption (u.slice? i k)) (Res.ofOption ((eraseV u).slice? i k))
        exact ER.ofOption (slice?_eraseV u i k) fun w hw => hu.slice? hw
  | dotP p a =>
    simp only [xPath, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet ρ v p hρ hx.2 hv) fun u _ hu => ?_
    exact ER.ofOption (field?_eraseV hx.1 u) fun w hw => hu.field? hw

theorem step_pathSet (ih : EraseAt Q gr gd env n) : ∀ ρ v p w, SG Q gd ρ →
    xPath gr gd p = true → AllIn Q v →
    pathSet (n + 1) env (eraseScope ρ) (eraseV v) p (eraseV w) =
      eraseV <$> pathSet (n + 1) env ρ v p w := by
  intro ρ v p w hρ hx hv
  cases p with
  | rootP => simp only [pathSet]; rfl
  | idxP p e =>
    simp only [xPath, Bool.and_eq_true] at hx
    simp only [pathSet]
    have hg := ih.pathGet ρ v p hρ hx.1 hv
    cases h₁ : pathGet n env ρ v p with
    | error e => rw [hg.eq_error h₁]; rfl
    | ok u =>
      rw [hg.eq_ok h₁]
      have he' := ih.exp ρ e hρ hx.2
      cases h₂ : evalExp n env ρ e with
      | error e => rw [he'.eq_error h₂]; rfl
      | ok iv =>
        rw [he'.eq_ok h₂]
        simp only [bind, Except.bind, asNat?_eraseV]
        cases iv.asNat? with
        | none => rfl
        | some i =>
          simp only [Res.ofOption, setIdx_eraseV]
          cases u.setIdx i w with
          | none => rfl
          | some u' => exact ih.pathSet ρ v p u' hρ hx.1 hv
  | sliceP p e₁ e₂ =>
    simp only [xPath, Bool.and_eq_true] at hx
    simp only [pathSet]
    have hg := ih.pathGet ρ v p hρ hx.1.1 hv
    cases hr : pathGet n env ρ v p with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      have e₁' := ih.exp ρ e₁ hρ hx.1.2
      have e₂' := ih.exp ρ e₂ hρ hx.2
      cases hx' : evalExp n env ρ e₁ with
      | error e => rw [e₁'.eq_error hx']; rfl
      | ok x =>
        rw [e₁'.eq_ok hx']
        cases hy : evalExp n env ρ e₂ with
        | error e => simp only [bind, Except.bind]; rw [e₂'.eq_error hy]; rfl
        | ok y =>
          simp only [bind, Except.bind]
          rw [e₂'.eq_ok hy]
          simp only [asNat?_eraseV]
          cases x.asNat? with
          | none => rfl
          | some i =>
            cases y.asNat? with
            | none => rfl
            | some k =>
              simp only [Res.ofOption, setSlice_eraseV]
              cases u.setSlice i k w with
              | none => rfl
              | some u' => exact ih.pathSet ρ v p u' hρ hx.1.1 hv
  | dotP p a =>
    simp only [xPath, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
    simp only [pathSet]
    have hg := ih.pathGet ρ v p hρ hx.2 hv
    cases hr : pathGet n env ρ v p with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      simp only [bind, Except.bind, Res.ofOption, setField_eraseV hx.1]
      cases u.setField a w with
      | none => rfl
      | some u' => exact ih.pathSet ρ v p u' hρ hx.2 hv

theorem step_patLen (ih : EraseAt Q gr gd env n) : ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
    patLen (n + 1) env (eraseScope ρ) e = patLen (n + 1) env ρ e := by
  intro ρ e hρ hx
  have hgen : ∀ e, xExp gr gd e = true →
      (do let v ← evalExp n env (eraseScope ρ) e; Res.ofOption v.len? : Res Nat) =
        (do let v ← evalExp n env ρ e; Res.ofOption v.len?) := by
    intro e he
    rw [(ih.exp ρ e hρ he).1]
    cases evalExp n env ρ e with
    | error _ => rfl
    | ok v => simp only [Functor.map, Except.map, bind, Except.bind, len?_eraseV]
  cases e
  case listE es => simp only [patLen]
  case catE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [patLen, ih.patLen ρ e₁ hρ hx.1, ih.patLen ρ e₂ hρ hx.2]
  case iterE e₀ it =>
    obtain ⟨i, ds⟩ := it
    cases i
    case listN eₙ x =>
      simp only [xExp, xIter, Bool.and_eq_true] at hx
      simp only [patLen]
      rw [(ih.exp ρ eₙ hρ hx.1.2).1]
      cases evalExp n env ρ eₙ with
      | error _ => rfl
      | ok v => simp only [Functor.map, Except.map, bind, Except.bind, asNat?_eraseV]
    all_goals simp only [patLen]; exact hgen _ hx
  all_goals simp only [patLen]; exact hgen _ hx

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
