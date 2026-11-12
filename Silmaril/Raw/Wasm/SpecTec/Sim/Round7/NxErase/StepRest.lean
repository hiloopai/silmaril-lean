module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxErase.StepExp

/-!
# Round 7, REH route 2: the erasure copy without `QInj`, the other members (unrefined)

`evalExps`, `evalExpFields`, `evalArg`, `evalArgs`, `evalDoms`, `evalIterE`, `evalIterList`,
`evalRounds`, `callDef`, `pathGet` and `pathSet` at fuel `n + 1`, from `NAt … n`, following
round 3's `EraseAll.step_*`. The rounds of an iteration conform to `NxSites.iterΓ`
(`NxFlow.rowScope_opt`, `NxFlow.rowScope_list`), from the conformance of the domains
(`NxFlow.expAt`). `nAt`: every fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)

variable {gr gd : String → Bool} {env : Env} {n : Nat}
variable {S : Sig} {T : TSig} {Γ : List (String × AT)} {tps : AuxCtx}

theorem step_exps (ih : NAt gr gd env n) (ρ : VarEnv) (es : List Exp) (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkL S T Γ es = true)
    (ha : auxL tps es = true) (hX : auxXL tps es = true) (hb : badEs S Γ es = 0)
    (hx : xExps gr gd es = true) :
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalExps (n + 1) env ρ es) (evalExps (n + 1) env (eraseScope ρ) es) := by
  simp only [evalExps]
  exact ER.mapM' es fun e he => ih.exp S T Γ tps ρ e hρ (hc.mono (Nat.le_succ n))
    (tyOkL_mem ht e he) (auxL_mem ha e he) (auxXL_mem hX e he) (badEs_mem hb e he)
    (xExps_mem hx e he)

theorem step_fields (ih : NAt gr gd env n) (ρ : VarEnv) (fs : List ExpField)
    (hρ : ScopeVT S Γ ρ) (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkF S T Γ fs = true)
    (ha : auxF tps fs = true) (hX : auxXF tps fs = true) (hb : badFs S Γ fs = 0)
    (hx : xFields gr gd fs = true) :
    ER (List.map eraseP) (fun gs => ∀ p ∈ gs, AllIn QT p.2 ∧ p.1 ≠ "EXPORTS")
      (evalExpFields (n + 1) env ρ fs) (evalExpFields (n + 1) env (eraseScope ρ) fs) := by
  simp only [evalExpFields]
  refine ER.mapM' fs fun f hf => ?_
  obtain ⟨a, e⟩ := f
  obtain ⟨hna, he⟩ := xFields_mem hx a e hf
  obtain ⟨h₁, h₂, h₃, h₄⟩ := fields_mem ht ha hX hb a e hf
  exact ER.map (fun v => (a, v)) (fun _ _ => rfl) (fun v hv => ⟨hv, hna⟩)
    (ih.exp S T Γ tps ρ e hρ (hc.mono (Nat.le_succ n)) h₁ h₂ h₃ h₄ he)

theorem step_arg (ih : NAt gr gd env n) (ρ : VarEnv) (x : Arg) (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkA S T Γ [x] = true)
    (ha : auxA tps [x] = true) (hX : auxXA tps [x] = true) (hb : badAs S Γ [x] = 0)
    (hx : xArg gr gd x = true) :
    ER eraseA (ArgIn QT gd) (evalArg (n + 1) env ρ x) (evalArg (n + 1) env (eraseScope ρ) x) := by
  cases x with
  | expA e =>
    simp only [tyOkA, auxA, auxXA, badAs, xArg, Bool.and_true, Nat.add_zero] at ht ha hX hb hx
    simp only [evalArg]
    exact ER.map ArgV.val (fun _ _ => rfl) (fun _ h => h)
      (ih.exp S T Γ tps ρ e hρ (hc.mono (Nat.le_succ n)) ht ha hX hb hx)
  | typA t =>
    simp only [evalArg, resolveTyp_eraseScope]
    exact ER.ok (a := ArgV.typ _) trivial
  | defA y =>
    simp only [xArg] at hx
    simp only [evalArg, eraseScope_findDef]
    exact ER.ok (a := ArgV.defName _) ((sg_of_defs hc.defs).defName hx)
  | gramA g =>
    simp only [evalArg, resolveSym_eraseScope]
    exact ER.ok (a := ArgV.gram _) trivial

theorem step_args (ih : NAt gr gd env n) (ρ : VarEnv) (xs : List Arg) (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkA S T Γ xs = true)
    (ha : auxA tps xs = true) (hX : auxXA tps xs = true) (hb : badAs S Γ xs = 0)
    (hx : xArgs gr gd xs = true) :
    ER (List.map eraseA) (fun ws => ∀ w ∈ ws, ArgIn QT gd w)
      (evalArgs (n + 1) env ρ xs) (evalArgs (n + 1) env (eraseScope ρ) xs) := by
  simp only [evalArgs]
  refine ER.mapM' xs fun x hx' => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := args_mem ht ha hX hb x hx'
  exact ih.arg S T Γ tps ρ x hρ (hc.mono (Nat.le_succ n)) h₁ h₂ h₃ h₄ (xArgs_mem hx x hx')

theorem step_doms (ih : NAt gr gd env n) (ρ : VarEnv) (ds : List Dom) (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkD S T Γ ds = true)
    (ha : auxD tps ds = true) (hX : auxXD tps ds = true) (hb : badDs S Γ ds = 0)
    (hx : xDoms gr gd ds = true) :
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn QT p.2)
      (evalDoms (n + 1) env ρ ds) (evalDoms (n + 1) env (eraseScope ρ) ds) := by
  simp only [evalDoms]
  refine ER.mapM' ds fun d hd => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := doms_mem ht ha hX hb d hd
  exact ER.map (fun v => (domVar d, v)) (fun _ _ => rfl) (fun _ h => h)
    (ih.exp S T Γ tps ρ _ hρ (hc.mono (Nat.le_succ n)) h₁ h₂ h₃ h₄ (xDoms_mem hx d hd))

theorem step_rounds (ih : NAt gr gd env n) (Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (rows : List (List (IL.Id × Value))) (hr : ∀ r ∈ rows, ScopeVT S Γi (ρ.bindVals r))
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOk S T Γi e = true) (ha : auxE tps e = true)
    (hX : auxX tps e = true) (hb : badE S Γi e = 0) (hx : xExp gr gd e = true) :
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalRounds (n + 1) env ρ e rows)
      (evalRounds (n + 1) env (eraseScope ρ) e (rows.map (List.map eraseP))) := by
  simp only [evalRounds]
  refine ER.mapM rows fun r hrm => ?_
  rw [← eraseScope_bindVals]
  exact ih.exp S T Γi tps (ρ.bindVals r) e (hr r hrm) ((hc.mono (Nat.le_succ n)).bindVals r)
    ht ha hX hb hx

theorem step_iterList (ih : NAt gr gd env n) (Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (k : Nat)
    (hr : ∀ ds, xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds →
      (∀ p ∈ ds, p.2.length = k) → ∀ i < k, ScopeVT S Γi (ρ.bindVals (iterRow ds ido i)))
    (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOk S T Γi e = true) (ha : auxE tps e = true)
    (hX : auxX tps e = true) (hb : badE S Γi e = 0) (hx : xExp gr gd e = true) :
    ER eraseV (AllIn QT) (evalIterList (n + 1) env ρ e xvs ido k)
      (evalIterList (n + 1) env (eraseScope ρ) e (xvs.map eraseP) ido k) := by
  simp only [evalIterList, mapM_asList_erase]
  cases hds : (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) with
  | none => exact ER.error _
  | some ds =>
    simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
    refine ER.assert (by simp [List.all_map, Function.comp_def]) fun hall => ?_
    have hlen : ∀ p ∈ ds, p.2.length = k := fun p hp => by
      have := List.all_eq_true.1 hall p hp
      simpa using this
    rw [iterRows_erase]
    refine ER.bind (ih.rounds S T Γi tps ρ e _ (fun r hr' => ?_) (hc.mono (Nat.le_succ n))
      ht ha hX hb hx) fun vs _ _ => ?_
    · simp only [iterRows, List.mem_map, List.mem_range] at hr'
      obtain ⟨i, hi, rfl⟩ := hr'
      exact hr ds hds hlen i hi
    · have h := ER.ok (f := eraseV) (allIn_top (.list vs))
      rw [eraseV_list'] at h
      exact h

set_option maxHeartbeats 1000000 in
theorem step_iter (ih : NAt gr gd env n) (ρ : VarEnv) (e : Exp) (it : Iter) (ds : List Dom)
    (hρ : ScopeVT S Γ ρ) (hc : NCalls gd S T tps env ρ (n + 1))
    (ht : tyOk S T (iterΓ S Γ it ds) e = true) (hti : tyOkI S T Γ it = true)
    (htd : tyOkD S T Γ ds = true) (hnd : nodupB (ds.map domVar) = true)
    (ha : auxE tps e = true) (hai : auxI tps it = true) (had : auxD tps ds = true)
    (hX : auxX tps e = true) (hXi : auxXI tps it = true) (hXd : auxXD tps ds = true)
    (hb : badE S (iterΓ S Γ it ds) e = 0) (hbi : badI S Γ it = 0) (hbd : badDs S Γ ds = 0)
    (hx : xExp gr gd e = true) (hxi : xIter gr gd it = true) (hxd : xDoms gr gd ds = true) :
    ER eraseV (AllIn QT) (evalIterE (n + 1) env ρ e it ds)
      (evalIterE (n + 1) env (eraseScope ρ) e it ds) := by
  have hc' := hc.mono (Nat.le_succ n)
  have hD := ih.doms S T Γ tps ρ ds hρ hc' htd had hXd hbd hxd
  have hE := fun xvs (h : evalDoms n env ρ ds = .ok xvs) =>
    (expAt env n).doms S T Γ tps ρ ds xvs hρ hc'.callH htd had h
  cases it with
  | opt =>
    simp only [evalIterE]
    refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
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
        · rename_i hsome
          rw [← eraseScope_bindVals]
          refine ER.bind (ih.exp S T _ tps _ e (rowScope_opt hρ hnd (hE xvs hxvs) hos hsome)
            (hc'.bindVals _) ht ha hX hb hx) fun v _ _ => ?_
          exact ER.ok (a := Value.opt (some v)) (allIn_top v)
        · exact ER.error _
  | list =>
    simp only [evalIterE]
    refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList S T _ tps ρ e xvs none k
        (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs) (by simp [counterΓ]) hl hlen hi)
        hc' ht ha hX hb hx
  | list1 =>
    simp only [evalIterE]
    refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ => ih.iterList S T _ tps ρ e xvs none k
        (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs) (by simp [counterΓ]) hl hlen hi)
        hc' ht ha hX hb hx
  | listN eₙ ido =>
    simp only [tyOkI] at hti
    simp only [auxI] at hai
    simp only [auxXI] at hXi
    simp only [badI] at hbi
    simp only [xIter] at hxi
    simp only [evalIterE]
    refine ER.bind hD fun xvs hxvs _ =>
      ER.bind (ih.exp S T Γ tps ρ eₙ hρ hc' hti hai hXi hbi hxi) fun kv _ _ => ?_
    rw [asNat?_eraseV]
    cases kv.asNat? with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList S T _ tps ρ e xvs ido k
        (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs)
          (by cases ido <;> simp [counterΓ]) hl hlen hi)
        hc' ht ha hX hb hx

theorem step_call (H : BIErase QT gd env) (ih : NAt gr gd env n) (ρ : VarEnv) (f : String)
    (xs : List Arg) (hρ : ScopeVT S Γ ρ) (hc : NCalls gd S T tps env ρ (n + 1))
    (ht : tyOk S T Γ (.callE f xs) = true) (ha : auxE tps (.callE f xs) = true)
    (hX : auxX tps (.callE f xs) = true) (hb : badE S Γ (.callE f xs) = 0)
    (hx : xExp gr gd (.callE f xs) = true) :
    ER eraseV (AllIn QT) (callDef (n + 1) env ρ f xs) (callDef (n + 1) env (eraseScope ρ) f xs) := by
  have hc' := hc.mono (Nat.le_succ n)
  simp only [tyOk, Bool.and_eq_true] at ht
  simp only [auxE, Bool.and_eq_true] at ha
  simp only [auxX] at hX
  simp only [badE] at hb
  simp only [xExp, Bool.and_eq_true] at hx
  simp only [callDef, eraseScope_findDef]
  refine ER.bind (ih.args S T Γ tps ρ xs hρ hc' ht.1 ha.2 hX hb hx.2) fun ws hws hwsA => ?_
  have hg := (sg_of_defs hc.defs).defName hx.1
  cases hd : env.findDef? ((ρ.findDef? f).getD f) with
  | none => exact ER.error _
  | some d =>
    simp only [Res.ofOption_some, bind, Except.bind]
    have hR : ∀ ps, callPar S T f xs = some ps → ArgsR S T ρ xs ws ps := by
      intro ps hp
      have h2 := ht.2
      rw [hp] at h2
      exact (expAt env n).args S T Γ tps ρ xs ws hρ hc'.callH ht.1 ha.2 hws ps h2
    refine ER.elimUndef (hc.callE n (Nat.lt_succ_self n) f xs ws d hR ha.1 hg hd hwsA)
      (fun v _ hv => ER.ok hv) fun _ => ?_
    obtain ⟨hbi, hbA⟩ := H _ ws hg hwsA
    exact ER.ofOption hbi hbA

theorem step_pathGet (ih : NAt gr gd env n) (ρ : VarEnv) (v : Value) (p : Path)
    (hρ : ScopeVT S Γ ρ) (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkP S T Γ p = true)
    (hX : auxXP tps p = true) (hb : badP S Γ p = 0) (hx : xPath gr gd p = true) :
    ER eraseV (AllIn QT) (pathGet (n + 1) env ρ v p) (pathGet (n + 1) env (eraseScope ρ) (eraseV v) p) := by
  have hc' := hc.mono (Nat.le_succ n)
  cases p with
  | rootP => simp only [pathGet]; exact ER.ok (allIn_top v)
  | idxP p e =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht hX hb hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet S T Γ tps ρ v p hρ hc' ht.1 hX.1.1 hb.1 hx.1) fun u _ _ =>
      ER.bind (ih.exp S T Γ tps ρ e hρ hc' ht.2 hX.1.2 hX.2 hb.2 hx.2) fun iv _ _ => ?_
    rw [asNat?_eraseV]
    cases iv.asNat? with
    | none => exact ER.error _
    | some i =>
      show ER eraseV (AllIn QT) (Res.ofOption (u.idx? i)) (Res.ofOption ((eraseV u).idx? i))
      exact ER.ofOption (idx?_eraseV u i) fun w _ => allIn_top w
  | sliceP p e₁ e₂ =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht hX hb hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet S T Γ tps ρ v p hρ hc' ht.1.1 hX.1.1.1.1 hb.1.1 hx.1.1)
      fun u _ _ => ER.bind (ih.exp S T Γ tps ρ e₁ hρ hc' ht.1.2 hX.1.1.1.2 hX.1.1.2 hb.1.2 hx.1.2)
        fun x _ _ => ER.bind (ih.exp S T Γ tps ρ e₂ hρ hc' ht.2 hX.1.2 hX.2 hb.2 hx.2)
          fun y _ _ => ?_
    rw [asNat?_eraseV, asNat?_eraseV]
    cases x.asNat? with
    | none => exact ER.error _
    | some i =>
      cases y.asNat? with
      | none => exact ER.error _
      | some k =>
        show ER eraseV (AllIn QT) (Res.ofOption (u.slice? i k))
          (Res.ofOption ((eraseV u).slice? i k))
        exact ER.ofOption (slice?_eraseV u i k) fun w _ => allIn_top w
  | dotP p a =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht hX hb hx
    simp only [pathGet]
    refine ER.bind (ih.pathGet S T Γ tps ρ v p hρ hc' ht hX hb hx.2) fun u _ _ => ?_
    exact ER.ofOption (field?_eraseV hx.1 u) fun w _ => allIn_top w

theorem step_pathSet (ih : NAt gr gd env n) (ρ : VarEnv) (v : Value) (p : Path) (w : Value)
    (hρ : ScopeVT S Γ ρ) (hc : NCalls gd S T tps env ρ (n + 1)) (ht : tyOkP S T Γ p = true)
    (hX : auxXP tps p = true) (hb : badP S Γ p = 0) (hx : xPath gr gd p = true) :
    pathSet (n + 1) env (eraseScope ρ) (eraseV v) p (eraseV w) =
      eraseV <$> pathSet (n + 1) env ρ v p w := by
  have hc' := hc.mono (Nat.le_succ n)
  cases p with
  | rootP => simp only [pathSet]; rfl
  | idxP p e =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht hX hb hx
    simp only [pathSet]
    have hg := ih.pathGet S T Γ tps ρ v p hρ hc' ht.1 hX.1.1 hb.1 hx.1
    cases h₁ : pathGet n env ρ v p with
    | error e => rw [hg.eq_error h₁]; rfl
    | ok u =>
      rw [hg.eq_ok h₁]
      have he' := ih.exp S T Γ tps ρ e hρ hc' ht.2 hX.1.2 hX.2 hb.2 hx.2
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
          | some u' => exact ih.pathSet S T Γ tps ρ v p u' hρ hc' ht.1 hX.1.1 hb.1 hx.1
  | sliceP p e₁ e₂ =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht hX hb hx
    simp only [pathSet]
    have hg := ih.pathGet S T Γ tps ρ v p hρ hc' ht.1.1 hX.1.1.1.1 hb.1.1 hx.1.1
    cases hr : pathGet n env ρ v p with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      have e₁' := ih.exp S T Γ tps ρ e₁ hρ hc' ht.1.2 hX.1.1.1.2 hX.1.1.2 hb.1.2 hx.1.2
      have e₂' := ih.exp S T Γ tps ρ e₂ hρ hc' ht.2 hX.1.2 hX.2 hb.2 hx.2
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
              | some u' => exact ih.pathSet S T Γ tps ρ v p u' hρ hc' ht.1.1 hX.1.1.1.1 hb.1.1 hx.1.1
  | dotP p a =>
    simp only [tyOkP, auxXP, badP, xPath, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht hX hb hx
    simp only [pathSet]
    have hg := ih.pathGet S T Γ tps ρ v p hρ hc' ht hX hb hx.2
    cases hr : pathGet n env ρ v p with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      simp only [bind, Except.bind, Res.ofOption, setField_eraseV hx.1]
      cases u.setField a w with
      | none => rfl
      | some u' => exact ih.pathSet S T Γ tps ρ v p u' hρ hc' ht hX hb hx.2

/-! ## Every fuel -/

theorem nAt_zero : NAt gr gd env 0 where
  exp := by intros; simp only [evalExp]; exact ER.error _
  exps := by intros; simp only [evalExps]; exact ER.error _
  fields := by intros; simp only [evalExpFields]; exact ER.error _
  arg := by intros; simp only [evalArg]; exact ER.error _
  args := by intros; simp only [evalArgs]; exact ER.error _
  doms := by intros; simp only [evalDoms]; exact ER.error _
  iter := by intros; simp only [evalIterE]; exact ER.error _
  iterList := by intros; simp only [evalIterList]; exact ER.error _
  rounds := by intros; simp only [evalRounds]; exact ER.error _
  call := by intros; simp only [callDef]; exact ER.error _
  pathGet := by intros; simp only [pathGet]; exact ER.error _
  pathSet := by intros; simp only [pathSet]; rfl

theorem nAt_succ (H : BIErase QT gd env) (ih : NAt gr gd env n) : NAt gr gd env (n + 1) where
  exp := step_exp ih
  exps := fun _ _ _ _ ρ es hρ hc ht ha hX hb hx => step_exps ih ρ es hρ hc ht ha hX hb hx
  fields := fun _ _ _ _ ρ fs hρ hc ht ha hX hb hx => step_fields ih ρ fs hρ hc ht ha hX hb hx
  arg := fun _ _ _ _ ρ x hρ hc ht ha hX hb hx => step_arg ih ρ x hρ hc ht ha hX hb hx
  args := fun _ _ _ _ ρ xs hρ hc ht ha hX hb hx => step_args ih ρ xs hρ hc ht ha hX hb hx
  doms := fun _ _ _ _ ρ ds hρ hc ht ha hX hb hx => step_doms ih ρ ds hρ hc ht ha hX hb hx
  iter := fun _ _ _ _ ρ e it ds hρ hc ht hti htd hnd ha hai had hX hXi hXd hb hbi hbd hx hxi hxd =>
    step_iter ih ρ e it ds hρ hc ht hti htd hnd ha hai had hX hXi hXd hb hbi hbd hx hxi hxd
  iterList := fun _ _ Γi _ ρ e xvs ido k hr hc ht ha hX hb hx =>
    step_iterList ih Γi ρ e xvs ido k hr hc ht ha hX hb hx
  rounds := fun _ _ Γi _ ρ e rows hr hc ht ha hX hb hx =>
    step_rounds ih Γi ρ e rows hr hc ht ha hX hb hx
  call := fun _ _ _ _ ρ f xs hρ hc ht ha hX hb hx => step_call H ih ρ f xs hρ hc ht ha hX hb hx
  pathGet := fun _ _ _ _ ρ v p hρ hc ht hX hb hx => step_pathGet ih ρ v p hρ hc ht hX hb hx
  pathSet := fun _ _ _ _ ρ v p w hρ hc ht hX hb hx => step_pathSet ih ρ v p w hρ hc ht hX hb hx

/-- **The expression members commute with erasure at every fuel**, without a swap set. -/
theorem nAt (H : BIErase QT gd env) : ∀ k, NAt gr gd env k
  | 0 => nAt_zero
  | k + 1 => nAt_succ H (nAt H k)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
