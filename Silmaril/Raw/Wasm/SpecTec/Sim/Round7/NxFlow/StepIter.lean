module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.StepRest

/-!
# Round 7, REH route 2: iterations, paths and calls, one step (unrefined)

The scope of a round of an iteration conforms to `iterΓ` (`rowScope`, with the `Opt` and list
forms `rowScope_opt`, `rowScope_list`), so `evalIterE`, `evalIterList` and `evalRounds` give
conforming elements. `pathGet` and `pathSet` follow `NxTyped.pathAT`. `callDef` returns what
`CallH` promises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {n : Nat} {S : Sig} {T : TSig} {Γ : List (String × AT)}

/-! ## The scope of a round -/

theorem counterΓ_cases (it : Iter) : counterΓ it = [] ∨ ∃ y, counterΓ it = [(y, .base)] := by
  unfold counterΓ
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- **The scope of one round of an iteration.** -/
theorem rowScope {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {ds : List Dom}
    (hnd : nodupB (ds.map domVar) = true) {it : Iter} {row : List (IL.Id × Value)}
    (hval : ∀ p ∈ row, (∃ d ∈ ds, domVar d = p.1 ∧
        vtB S (elemAT S (tyOf S Γ (domSrc d))) p.2 = true) ∨
      (nxB p.2 = true ∧ counterΓ it = [(p.1, .base)]))
    (hkey : ∀ d ∈ ds, ∃ w, (domVar d, w) ∈ row)
    (hcnt : ∀ y, counterΓ it = [(y, .base)] → ∃ w, (y, w) ∈ row) :
    ScopeVT S (iterΓ S Γ it ds) (ρ.bindVals row) := by
  have he : iterΓ S Γ it ds = (domsΓ S Γ ds ++ counterΓ it) ++ Γ := by
    simp [iterΓ, List.append_assoc]
  rw [he]
  refine ScopeVT.rows hρ (fun p hp a ha => ?_) (fun p hp => ?_) (fun x hx => ?_)
  · rcases hval p hp with ⟨d, hd, hx, hv⟩ | ⟨hn, _⟩
    · rw [← hx, lookup_append_of_some (domsΓ_lookup_mem hnd d hd)] at ha
      cases ha; exact hv
    · exact vtB_of_nxB' hn
  · rcases hval p hp with ⟨d, hd, hx, _⟩ | ⟨_, hc⟩
    · rw [← hx, lookup_append_of_some (domsΓ_lookup_mem hnd d hd)]; rfl
    · refine lookup_append_isSome ?_
      rw [hc]; simp [List.lookup]
  · rw [lookup_append] at hx
    split at hx
    · rename_i a ha
      obtain ⟨d, hd, rfl⟩ := domsΓ_lookup_some ha
      exact hkey d hd
    · rcases counterΓ_cases it with hc | ⟨y, hc⟩
      · rw [hc] at hx; simp [List.lookup] at hx
      · rw [hc] at hx
        simp only [List.lookup] at hx
        split at hx
        · rename_i hy
          have : x = y := beq_iff_eq.1 hy
          subst this
          exact hcnt x hc
        · simp at hx

/-- The scope of the round of an `Opt` iteration. -/
theorem rowScope_opt {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {ds : List Dom}
    (hnd : nodupB (ds.map domVar) = true) {xvs : List (IL.Id × Value)}
    (hd : List.Forall₂ (fun d p => p.1 = domVar d ∧ EOk S T Γ (domSrc d) p.2) ds xvs)
    {os : List (IL.Id × Option Value)}
    (ho : xvs.mapM (fun p => p.2.asOpt?.map fun o => (p.1, o)) = some os)
    (hs : (os.all fun p => p.2.isSome) = true) :
    ScopeVT S (iterΓ S Γ .opt ds)
      (ρ.bindVals (os.filterMap fun p => p.2.map fun w => (p.1, w))) := by
  have h2 := forall₂_trans hd (mapM_option_forall₂ ho)
  refine rowScope hρ hnd (fun p hp => ?_) (fun d hd' => ?_) (fun y hy => ?_)
  · obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
    obtain ⟨d, hdm, r, ⟨hr1, hr2⟩, hr⟩ := forall₂_mem_right h2 q hq
    simp only [Option.map_eq_some_iff, Value.asOpt?_eq_some] at hr
    obtain ⟨o, ho', rfl⟩ := hr
    simp only [Option.map_eq_some_iff] at hqp
    obtain ⟨w, rfl, rfl⟩ := hqp
    rw [ho'] at hr2
    exact .inl ⟨d, hdm, hr1.symm, vtB_elemAT_of_elemOf (vtB_elemOpt hr2.ty)⟩
  · obtain ⟨q, hq, r, ⟨hr1, _⟩, hr⟩ := forall₂_mem_left h2 d hd'
    simp only [Option.map_eq_some_iff] at hr
    obtain ⟨o, _, rfl⟩ := hr
    have hsome : o.isSome = true := (List.all_eq_true.1 hs) _ hq
    obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨w, List.mem_filterMap.2 ⟨_, hq, ?_⟩⟩
    simp [hr1]
  · simp [counterΓ] at hy

/-- The scope of round `i` of a list iteration. -/
theorem rowScope_list {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {ds : List Dom}
    (hnd : nodupB (ds.map domVar) = true) {xvs : List (IL.Id × Value)}
    (hd : List.Forall₂ (fun d p => p.1 = domVar d ∧ EOk S T Γ (domSrc d) p.2) ds xvs)
    {it : Iter} {ido : Option IL.Id}
    (hit : counterΓ it = (ido.map fun y => (y, AT.base)).toList)
    {ds' : List (IL.Id × List Value)}
    (hl : xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds')
    {k : Nat} (hlen : ∀ p ∈ ds', p.2.length = k) {i : Nat} (hi : i < k) :
    ScopeVT S (iterΓ S Γ it ds) (ρ.bindVals (iterRow ds' ido i)) := by
  have h2 := forall₂_trans hd (mapM_option_forall₂ hl)
  refine rowScope hρ hnd (fun p hp => ?_) (fun d hd' => ?_) (fun y hy => ?_)
  · unfold iterRow at hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
      obtain ⟨d, hdm, r, ⟨hr1, hr2⟩, hr⟩ := forall₂_mem_right h2 q hq
      simp only [Option.map_eq_some_iff, Value.asList?_eq_some] at hr
      obtain ⟨l, hl', rfl⟩ := hr
      simp only [Option.map_eq_some_iff] at hqp
      obtain ⟨w, hw, rfl⟩ := hqp
      rw [hl'] at hr2
      exact .inl ⟨d, hdm, hr1.symm,
        vtB_elemAT_of_elemOf (vtB_elem hr2.ty w (List.mem_of_getElem? hw))⟩
    · cases ido with
      | none => simp at hp
      | some y =>
        simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        exact .inr ⟨nxB_num _, by simpa using hit⟩
  · obtain ⟨q, hq, r, ⟨hr1, _⟩, hr⟩ := forall₂_mem_left h2 d hd'
    simp only [Option.map_eq_some_iff] at hr
    obtain ⟨l, _, rfl⟩ := hr
    have hk : i < l.length := by rw [hlen _ hq]; exact hi
    refine ⟨l[i], List.mem_append_left _ (List.mem_filterMap.2 ⟨_, hq, ?_⟩)⟩
    simp [hr1, List.getElem?_eq_getElem hk]
  · rw [hit] at hy
    cases ido with
    | none => simp at hy
    | some y' =>
      simp only [Option.map_some, Option.toList_some, List.cons.injEq, Prod.mk.injEq,
        and_true] at hy
      subst hy
      exact ⟨Value.num (.natN i), List.mem_append_right _ (by simp)⟩

/-! ## Iterations -/

theorem step_rounds (ih : ExpAt env n) (tps : AuxCtx) (Γi : List (String × AT))
    (ρ : VarEnv) (e : Exp) (hc : CallH S T tps env ρ (n + 1)) (ht : tyOk S T Γi e = true)
    (ha : auxE tps e = true) : ∀ (rows : List (List (IL.Id × Value))) (vs : List Value),
    (∀ r ∈ rows, ScopeVT S Γi (ρ.bindVals r)) → evalRounds (n + 1) env ρ e rows = .ok vs →
    ∀ w ∈ vs, EOk S T Γi e w := by
  intro rows vs hr hv w hw
  simp only [evalRounds] at hv
  obtain ⟨r, hrm, hrv⟩ := forall₂_mem_right (mapM_forall₂ hv) w hw
  exact ih.exp S T Γi tps (ρ.bindVals r) e w (hr r hrm)
    ((hc.mono (Nat.le_succ n)).bindVals r) ht ha hrv

theorem step_iterList (ih : ExpAt env n) (tps : AuxCtx) (Γi : List (String × AT))
    (ρ : VarEnv) (e : Exp) (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (k : Nat)
    (v : Value)
    (hr : ∀ ds, xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds →
      (∀ p ∈ ds, p.2.length = k) → ∀ i < k, ScopeVT S Γi (ρ.bindVals (iterRow ds ido i)))
    (hc : CallH S T tps env ρ (n + 1)) (ht : tyOk S T Γi e = true) (ha : auxE tps e = true)
    (hv : evalIterList (n + 1) env ρ e xvs ido k = .ok v) : IterV (EOk S T Γi e) v := by
  simp only [evalIterList, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at hv
  obtain ⟨ds, hds, hall, vs, hvs, hv⟩ := hv
  cases hv
  have hlen : ∀ p ∈ ds, p.2.length = k := fun p hp => by
    have := List.all_eq_true.1 hall p hp
    simpa using this
  refine ih.rounds S T Γi tps ρ e (iterRows ds ido k) vs (fun r hr' => ?_)
    (hc.mono (Nat.le_succ n)) ht ha hvs
  simp only [iterRows, List.mem_map, List.mem_range] at hr'
  obtain ⟨i, hi, rfl⟩ := hr'
  exact hr ds hds hlen i hi

set_option maxHeartbeats 400000 in
theorem step_iter (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (e : Exp) (it : Iter)
    (ds : List Dom) (v : Value) (hρ : ScopeVT S Γ ρ) (hc : CallH S T tps env ρ (n + 1))
    (ht : tyOk S T (iterΓ S Γ it ds) e = true) (hti : tyOkI S T Γ it = true)
    (htd : tyOkD S T Γ ds = true) (hnd : nodupB (ds.map domVar) = true)
    (ha : auxE tps e = true) (hai : auxI tps it = true) (had : auxD tps ds = true)
    (hv : evalIterE (n + 1) env ρ e it ds = .ok v) : IterV (EOk S T (iterΓ S Γ it ds) e) v := by
  have hc' := hc.mono (Nat.le_succ n)
  cases it with
  | opt =>
    simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨xvs, hxvs, _, os, hos, hv⟩ := hv
    have hd := ih.doms S T Γ tps ρ ds xvs hρ hc' htd had hxvs
    split at hv
    · cases hv; trivial
    · split at hv
      · rename_i hs
        simp only [Res.bind_eq_ok] at hv
        obtain ⟨w, hw, hv⟩ := hv
        cases hv
        exact ih.exp S T _ tps _ e w (rowScope_opt hρ hnd hd hos hs) (hc'.bindVals _) ht ha hw
      · cases hv
  | list =>
    simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨xvs, hxvs, _, k, _, hv⟩ := hv
    have hd := ih.doms S T Γ tps ρ ds xvs hρ hc' htd had hxvs
    exact ih.iterList S T _ tps ρ e xvs none k v
      (fun ds' hl hlen i hi => rowScope_list hρ hnd hd (by simp [counterΓ]) hl hlen hi)
      hc' ht ha hv
  | list1 =>
    simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨xvs, hxvs, _, k, _, _, hv⟩ := hv
    have hd := ih.doms S T Γ tps ρ ds xvs hρ hc' htd had hxvs
    exact ih.iterList S T _ tps ρ e xvs none k v
      (fun ds' hl hlen i hi => rowScope_list hρ hnd hd (by simp [counterΓ]) hl hlen hi)
      hc' ht ha hv
  | listN eₙ ido =>
    simp only [evalIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨xvs, hxvs, kv, _, k, _, hv⟩ := hv
    have hd := ih.doms S T Γ tps ρ ds xvs hρ hc' htd had hxvs
    exact ih.iterList S T _ tps ρ e xvs ido k v
      (fun ds' hl hlen i hi => rowScope_list hρ hnd hd
        (by cases ido <;> simp [counterΓ]) hl hlen hi)
      hc' ht ha hv

/-! ## Paths -/

theorem vtB_fieldOf' {a : AT} {v w : Value} {k : AtomS} (h : vtB S a v = true)
    (hf : v.field? k = some w) : vtB S (fieldOf' S a k) w = true := by
  cases hn : nxAT S.good a
  · rw [fieldOf'_eq hn]; exact vtB_field? h hf
  · simp only [fieldOf', hn, ite_true]
    exact base_of_nxB (nxB_field? (nxB_of_vtB hn h) hf)

theorem step_pathGet (ih : ExpAt env n) (ρ : VarEnv) (a : AT) (v : Value) :
    ∀ (p : Path) (u : Value), vtB S a v = true → pathGet (n + 1) env ρ v p = .ok u →
      vtB S (pathAT S a p) u = true
  | .rootP, u, h, hv => by
    simp only [pathGet, Except.ok.injEq] at hv; subst hv; exact h
  | .idxP p e, u, h, hv => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', _, _, i, _, hi⟩ := hv
    exact vtB_idx? (ih.pathGet S ρ a v p u' h hu') hi
  | .sliceP p e₁ e₂, u, h, hv => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', _, _, _, _, i, _, k, _, hs⟩ := hv
    exact vtB_slice? (ih.pathGet S ρ a v p u' h hu') hs
  | .dotP p k, u, h, hv => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', hf⟩ := hv
    exact vtB_fieldOf' (ih.pathGet S ρ a v p u' h hu') hf

theorem step_pathSet (ih : ExpAt env n) (ρ : VarEnv) (a : AT) (v : Value) :
    ∀ (p : Path) (w u : Value), vtB S a v = true → vtB S (pathAT S a p) w = true →
      pathSet (n + 1) env ρ v p w = .ok u → vtB S a u = true
  | .rootP, w, u, _, hw, hv => by
    simp only [pathSet, Except.ok.injEq] at hv; subst hv; exact hw
  | .idxP p e, w, u, h, hw, hv => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', _, _, i, _, u'', hu'', hset⟩ := hv
    exact ih.pathSet S ρ a v p u'' u h (vtB_setIdx (ih.pathGet S ρ a v p u' h hu') hw hu'') hset
  | .sliceP p e₁ e₂, w, u, h, hw, hv => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', _, _, _, _, i, _, k, _, u'', hu'', hset⟩ := hv
    exact ih.pathSet S ρ a v p u'' u h (vtB_setSlice (ih.pathGet S ρ a v p u' h hu') hw hu'')
      hset
  | .dotP p k, w, u, h, hw, hv => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨u', hu', u'', hu'', hset⟩ := hv
    exact ih.pathSet S ρ a v p u'' u h (vtB_setField (ih.pathGet S ρ a v p u' h hu') hw hu'')
      hset

/-! ## Calls -/

theorem elimUndef_ok {α : Type} {r : Res α} {g : Unit → Res α} {v : α}
    (h : Res.elimUndef r (fun a => (.ok a : Res α)) g = .ok v) :
    r = .ok v ∨ (r = .error .undef ∧ g () = .ok v) := by
  cases r with
  | ok a => exact .inl h
  | error e =>
    cases e with
    | undef => exact .inr ⟨rfl, h⟩
    | outOfFuel => cases h

theorem step_call (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (f : String)
    (xs : List Arg) (v : Value) (hρ : ScopeVT S Γ ρ) (hc : CallH S T tps env ρ (n + 1))
    (ht : tyOk S T Γ (.callE f xs) = true) (ha : auxE tps (.callE f xs) = true)
    (hv : callDef (n + 1) env ρ f xs = .ok v) : EOk S T Γ (.callE f xs) v := by
  simp only [tyOk, Bool.and_eq_true] at ht
  simp only [auxE, Bool.and_eq_true] at ha
  simp only [callDef, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
  obtain ⟨ws, hws, d, hd, hr⟩ := hv
  have hr' : CallRes env n d ((ρ.findDef? f).getD f) ws v := by
    rcases elimUndef_ok hr with h | ⟨h₁, h₂⟩
    · exact .inl h
    · exact .inr ⟨h₁, by simpa using h₂⟩
  have key : vtB S (callRes S T f xs) v = true ∧
      vtB S ((S.results.lookup f).getD .unk) v = true := by
    obtain ⟨ht₁, ht₂⟩ := ht
    revert ht₂
    cases hp : callPar S T f xs with
    | some ps =>
      intro ht₂
      have hargs := ih.args S T Γ tps ρ xs ws hρ (hc.mono (Nat.le_succ n)) ht₁ ha.2 hws ps ht₂
      exact hc n (Nat.lt_succ_self n) f xs ws ps d v hp hargs ha.1 hd hr'
    | none =>
      intro ht₂
      simp only [Bool.and_eq_true] at ht₂
      have hg : T.gres.lookup f = none := by simpa using ht₂.2
      have htr := vtB_of_triv ht₂.1 v
      refine ⟨?_, htr⟩
      simp only [callRes, hg]
      exact htr
  have hty : vtB S (tyOf S Γ (.callE f xs)) v = true := by rw [tyOf_callE]; exact key.2
  have hnx : nxD S Γ (.callE f xs) = true → nxB v = true := by
    intro h
    simp only [nxD, nxE] at h
    exact nxB_of_vtB h hty
  refine ⟨hty, hnx, fun a h => ?_⟩
  simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨_, h⟩
  · exact vtB_of_atLe S _ _ _ h v key.1
  · exact vtB_of_nxB' (hnx h)

/-! ## `ExpAt` at every fuel -/

theorem expAt_zero (env : Env) : ExpAt env 0 where
  exp := by intros; simp_all [evalExp]
  exps := by intros; simp_all [evalExps]
  fields := by intros; simp_all [evalExpFields]
  arg := by intros; simp_all [evalArg]
  args := by intros; simp_all [evalArgs]
  doms := by intros; simp_all [evalDoms]
  iter := by intros; simp_all [evalIterE]
  iterList := by intros; simp_all [evalIterList]
  rounds := by intros; simp_all [evalRounds]
  call := by intros; simp_all [callDef]
  pathGet := by intros; simp_all [pathGet]
  pathSet := by intros; simp_all [pathSet]

theorem expAt_succ (ih : ExpAt env n) : ExpAt env (n + 1) where
  exp := fun S T Γ tps ρ e v hρ hc ht ha hv => step_exp ih S T Γ tps ρ e v hρ hc ht ha hv
  exps := fun _ _ _ tps ρ es vs hρ hc ht ha hv => step_exps ih tps ρ hρ hc es vs ht ha hv
  fields := fun _ _ _ tps ρ fs gs hρ hc ht ha hv => step_fields ih tps ρ hρ hc fs gs ht ha hv
  arg := fun _ _ _ tps ρ x w hρ hc ht ha hv p hp => step_arg ih tps ρ hρ hc x w ht ha hv p hp
  args := fun _ _ _ tps ρ xs ws hρ hc ht ha hv => step_args ih tps ρ hρ hc xs ws ht ha hv
  doms := fun _ _ _ tps ρ ds xvs hρ hc ht ha hv => step_doms ih tps ρ hρ hc ds xvs ht ha hv
  iter := fun _ _ _ tps ρ e it ds v hρ hc ht hti htd hnd ha hai had hv =>
    step_iter ih tps ρ e it ds v hρ hc ht hti htd hnd ha hai had hv
  iterList := fun _ _ Γi tps ρ e xvs ido k v hr hc ht ha hv =>
    step_iterList ih tps Γi ρ e xvs ido k v hr hc ht ha hv
  rounds := fun _ _ Γi tps ρ e rows vs hr hc ht ha hv =>
    step_rounds ih tps Γi ρ e hc ht ha rows vs hr hv
  call := fun _ _ _ tps ρ f xs v hρ hc ht ha hv => step_call ih tps ρ f xs v hρ hc ht ha hv
  pathGet := fun _ ρ a v p u h hv => step_pathGet ih ρ a v p u h hv
  pathSet := fun _ ρ a v p w u h hw hv => step_pathSet ih ρ a v p w u h hw hv

/-- **The expression members conform at every fuel**, given that calls conform. -/
theorem expAt (env : Env) : ∀ k, ExpAt env k
  | 0 => expAt_zero env
  | k + 1 => expAt_succ (expAt env k)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
