module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.StepMatch

/-!
# Round 7, REH route 2: the other matching members, one step, and `MatchAt` at every fuel
(unrefined)
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

theorem step_mexps (ih : MatchAt env n) : ∀ (ρ : VarEnv) (es : List Exp) (vs : List Value)
    (ρ' : VarEnv), ScopeVT S Γ ρ →
    (∀ (i : Nat) e v, es[i]? = some e → vs[i]? = some v →
      ∃ b, patTy S T Γ b e = true ∧ vtB S b v = true) →
    matchExps (n + 1) env ρ es vs = .ok ρ' → MatchOk S Γ ρ ρ'
  | ρ, [], [], ρ', hρ, _, hm => by
    simp only [matchExps, Except.ok.injEq] at hm; subst hm; exact MatchOk.refl hρ
  | ρ, e :: es, v :: vs, ρ', hρ, hp, hm => by
    simp only [matchExps, Res.bind_eq_ok] at hm
    obtain ⟨ρ₁, h₁, h₂⟩ := hm
    obtain ⟨b, hb, hvb⟩ := hp 0 e v rfl rfl
    have m₁ := ih.exp S T Γ ρ e b v ρ₁ hρ hb hvb h₁
    exact m₁.trans (ih.exps S T Γ ρ₁ es vs ρ' m₁.1
      (fun i e' v' he hv => hp (i + 1) e' v' (by simpa using he) (by simpa using hv)) h₂)
  | ρ, [], _ :: _, ρ', _, _, hm => by simp [matchExps] at hm
  | ρ, _ :: _, [], ρ', _, _, hm => by simp [matchExps] at hm

theorem step_mfields (ih : MatchAt env n) (a : AT) : ∀ (ρ : VarEnv) (fs : List ExpField)
    (gs : List (AtomS × Value)) (ρ' : VarEnv), ScopeVT S Γ ρ → patF S T Γ a fs = true →
    (∀ g ∈ gs, vtB S (fieldOf' S a g.1) g.2 = true) →
    matchExpFields (n + 1) env ρ fs gs = .ok ρ' → MatchOk S Γ ρ ρ'
  | ρ, [], [], ρ', hρ, _, _, hm => by
    simp only [matchExpFields, Except.ok.injEq] at hm; subst hm; exact MatchOk.refl hρ
  | ρ, .mk k e :: fs, g :: gs, ρ', hρ, hp, hg, hm => by
    simp only [patF, Bool.and_eq_true] at hp
    simp only [matchExpFields, Res.assert_eq_ok, Res.bind_eq_ok] at hm
    obtain ⟨hk, ρ₁, h₁, h₂⟩ := hm
    have hg0 := hg g (List.mem_cons_self ..)
    rw [← hk] at hg0
    have m₁ := ih.exp S T Γ ρ e _ g.2 ρ₁ hρ hp.1 hg0 h₁
    exact m₁.trans (ih.fields S T Γ ρ₁ a fs gs ρ' m₁.1 hp.2
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) h₂)
  | ρ, [], _ :: _, ρ', _, _, _, hm => by simp [matchExpFields] at hm
  | ρ, _ :: _, [], ρ', _, _, _, hm => by simp [matchExpFields] at hm

theorem step_mrounds (ih : MatchAt env n) (Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (xs : List IL.Id) (ido : Option IL.Id) (b : AT)
    (hs : ∀ j, ScopeVT S Γi (ctrScope ρ ido j)) (hp : patTy S T Γi b e = true) :
    ∀ (i : Nat) (vs : List Value) (rows : List (List Value)), (∀ w ∈ vs, vtB S b w = true) →
    matchRounds (n + 1) env ρ e xs ido i vs = .ok rows →
    ∀ row ∈ rows, ∀ (j : Nat) x w, xs[j]? = some x → row[j]? = some w →
      vtB S ((Γi.lookup x).getD .unk) w = true
  | i, [], rows, _, hm => by
    simp only [matchRounds, Except.ok.injEq] at hm; subst hm; intro row hr; simp at hr
  | i, v :: vs, rows, hv, hm => by
    rw [matchRounds.eq_def] at hm
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Except.ok.injEq] at hm
    obtain ⟨ρ', h₁, row, hrow, rest, hrest, rfl⟩ := hm
    have m₁ := ih.exp S T Γi (ctrScope ρ ido i) e b v ρ' (hs i) hp (hv v (List.mem_cons_self ..))
      (by cases ido <;> exact h₁)
    intro r hr j x w hx hw
    rcases List.mem_cons.1 hr with rfl | hr
    · exact vtB_getD m₁.1 (findVals?_get hrow j x w hx hw)
    · exact ih.rounds S T Γi ρ e xs ido (i + 1) b vs rest hs hp
        (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hrest r hr j x w hx hw

theorem mem_iterCol {rows : List (List Value)} {j : Nat} {w : Value}
    (h : w ∈ iterCol rows j) : ∃ row ∈ rows, row[j]? = some w := by
  simp only [iterCol, List.mem_filterMap] at h
  exact h

theorem step_miterList (ih : MatchAt env n) (Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (ds : List Dom) (ido : Option IL.Id) (b : AT) (vs : List Value) (ρ' : VarEnv)
    (hρ : ScopeVT S Γ ρ) (hs : ∀ i, ScopeVT S Γi (ctrScope ρ ido i))
    (hp : patTy S T Γi b e = true) (hv : ∀ w ∈ vs, vtB S b w = true)
    (hd : patD S T Γ Γi ds = true)
    (hm : matchIterList (n + 1) env ρ e ds ido vs = .ok ρ') : MatchOk S Γ ρ ρ' := by
  simp only [matchIterList, Res.bind_eq_ok] at hm
  obtain ⟨rows, hrows, hm⟩ := hm
  have hr := ih.rounds S T Γi ρ e (ds.map domVar) ido 0 b vs rows hs hp hv hrows
  refine ih.exps S T Γ ρ _ _ ρ' hρ (fun i e' v' he hv' => ?_) hm
  rw [List.getElem?_map] at he
  cases hdi : ds[i]? with
  | none => rw [hdi] at he; cases he
  | some d =>
    rw [hdi] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    have hi : i < ds.length := (List.getElem?_eq_some_iff.1 hdi).1
    simp only [iterCols, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at hv'
    subst hv'
    refine ⟨_, patD_get hd d (List.mem_of_getElem? hdi), vtB_iter_list fun w hw => ?_⟩
    obtain ⟨row, hrow, hw'⟩ := mem_iterCol hw
    exact hr row hrow i (domVar d) w (by simp [List.getElem?_map, hdi]) hw'

theorem ctrScope_none (ρ : VarEnv) (i : Nat) : ctrScope ρ none i = ρ := rfl

theorem scope_ctr {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {eₙ : Exp} {ido : Option IL.Id}
    {ds : List Dom} (hf : freshDoms Γ (.listN eₙ ido) ds = true) (i : Nat) :
    ScopeVT S (iterΓ S Γ (.listN eₙ ido) ds) (ctrScope ρ ido i) := by
  have h0 := scope_iter hρ hf
  cases ido with
  | none => exact h0
  | some y =>
    refine h0.bindVal ?_ fun a _ => vtB_of_nxB' (nxB_num _)
    have : (((domsΓ S Γ ds ++ [(y, AT.base)]) ++ Γ).lookup y).isSome = true := by
      rw [lookup_append, lookup_append]
      cases (domsΓ S Γ ds).lookup y <;> simp [List.lookup]
    simpa [iterΓ, counterΓ, List.append_assoc] using this

set_option maxHeartbeats 400000 in
theorem step_miter (ih : MatchAt env n) (ρ : VarEnv) (e : Exp) (it : Iter) (ds : List Dom)
    (a : AT) (v : Value) (ρ' : VarEnv) (hρ : ScopeVT S Γ ρ)
    (hp : patTy S T Γ a (.iterE e (.mk it ds)) = true) (hv : vtB S a v = true)
    (hm : matchIterE (n + 1) env ρ e it ds v = .ok ρ') : MatchOk S Γ ρ ρ' := by
  simp only [patTy, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨hpi, hf⟩, hpe⟩, hpd⟩ := hp
  have hsi := scope_iter hρ hf
  cases it with
  | opt =>
    simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asOpt?_eq_some] at hm
    obtain ⟨o, rfl, hm⟩ := hm
    cases o with
    | none =>
      refine ih.exps S T Γ ρ _ _ ρ' hρ (fun i e' v' he hv' => ?_) hm
      rw [List.getElem?_map] at he hv'
      cases hdi : ds[i]? with
      | none => rw [hdi] at he; cases he
      | some d =>
        rw [hdi] at he hv'
        simp only [Option.map_some, Option.some.injEq] at he hv'
        subst he hv'
        exact ⟨_, patD_get hpd d (List.mem_of_getElem? hdi), vtB_optNone _⟩
    | some w =>
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hm
      obtain ⟨ρ₁, h₁, ws, hws, hm⟩ := hm
      have m₁ := ih.exp S T _ ρ e _ w ρ₁ hsi hpe (vtB_elemOpt hv) h₁
      refine ih.exps S T Γ ρ _ _ ρ' hρ (fun i e' v' he hv' => ?_) hm
      rw [List.getElem?_map] at he hv'
      cases hdi : ds[i]? with
      | none => rw [hdi] at he; cases he
      | some d =>
        rw [hdi] at he
        simp only [Option.map_some, Option.some.injEq] at he
        subst he
        cases hwi : ws[i]? with
        | none => rw [hwi] at hv'; cases hv'
        | some u =>
          rw [hwi] at hv'
          simp only [Option.map_some, Option.some.injEq] at hv'
          subst hv'
          refine ⟨_, patD_get hpd d (List.mem_of_getElem? hdi), vtB_iter_some ?_⟩
          exact vtB_getD m₁.1 (findVals?_get hws i (domVar d) u
            (by simp [List.getElem?_map, hdi]) hwi)
  | list =>
    simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some] at hm
    obtain ⟨vs, rfl, hm⟩ := hm
    exact ih.iterList S T Γ _ ρ e ds none _ vs ρ' hρ (fun i => hsi) hpe
      (fun w hw => vtB_elem hv w hw) hpd hm
  | list1 =>
    simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some,
      Res.assert_eq_ok] at hm
    obtain ⟨vs, rfl, _, hm⟩ := hm
    exact ih.iterList S T Γ _ ρ e ds none _ vs ρ' hρ (fun i => hsi) hpe
      (fun w hw => vtB_elem hv w hw) hpd hm
  | listN eₙ ido =>
    simp only [NxTyped.patI] at hpi
    simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some] at hm
    obtain ⟨vs, rfl, ρ₀, h₀, hm⟩ := hm
    have m₀ := ih.exp S T Γ ρ eₙ .base _ ρ₀ hρ hpi (base_of_nxB (nxB_num _)) h₀
    exact m₀.trans (ih.iterList S T Γ _ ρ₀ e ds ido _ vs ρ' m₀.1 (scope_ctr m₀.1 hf) hpe
      (fun w hw => vtB_elem hv w hw) hpd hm)

theorem matchAt_zero (env : Env) : MatchAt env 0 where
  exp := by intros; simp_all [matchExp]
  exps := by intros; simp_all [matchExps]
  fields := by intros; simp_all [matchExpFields]
  iter := by intros; simp_all [matchIterE]
  iterList := by intros; simp_all [matchIterList]
  rounds := by intros; simp_all [matchRounds]

theorem matchAt_succ (ih : MatchAt env n) : MatchAt env (n + 1) where
  exp := fun _ _ _ ρ e a v ρ' hρ hp hv hm => step_mexp ih ρ e a v ρ' hρ hp hv hm
  exps := fun _ _ _ ρ es vs ρ' hρ hp hm => step_mexps ih ρ es vs ρ' hρ hp hm
  fields := fun _ _ _ ρ a fs gs ρ' hρ hp hg hm => step_mfields ih a ρ fs gs ρ' hρ hp hg hm
  iter := fun _ _ _ ρ e it ds a v ρ' hρ hp hv hm => step_miter ih ρ e it ds a v ρ' hρ hp hv hm
  iterList := fun _ _ _ Γi ρ e ds ido b vs ρ' hρ hs hp hv hd hm =>
    step_miterList ih Γi ρ e ds ido b vs ρ' hρ hs hp hv hd hm
  rounds := fun _ _ Γi ρ e xs ido i b vs rows hs hp hv hm =>
    step_mrounds ih Γi ρ e xs ido b hs hp i vs rows hv hm

/-- **Matching keeps scopes conforming at every fuel.** -/
theorem matchAt (env : Env) : ∀ k, MatchAt env k
  | 0 => matchAt_zero env
  | k + 1 => matchAt_succ (matchAt env k)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
