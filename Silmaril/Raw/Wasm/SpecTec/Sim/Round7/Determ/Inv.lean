module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Basic

/-!
# Round 7, determination: inverting the evaluator on `ExpFree` values (unrefined)

`ef_inv`: if `e` evaluates to an `ExpFree` value, every variable of `invVars e` is bound to an
`ExpFree` value. `invVars` follows only the constructors whose value contains the values of their
parts (tuples, lists, cases, options, concatenations, subsumptions) and single-domain iterations
`e*` over a variable, whose rounds evaluate `e` once per element of that variable's value. One case
per constructor, by strong induction on the fuel, kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

theorem mapM_ok_forall {α β : Type} {f : α → Res β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
  | [], ys, _ => by simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨y₀, h₀, ys', h', hys⟩ := h
    cases hys
    intro x' hx'
    rcases List.mem_cons.1 hx' with rfl | hx'
    · exact ⟨y₀, List.mem_cons_self, h₀⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_ok_forall h' x' hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem mem_invVarsL : ∀ {es : List Exp} {x : IL.Id}, x ∈ invVarsL es → ∃ e ∈ es, x ∈ invVars e
  | [], _, h => by simp [invVarsL] at h
  | e :: es, x, h => by
    simp only [invVarsL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hx⟩ := mem_invVarsL h
      exact ⟨e', List.mem_cons_of_mem _ he', hx⟩

theorem findVal_bindVals_single {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") (w : Value) :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, hx]

theorem ef_of_cat {v₁ v₂ v : Value} (h : Value.cat? v₁ v₂ = some v) (hv : ExpFree v) :
    ExpFree v₁ ∧ ExpFree v₂ := by
  unfold Value.cat? at h
  split at h <;> cases h
  · exact ⟨ef_list.2 fun u hu => ef_list.1 hv u (List.mem_append_left _ hu),
      ef_list.2 fun u hu => ef_list.1 hv u (List.mem_append_right _ hu)⟩
  · exact ⟨ef_optNone, hv⟩
  · exact ⟨hv, ef_optNone⟩

theorem evalDoms_single {env : Env} {m : Nat} {ρ : VarEnv} {y xs : IL.Id}
    {xvs : List (IL.Id × Value)} (h : evalDoms m env ρ [.mk y (.varE xs)] = .ok xvs) :
    ∃ u, xvs = [(y, u)] ∧ ρ.findVal? xs = some u := by
  rcases m with _ | m
  · simp [evalDoms] at h
  simp only [evalDoms, List.mapM_cons, List.mapM_nil, Res.bind_eq_ok, Res.map_eq_ok] at h
  obtain ⟨p, ⟨u, hu, rfl⟩, ps, hps, hxvs⟩ := h
  cases hps
  cases hxvs
  rcases m with _ | m
  · simp [evalExp] at hu
  simp only [domSrc, evalExp, Res.ofOption_eq_ok] at hu
  exact ⟨u, by simp [domVar], hu⟩

theorem invVars_iterE {e : Exp} {i : Iter} {ds : List Dom} {x : IL.Id}
    (hx : x ∈ invVars (.iterE e (.mk i ds))) :
    ∃ y xs, ds = [.mk y (.varE xs)] ∧ y ≠ "_" ∧ invIter i = true ∧ y ∈ invVars e ∧ x = xs := by
  rcases ds with _ | ⟨⟨y, s⟩, _ | ⟨d, ds⟩⟩
  · simp [invVars] at hx
  · cases s with
    | varE xs =>
      simp only [invVars, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hx
      split at hx
      · rename_i hc
        simp only [List.mem_singleton] at hx
        exact ⟨y, xs, rfl, hc.1.1, hc.1.2, hc.2, hx⟩
      · simp at hx
    | _ => simp [invVars] at hx
  · simp [invVars] at hx

/-- **The inversion at fuel `n`.** -/
def InvAt (env : Env) (n : Nat) : Prop :=
  ∀ ρ e v, evalExp n env ρ e = .ok v → ExpFree v →
    ∀ x ∈ invVars e, ∀ w, ρ.findVal? x = some w → ExpFree w

theorem iterList_inv {env : Env} {m : Nat} (ih : ∀ m' < m, InvAt env m') {ρ : VarEnv}
    {e : Exp} {y : IL.Id} {u v : Value} {k : Nat} (hy : y ≠ "_") (hye : y ∈ invVars e)
    (h : evalIterList m env ρ e [(y, u)] none k = .ok v) (hv : ExpFree v) : ExpFree u := by
  rcases m with _ | m
  · simp [evalIterList] at h
  simp only [evalIterList, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok,
    List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Option.map_eq_some_iff] at h
  obtain ⟨ds, ⟨_, ⟨l, hl, rfl⟩, _, rfl, rfl⟩, hk, vs, hvs, hveq⟩ := h
  cases hveq
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at hk
  have hu : u = .list l := by cases u <;> simp_all [Value.asList?]
  subst hu
  refine ef_list.2 fun w hw => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  rcases m with _ | m
  · simp [evalRounds] at hvs
  simp only [evalRounds] at hvs
  have hrow : iterRow [(y, l)] none i ∈ iterRows [(y, l)] none k := by
    simp only [iterRows, List.mem_map, List.mem_range]
    exact ⟨i, by simpa [hk] using hi, rfl⟩
  have hrow' : iterRow [(y, l)] none i = [(y, l[i])] := by
    simp [iterRow, List.getElem?_eq_getElem hi]
  obtain ⟨v', hv', hev⟩ := mapM_ok_forall hvs _ hrow
  rw [hrow'] at hev
  exact ih m (by omega) _ _ _ hev (ef_list.1 hv v' hv') y hye _ (findVal_bindVals_single hy _)

theorem invAt_succ {env : Env} (n : Nat) (ih : ∀ m < n + 1, InvAt env m) : InvAt env (n + 1) := by
  intro ρ e v h hv x hx w hw
  cases e with
  | varE y =>
      simp only [invVars, List.mem_singleton] at hx
      subst hx
      simp only [evalExp, Res.ofOption_eq_ok] at h
      rw [hw] at h; cases h; exact hv
  | tupE es =>
      simp only [evalExp, Res.map_eq_ok] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      obtain ⟨e, he, hxe⟩ := mem_invVarsL hx
      rcases n with _ | m
      · simp [evalExps] at hvs
      simp only [evalExps] at hvs
      obtain ⟨u, hu, heu⟩ := mapM_ok_forall hvs e he
      exact ih m (by omega) _ _ _ heu (ef_tuple.1 hv u hu) x hxe w hw
  | listE es =>
      simp only [evalExp, Res.map_eq_ok] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      obtain ⟨e, he, hxe⟩ := mem_invVarsL hx
      rcases n with _ | m
      · simp [evalExps] at hvs
      simp only [evalExps] at hvs
      obtain ⟨u, hu, heu⟩ := mapM_ok_forall hvs e he
      exact ih m (by omega) _ _ _ heu (ef_list.1 hv u hu) x hxe w hw
  | caseE op e =>
      simp only [invVars] at hx
      simp only [evalExp, Res.map_eq_ok] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact ih n (by omega) _ _ _ hu (ef_case.1 hv) x hx w hw
  | optE eo =>
      cases eo with
      | none => simp [invVars] at hx
      | some e =>
        simp only [invVars] at hx
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨u, hu, rfl⟩ := h
        exact ih n (by omega) _ _ _ hu (ef_optSome.1 hv) x hx w hw
  | catE e₁ e₂ =>
      simp only [invVars, List.mem_append] at hx
      simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨v₁, h₁, v₂, h₂, h⟩ := h
      obtain ⟨ef₁, ef₂⟩ := ef_of_cat h hv
      rcases hx with hx | hx
      · exact ih n (by omega) _ _ _ h₁ ef₁ x hx w hw
      · exact ih n (by omega) _ _ _ h₂ ef₂ x hx w hw
  | subE e t₁ t₂ =>
      simp only [invVars] at hx
      simp only [evalExp] at h
      exact ih n (by omega) _ _ _ h hv x hx w hw
  | iterE e it =>
      obtain ⟨i, ds⟩ := it
      obtain ⟨y, xs, rfl, hy, hit, hye, rfl⟩ := invVars_iterE hx
      simp only [evalExp] at h
      rcases n with _ | m
      · simp [evalIterE] at h
      cases i with
      | opt =>
        simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, os, hos, h⟩ := h
        obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
        rw [hw] at hu; cases hu
        simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq, Option.map_eq_some_iff] at hos
        obtain ⟨_, ⟨o, ho, rfl⟩, _, rfl, rfl⟩ := hos
        have hwo : w = .opt o := by cases w <;> simp_all [Value.asOpt?]
        subst hwo
        cases o with
        | none => exact ef_optNone
        | some w₀ =>
          simp only [List.all_cons, List.all_nil, Option.isNone_some, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, Option.isSome_some, List.filterMap_cons,
            Option.map_some, List.filterMap_nil, Res.bind_eq_ok] at h
          obtain ⟨u', hu', h⟩ := h
          cases h
          exact ef_optSome.2 (ih m (by omega) _ _ _ hu' (ef_optSome.1 hv) y hye _
            (findVal_bindVals_single hy _))
      | list =>
        simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, h⟩ := h
        obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
        rw [hw] at hu; cases hu
        exact iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
      | list1 =>
        simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, _, h⟩ := h
        obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
        rw [hw] at hu; cases hu
        exact iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
      | listN eₙ ido =>
        cases ido with
        | some _ => simp [invIter] at hit
        | none =>
          simp only [evalIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, hxvs, _, _, k, _, h⟩ := h
          obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
          rw [hw] at hu; cases hu
          exact iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
  | _ => simp [invVars] at hx

/-- **Inverting the evaluator on `ExpFree` values.** -/
theorem ef_inv (env : Env) : ∀ n, InvAt env n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · intro ρ e v h; simp [evalExp] at h
    · exact invAt_succ n ih

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
