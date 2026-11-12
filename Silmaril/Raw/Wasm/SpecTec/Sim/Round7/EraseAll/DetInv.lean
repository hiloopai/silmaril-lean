module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms

/-!
# Round 7, the export swap: inverting the evaluator on swap-set values (unrefined)

`ai_inv`, the `AllIn Q` copy of `Round7.Determ.ef_inv`: if `e` evaluates to a value in the swap
set, every variable of `Round7.Determ.invVars e` is bound to a value in the swap set. `AllIn Q` is
hereditary through tuples, lists, cases, options and concatenations, which is all the proof uses.
Kept unrefined like its original.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (invVars invVarsL invIter mapM_ok_forall mem_invVarsL
  findVal_bindVals_single evalDoms_single invVars_iterE)

variable {Q : Value → Prop}

/-! ## Parts of swap-set values -/

theorem ai_tuple {vs : List Value} : AllIn Q (.tuple vs) ↔ ∀ w ∈ vs, AllIn Q w := allIns_iff Q vs

theorem ai_list {vs : List Value} : AllIn Q (.list vs) ↔ ∀ w ∈ vs, AllIn Q w := allIns_iff Q vs

theorem ai_case {op : MixopS} {w : Value} : AllIn Q (.case op w) ↔ AllIn Q w := Iff.rfl

theorem ai_optSome {w : Value} : AllIn Q (.opt (some w)) ↔ AllIn Q w := Iff.rfl

theorem ai_optNone : AllIn Q (.opt none) := trivial

theorem ai_of_cat {v₁ v₂ v : Value} (h : Value.cat? v₁ v₂ = some v) (hv : AllIn Q v) :
    AllIn Q v₁ ∧ AllIn Q v₂ := by
  unfold Value.cat? at h
  split at h <;> cases h
  · exact ⟨ai_list.2 fun u hu => ai_list.1 hv u (List.mem_append_left _ hu),
      ai_list.2 fun u hu => ai_list.1 hv u (List.mem_append_right _ hu)⟩
  · exact ⟨ai_optNone, hv⟩
  · exact ⟨hv, ai_optNone⟩

/-- **The inversion at fuel `n`.** -/
def AIInvAt (Q : Value → Prop) (env : Env) (n : Nat) : Prop :=
  ∀ ρ e v, evalExp n env ρ e = .ok v → AllIn Q v →
    ∀ x ∈ invVars e, ∀ w, ρ.findVal? x = some w → AllIn Q w

theorem ai_iterList_inv {env : Env} {m : Nat} (ih : ∀ m' < m, AIInvAt Q env m') {ρ : VarEnv}
    {e : Exp} {y : IL.Id} {u v : Value} {k : Nat} (hy : y ≠ "_") (hye : y ∈ invVars e)
    (h : evalIterList m env ρ e [(y, u)] none k = .ok v) (hv : AllIn Q v) : AllIn Q u := by
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
  refine ai_list.2 fun w hw => ?_
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
  exact ih m (by omega) _ _ _ hev (ai_list.1 hv v' hv') y hye _ (findVal_bindVals_single hy _)

theorem aiInvAt_succ {env : Env} (n : Nat) (ih : ∀ m < n + 1, AIInvAt Q env m) : AIInvAt Q env (n + 1) := by
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
      exact ih m (by omega) _ _ _ heu (ai_tuple.1 hv u hu) x hxe w hw
  | listE es =>
      simp only [evalExp, Res.map_eq_ok] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      obtain ⟨e, he, hxe⟩ := mem_invVarsL hx
      rcases n with _ | m
      · simp [evalExps] at hvs
      simp only [evalExps] at hvs
      obtain ⟨u, hu, heu⟩ := mapM_ok_forall hvs e he
      exact ih m (by omega) _ _ _ heu (ai_list.1 hv u hu) x hxe w hw
  | caseE op e =>
      simp only [invVars] at hx
      simp only [evalExp, Res.map_eq_ok] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact ih n (by omega) _ _ _ hu (ai_case.1 hv) x hx w hw
  | optE eo =>
      cases eo with
      | none => simp [invVars] at hx
      | some e =>
        simp only [invVars] at hx
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨u, hu, rfl⟩ := h
        exact ih n (by omega) _ _ _ hu (ai_optSome.1 hv) x hx w hw
  | catE e₁ e₂ =>
      simp only [invVars, List.mem_append] at hx
      simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨v₁, h₁, v₂, h₂, h⟩ := h
      obtain ⟨ef₁, ef₂⟩ := ai_of_cat h hv
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
        | none => exact ai_optNone
        | some w₀ =>
          simp only [List.all_cons, List.all_nil, Option.isNone_some, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, Option.isSome_some, List.filterMap_cons,
            Option.map_some, List.filterMap_nil, Res.bind_eq_ok] at h
          obtain ⟨u', hu', h⟩ := h
          cases h
          exact ai_optSome.2 (ih m (by omega) _ _ _ hu' (ai_optSome.1 hv) y hye _
            (findVal_bindVals_single hy _))
      | list =>
        simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, h⟩ := h
        obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
        rw [hw] at hu; cases hu
        exact ai_iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
      | list1 =>
        simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, _, h⟩ := h
        obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
        rw [hw] at hu; cases hu
        exact ai_iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
      | listN eₙ ido =>
        cases ido with
        | some _ => simp [invIter] at hit
        | none =>
          simp only [evalIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, hxvs, _, _, k, _, h⟩ := h
          obtain ⟨u, rfl, hu⟩ := evalDoms_single hxvs
          rw [hw] at hu; cases hu
          exact ai_iterList_inv (fun m' hm' => ih m' (by omega)) hy hye h hv
  | _ => simp [invVars] at hx

/-- **Inverting the evaluator on swap-set values.** -/
theorem ai_inv (Q : Value → Prop) (env : Env) : ∀ n, AIInvAt Q env n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · intro ρ e v h; simp [evalExp] at h
    · exact aiInvAt_succ n ih

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
