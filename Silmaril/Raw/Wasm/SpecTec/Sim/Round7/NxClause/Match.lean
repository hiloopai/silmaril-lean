module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Simple

/-!
# Round 8, REH route 2: matching argument patterns commutes with erasure (unrefined)

`linAt`: at every fuel, `matchExp`, `matchExps`, `matchExpFields`, `matchIterE`,
`matchIterList` and `matchRounds` on a pattern that passes the pattern check (`linE`), run on the
erased value in the erased scope, give the erased scope of the original match, and keep the
invariant `Inv`. No type is read: a comparison happens only at a variable that is already bound,
and the check makes one side of it export-free (`NxSites.eraseV_eq_iff_of_nx`). `matchArgs_erase`:
the same for a clause's argument patterns.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT allIn_top)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow (ctrScope nxBf_mem)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (eraseV_eq_iff_of_nx)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope find?_eraseScope)

variable {gd : String → Bool}

/-! ## Values -/

theorem nxBs_mem' : ∀ {vs : List Value}, nxBs vs = true → ∀ w ∈ vs, nxB w = true
  | [], _, _, h => by simp at h
  | v :: vs, h, w, hw => by
    simp only [nxBs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.1
    · exact nxBs_mem' h.2 w hw

theorem nxBs_of_mem' : ∀ {vs : List Value}, (∀ w ∈ vs, nxB w = true) → nxBs vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true]
    exact ⟨h v (List.mem_cons_self ..), nxBs_of_mem' fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

theorem nx_asTuple {v : Value} {vs : List Value} (h : nxB v = true) (ht : v.asTuple? = some vs) :
    ∀ w ∈ vs, nxB w = true := by
  cases v <;> simp only [Value.asTuple?, Option.some.injEq, reduceCtorEq] at ht
  subst ht
  exact nxBs_mem' h

theorem nx_asList {v : Value} {vs : List Value} (h : nxB v = true) (ht : v.asList? = some vs) :
    ∀ w ∈ vs, nxB w = true := by
  cases v <;> simp only [Value.asList?, Option.some.injEq, reduceCtorEq] at ht
  subst ht
  exact nxBs_mem' h

theorem nx_asCase {v w : Value} {op : MixopS} (h : nxB v = true) (ht : v.asCase? = some (op, w)) :
    nxB w = true := by
  cases v <;> simp only [Value.asCase?, Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact h

theorem nx_asOpt {v w : Value} (h : nxB v = true) (ht : v.asOpt? = some (some w)) :
    nxB w = true := by
  cases v <;> simp only [Value.asOpt?, Option.some.injEq, reduceCtorEq] at ht
  subst ht
  exact h

theorem nx_struct {gs : List (AtomS × Value)} (h : nxB (.struct gs) = true) :
    ∀ g ∈ gs, nxB g.2 = true :=
  nxBf_mem h

/-! ## The invariant -/

theorem contains_of_filter {l : List String} {x y : String}
    (h : (l.filter (· != x)).contains y = true) : l.contains y = true := by
  simp only [List.contains_iff_mem, List.mem_filter] at h ⊢
  exact h.1

theorem not_contains_filter {l : List String} {x : String} :
    (l.filter (· != x)).contains x = false := by
  simp [List.mem_filter]

theorem inv_empty : Inv gd VarEnv.empty ([], []) where
  wild := rfl
  dom x w h := by simp [VarEnv.findVal?, VarEnv.empty, Map.empty] at h
  nx x w _ h := by simp [VarEnv.findVal?, VarEnv.empty, Map.empty] at h
  defs p hp := by simp [VarEnv.empty, Map.empty] at hp

theorem Inv.mono {ρ : VarEnv} {st st' : LSt} (h : Inv gd ρ st)
    (h₁ : ∀ x, st.1.contains x = true → st'.1.contains x = true)
    (h₂ : ∀ x, st'.2.contains x = true → st.2.contains x = true) : Inv gd ρ st' where
  wild := h.wild
  dom x w hx := h₁ x (h.dom x w hx)
  nx x w hx hw := h.nx x w (h₂ x hx) hw
  defs := h.defs

theorem findVal?_ctr (ρ : VarEnv) (y x : IL.Id) (i : Nat) :
    (ρ.bindVal y (.num (.natN i))).findVal? x =
      if y = "_" then ρ.findVal? x else if y = x then some (.num (.natN i)) else ρ.findVal? x :=
  NxFlow.findVal?_bindVal _ _ _ _

/-- The scope a round of a pattern iteration starts from keeps the invariant, with the counter. -/
theorem Inv.ctr {ρ : VarEnv} {s : LSt} (h : Inv gd ρ s) (ido : Option IL.Id) (i : Nat) :
    Inv gd (ctrScope ρ ido i) (match ido with
      | some y => (y :: s.1, y :: s.2)
      | none => s) := by
  cases ido with
  | none => exact h
  | some y =>
    simp only [ctrScope]
    refine ⟨?_, fun x w hx => ?_, fun x w hx hw => ?_, h.defs⟩
    · rw [findVal?_ctr]
      by_cases hy : y = "_" <;> simp [hy, h.wild]
    · rw [findVal?_ctr] at hx
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq]
      split at hx
      · exact .inr (h.dom x w hx)
      · split at hx
        · rename_i _ hyx; exact .inl hyx.symm
        · exact .inr (h.dom x w hx)
    · rw [findVal?_ctr] at hw
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hx
      split at hw
      · rcases hx with rfl | hx
        · rename_i hy; rw [hy] at hw; rw [h.wild] at hw; cases hw
        · exact h.nx x w hx hw
      · split at hw
        · cases hw; rfl
        · rcases hx with rfl | hx
          · rename_i h2; exact absurd rfl h2
          · exact h.nx x w hx hw

theorem eraseScope_ctr (ρ : VarEnv) (ido : Option IL.Id) (i : Nat) :
    eraseScope (ctrScope ρ ido i) = ctrScope (eraseScope ρ) ido i := by
  cases ido with
  | none => rfl
  | some y => simp only [ctrScope, eraseScope_bindVal, eraseV_num]

theorem linDs_eq (vnx : Bool) : ∀ (st : LSt) (ds : List Dom),
    linDs vnx st ds = linEs vnx st (ds.map domSrc)
  | _, [] => by simp [linDs, linEs]
  | st, .mk x e :: ds => by
    simp only [linDs, List.map_cons, domSrc, linEs]
    cases linE vnx st e with
    | none => rfl
    | some st₁ => exact linDs_eq vnx st₁ ds

theorem findVals?_mem {ρ : VarEnv} : ∀ {xs : List IL.Id} {ws : List Value},
    ρ.findVals? xs = some ws → ∀ a ∈ ws, ∃ x ∈ xs, ρ.findVal? x = some a
  | [], ws, h, a, ha => by
    simp only [VarEnv.findVals?, List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp at ha
  | x :: xs, ws, h, a, ha => by
    simp only [VarEnv.findVals?, List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : ρ.findVal? x with
    | none => simp [hx] at h
    | some u =>
      cases hr : xs.mapM ρ.findVal? with
      | none => simp [hx, hr] at h
      | some us =>
        simp only [hx, hr, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨x, List.mem_cons_self .., hx⟩
        · obtain ⟨y, hy, hya⟩ := findVals?_mem (xs := xs) hr a ha
          exact ⟨y, List.mem_cons_of_mem _ hy, hya⟩

/-! ## The statement -/

/-- **Matching passes the erasure at fuel `n`**, on patterns that pass the pattern check. -/
structure LinAt (gd : String → Bool) (env : Env) (n : Nat) : Prop where
  exp : ∀ ρ e v vnx st st', Inv gd ρ st → (vnx = true → nxB v = true) →
    linE vnx st e = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExp n env ρ e v)
      (matchExp n env (eraseScope ρ) e (eraseV v))
  exps : ∀ ρ es vs vnx st st', Inv gd ρ st → (vnx = true → ∀ v ∈ vs, nxB v = true) →
    linEs vnx st es = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExps n env ρ es vs)
      (matchExps n env (eraseScope ρ) es (vs.map eraseV))
  fields : ∀ ρ fs gs vnx st st', Inv gd ρ st → (vnx = true → ∀ g ∈ gs, nxB g.2 = true) →
    linFs vnx st fs = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExpFields n env ρ fs gs)
      (matchExpFields n env (eraseScope ρ) fs (eraseVf gs))
  iter : ∀ ρ e it ds v vnx st st', Inv gd ρ st → (vnx = true → nxB v = true) →
    linE vnx st (.iterE e (.mk it ds)) = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchIterE n env ρ e it ds v)
      (matchIterE n env (eraseScope ρ) e it ds (eraseV v))
  iterList : ∀ ρ e ds ido vs vnx st stb st₁ st', Inv gd ρ st →
    (∀ i, Inv gd (ctrScope ρ ido i) stb) → (vnx = true → ∀ v ∈ vs, nxB v = true) →
    linE vnx stb e = some st₁ →
    linDs ((ds.map domVar).all fun x => st₁.2.contains x) st ds = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchIterList n env ρ e ds ido vs)
      (matchIterList n env (eraseScope ρ) e ds ido (vs.map eraseV))
  rounds : ∀ ρ e xs ido i vs vnx stb st₁, (∀ j, Inv gd (ctrScope ρ ido j) stb) →
    (vnx = true → ∀ v ∈ vs, nxB v = true) → linE vnx stb e = some st₁ →
    ER (List.map (List.map eraseV))
      (fun rows => xs.all (fun x => st₁.2.contains x) = true → ∀ r ∈ rows, ∀ u ∈ r, nxB u = true)
      (matchRounds n env ρ e xs ido i vs)
      (matchRounds n env (eraseScope ρ) e xs ido i (vs.map eraseV))

section
variable {env : Env} {n : Nat}

theorem linAt_zero (gd : String → Bool) (env : Env) : LinAt gd env 0 where
  exp _ _ _ _ _ _ _ _ _ := by simp only [matchExp]; exact ER.error _
  exps _ _ _ _ _ _ _ _ _ := by simp only [matchExps]; exact ER.error _
  fields _ _ _ _ _ _ _ _ _ := by simp only [matchExpFields]; exact ER.error _
  iter _ _ _ _ _ _ _ _ _ _ _ := by simp only [matchIterE]; exact ER.error _
  iterList _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by simp only [matchIterList]; exact ER.error _
  rounds _ _ _ _ _ _ _ _ _ _ _ _ := by simp only [matchRounds]; exact ER.error _

/-- A variable pattern. -/
theorem step_var (ρ : VarEnv) (x : IL.Id) (v : Value) (vnx : Bool) (st st' : LSt)
    (hρ : Inv gd ρ st) (hv : vnx = true → nxB v = true) (hl : linE vnx st (.varE x) = some st') :
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExp (n + 1) env ρ (.varE x) v)
      (matchExp (n + 1) env (eraseScope ρ) (.varE x) (eraseV v)) := by
  simp only [matchExp, find?_eraseScope]
  -- the static branch
  have hst : (st.1.contains x = true ∧
      ((vnx = true ∧ st' = st) ∨ (vnx = false ∧ st.2.contains x = true ∧
        st' = (st.1, st.2.filter (· != x))))) ∨
      (st.1.contains x = false ∧
        st' = (x :: st.1, if vnx then x :: st.2 else st.2.filter (· != x))) := by
    simp only [linE] at hl
    split at hl
    · rename_i h1
      refine .inl ⟨h1, ?_⟩
      split at hl
      · rename_i h2; cases hl; exact .inl ⟨h2, rfl⟩
      · rename_i h2
        split at hl
        · rename_i h3; cases hl; exact .inr ⟨by simpa using h2, h3, rfl⟩
        · cases hl
    · rename_i h1; cases hl; exact .inr ⟨by simpa using h1, rfl⟩
  have hsub₁ : ∀ y, st.1.contains y = true → st'.1.contains y = true := by
    intro y hy
    rcases hst with ⟨_, ⟨_, rfl⟩ | ⟨_, _, rfl⟩⟩ | ⟨_, rfl⟩
    · exact hy
    · exact hy
    · simp only [List.contains_cons, hy, Bool.or_true]
  have hsub₂ : ∀ y, st'.2.contains y = true → st.2.contains y = true ∨ (y = x ∧ vnx = true) := by
    intro y hy
    rcases hst with ⟨_, ⟨_, rfl⟩ | ⟨_, _, rfl⟩⟩ | ⟨_, rfl⟩
    · exact .inl hy
    · exact .inl (contains_of_filter hy)
    · cases hvx : vnx
      · simp only [hvx, Bool.false_eq_true, ite_false] at hy
        exact .inl (contains_of_filter hy)
      · simp only [hvx, ite_true, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hy
        rcases hy with rfl | hy
        · exact .inr ⟨rfl, rfl⟩
        · exact .inl hy
  have hnot : vnx = false → st'.2.contains x = false := by
    intro hvx
    rcases hst with ⟨_, ⟨h1, _⟩ | ⟨_, _, rfl⟩⟩ | ⟨_, rfl⟩
    · rw [hvx] at h1; cases h1
    · exact not_contains_filter
    · simp only [hvx, Bool.false_eq_true, ite_false]; exact not_contains_filter
  cases hf : ρ.findVal? x with
  | some w =>
    simp only [Option.map_some]
    have hx := hρ.dom x w hf
    have hnx : nxB v = true ∨ nxB w = true := by
      rcases hst with ⟨_, ⟨h1, _⟩ | ⟨_, h2, _⟩⟩ | ⟨h1, _⟩
      · exact .inl (hv h1)
      · exact .inr (hρ.nx x w h2 hf)
      · rw [hx] at h1; cases h1
    have hiff : eraseV w = eraseV v ↔ w = v := eraseV_eq_iff_of_nx hnx.symm
    by_cases h : w = v
    · subst h
      simp only [ite_true]
      refine ER.ok ⟨hρ.wild, fun y u hy => hsub₁ y (hρ.dom y u hy), fun y u hy hu => ?_, hρ.defs⟩
      rcases hsub₂ y hy with hy | ⟨rfl, hvx⟩
      · exact hρ.nx y u hy hu
      · rw [hf] at hu; cases hu; exact hv hvx
    · have h' : eraseV w ≠ eraseV v := fun h' => h (hiff.1 h')
      simp only [h, h', ite_false]; exact ER.error _
  | none =>
    simp only [Option.map_none]
    rw [← eraseScope_bindVal]
    refine ER.ok ⟨?_, fun y u hy => ?_, fun y u hy hu => ?_, hρ.defs⟩
    · rw [NxFlow.findVal?_bindVal]
      by_cases hx : x = "_" <;> simp [hx, hρ.wild]
    · rw [NxFlow.findVal?_bindVal] at hy
      split at hy
      · exact hsub₁ y (hρ.dom y u hy)
      · split at hy
        · rename_i _ hxy
          subst hxy
          rcases hst with ⟨_, ⟨_, rfl⟩ | ⟨_, _, rfl⟩⟩ | ⟨_, rfl⟩
          · assumption
          · assumption
          · simp
        · exact hsub₁ y (hρ.dom y u hy)
    · rw [NxFlow.findVal?_bindVal] at hu
      split at hu
      · rcases hsub₂ y hy with hy | ⟨rfl, _⟩
        · exact hρ.nx y u hy hu
        · rename_i hx_; rw [hx_, hρ.wild] at hu; cases hu
      · split at hu
        · rename_i _ hxy
          cases hu
          subst hxy
          cases hvx : vnx
          · rw [hnot hvx] at hy; cases hy
          · exact hv hvx
        · rename_i _ hxy
          rcases hsub₂ y hy with hy | ⟨rfl, _⟩
          · exact hρ.nx y u hy hu
          · exact absurd rfl hxy

/-- Matching a list value, in the form the erased side presents it. -/
theorem matchList_er (ih : LinAt gd env n) {ρ : VarEnv} {e : Exp} {l : List Value} {vnx : Bool}
    {st st' : LSt} (hρ : Inv gd ρ st) (hl : vnx = true → ∀ w ∈ l, nxB w = true)
    (h : linE vnx st e = some st') :
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExp n env ρ e (.list l))
      (matchExp n env (eraseScope ρ) e (.list (l.map eraseV))) := by
  have := ih.exp ρ e (.list l) vnx st st' hρ (fun hv => nxBs_of_mem' (hl hv)) h
  rwa [eraseV_list'] at this

theorem step_exp (ih : LinAt gd env n) : ∀ ρ e v vnx st st', Inv gd ρ st →
    (vnx = true → nxB v = true) → linE vnx st e = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExp (n + 1) env ρ e v)
      (matchExp (n + 1) env (eraseScope ρ) e (eraseV v)) := by
  intro ρ e v vnx st st' hρ hv hl
  cases e with
  | varE x => exact step_var ρ x v vnx st st' hρ hv hl
  | boolE b =>
    simp only [linE, Option.some.injEq] at hl; subst hl
    simp only [matchExp]
    exact ER.assert eraseV_eq_bool.symm fun _ => ER.ok hρ
  | numE m =>
    simp only [linE, Option.some.injEq] at hl; subst hl
    simp only [matchExp]
    exact ER.assert eraseV_eq_num.symm fun _ => ER.ok hρ
  | textE t =>
    simp only [linE, Option.some.injEq] at hl; subst hl
    simp only [matchExp]
    exact ER.assert eraseV_eq_text.symm fun _ => ER.ok hρ
  | tupE es =>
    simp only [linE] at hl
    simp only [matchExp, asTuple?_eraseV]
    cases ht : v.asTuple? with
    | none => exact ER.error _
    | some vs => exact ih.exps ρ es vs vnx st st' hρ (fun h => nx_asTuple (hv h) ht) hl
  | projE e i =>
    simp only [linE] at hl
    simp only [matchExp]
    by_cases hi : i = 0
    · simp only [hi, ite_true] at hl ⊢
      have := ih.exp ρ e (.tuple [v]) vnx st st' hρ
        (fun h => by simp [nxBs, hv h]) hl
      rw [eraseV_tuple'] at this
      exact this
    · simp [hi] at hl
  | caseE op e =>
    simp only [linE] at hl
    simp only [matchExp, asCase?_eraseV]
    cases ht : v.asCase? with
    | none => exact ER.error _
    | some p =>
      obtain ⟨op', w⟩ := p
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ =>
        ih.exp ρ e w vnx st st' hρ (fun h => nx_asCase (hv h) ht) hl
  | uncaseE e op =>
    simp only [linE] at hl
    simp only [matchExp]
    exact ih.exp ρ e (.case op v) vnx st st' hρ (fun h => hv h) hl
  | optE eo =>
    cases eo with
    | none =>
      simp only [linE, Option.some.injEq] at hl; subst hl
      simp only [matchExp]
      exact ER.assert eraseV_eq_optNone.symm fun _ => ER.ok hρ
    | some e =>
      simp only [linE] at hl
      simp only [matchExp, asOpt?_eraseV]
      cases ht : v.asOpt? with
      | none => exact ER.error _
      | some o =>
        simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
        cases o with
        | none => exact ER.error _
        | some w => exact ih.exp ρ e w vnx st st' hρ (fun h => nx_asOpt (hv h) ht) hl
  | strE fs =>
    simp only [linE] at hl
    simp only [matchExp, asStruct?_eraseV]
    cases v with
    | struct gs => exact ih.fields ρ fs gs vnx st st' hρ (fun h => nx_struct (hv h)) hl
    | opt o => cases o <;> exact ER.error _
    | _ => exact ER.error _
  | listE es =>
    simp only [linE] at hl
    simp only [matchExp, asList?_eraseV]
    cases ht : v.asList? with
    | none => exact ER.error _
    | some vs => exact ih.exps ρ es vs vnx st st' hρ (fun h => nx_asList (hv h) ht) hl
  | catE e₁ e₂ =>
    simp only [linE] at hl
    split at hl
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨hl₁, hl₂⟩ := hc
      cases h₁ : linE vnx st e₁ with
      | none => simp [h₁] at hl
      | some st₁ =>
        simp only [h₁] at hl
        simp only [matchExp, asList?_eraseV]
        cases ht : v.asList? with
        | none => exact ER.error _
        | some vs =>
          have hnv : vnx = true → ∀ w ∈ vs, nxB w = true := fun h => nx_asList (hv h) ht
          have hpair : ∀ a b : List Value, (∀ w ∈ a, w ∈ vs) → (∀ w ∈ b, w ∈ vs) →
              ER eraseScope (fun ρ' => Inv gd ρ' st')
                (matchExp n env ρ e₁ (.list a) >>= fun ρ' => matchExp n env ρ' e₂ (.list b))
                (matchExp n env (eraseScope ρ) e₁ (.list (a.map eraseV)) >>= fun ρ' =>
                  matchExp n env ρ' e₂ (.list (b.map eraseV))) := by
            intro a b ha hb
            refine ER.bind (matchList_er ih hρ (fun h w hw => hnv h w (ha w hw)) h₁)
              fun ρ' _ hρ' => ?_
            exact matchList_er ih hρ' (fun h w hw => hnv h w (hb w hw)) hl
          have htk : ∀ k, ∀ w ∈ vs.take k, w ∈ vs := fun k w hw => List.mem_of_mem_take hw
          have hdk : ∀ k, ∀ w ∈ vs.drop k, w ∈ vs := fun k w hw => List.mem_of_mem_drop hw
          simp only [Option.map_some, Res.ofOption_some, bind, Except.bind,
            patLen_erase env ρ n e₁ hl₁, List.length_map, ← List.map_take, ← List.map_drop]
          refine ER.elimUndef (ER.res_id _) (fun k _ _ => ?_) fun hu => ?_
          · exact ER.assert Iff.rfl fun _ => hpair _ _ (htk k) (hdk k)
          · have hl₂' : lenOk e₂ = true := by
              rcases hl₂ with h | h
              · cases e₁ <;> simp [isListE] at h
                cases n <;> simp [patLen] at hu
              · exact h
            rw [patLen_erase env ρ n e₂ hl₂']
            refine ER.elimUndef (ER.res_id _) (fun k _ _ => ?_) fun _ => ?_
            · exact ER.assert Iff.rfl fun _ => hpair _ _ (htk _) (hdk _)
            · exact ER.scan (fun j => hpair _ _ (htk j) (hdk j)) _ _
    · cases hl
  | iterE e it =>
    obtain ⟨it, ds⟩ := it
    simp only [matchExp]
    exact ih.iter ρ e it ds v vnx st st' hρ hv hl
  | subE e t₁ t₂ =>
    simp only [linE] at hl
    simp only [matchExp]
    exact ih.exp ρ e v vnx st st' hρ hv hl
  | _ => simp [linE] at hl

theorem step_exps (ih : LinAt gd env n) : ∀ ρ es vs vnx st st', Inv gd ρ st →
    (vnx = true → ∀ v ∈ vs, nxB v = true) → linEs vnx st es = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExps (n + 1) env ρ es vs)
      (matchExps (n + 1) env (eraseScope ρ) es (vs.map eraseV)) := by
  intro ρ es vs vnx st st' hρ hv hl
  cases es with
  | nil =>
    cases vs with
    | nil =>
      simp only [linEs, Option.some.injEq] at hl; subst hl
      simp only [List.map_nil, matchExps]; exact ER.ok hρ
    | cons _ _ => simp only [List.map_cons, matchExps]; exact ER.error _
  | cons e es =>
    cases vs with
    | nil => simp only [List.map_nil, matchExps]; exact ER.error _
    | cons v vs =>
      simp only [linEs] at hl
      cases h₁ : linE vnx st e with
      | none => simp [h₁] at hl
      | some st₁ =>
        simp only [h₁] at hl
        simp only [List.map_cons, matchExps]
        refine ER.bind (ih.exp ρ e v vnx st st₁ hρ (fun h => hv h v (List.mem_cons_self ..)) h₁)
          fun ρ' _ hρ' => ?_
        exact ih.exps ρ' es vs vnx st₁ st' hρ' (fun h w hw => hv h w (List.mem_cons_of_mem _ hw)) hl

theorem step_fields (ih : LinAt gd env n) : ∀ ρ fs gs vnx st st', Inv gd ρ st →
    (vnx = true → ∀ g ∈ gs, nxB g.2 = true) → linFs vnx st fs = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchExpFields (n + 1) env ρ fs gs)
      (matchExpFields (n + 1) env (eraseScope ρ) fs (eraseVf gs)) := by
  intro ρ fs gs vnx st st' hρ hv hl
  cases fs with
  | nil =>
    cases gs with
    | nil =>
      simp only [linFs, Option.some.injEq] at hl; subst hl
      simp only [eraseVf_nil, matchExpFields]; exact ER.ok hρ
    | cons g _ =>
      obtain ⟨b, w⟩ := g
      simp only [eraseVf_cons, matchExpFields]; exact ER.error _
  | cons f fs =>
    obtain ⟨a, e⟩ := f
    cases gs with
    | nil => simp only [eraseVf_nil, matchExpFields]; exact ER.error _
    | cons g gs =>
      obtain ⟨b, w⟩ := g
      simp only [linFs] at hl
      split at hl
      · cases hl
      · rename_i ha
        cases h₁ : linE vnx st e with
        | none => simp [h₁] at hl
        | some st₁ =>
          simp only [h₁] at hl
          simp only [eraseVf_cons, matchExpFields]
          refine ER.assert Iff.rfl fun hab => ?_
          subst hab
          simp only [ha, ite_false]
          refine ER.bind (ih.exp ρ e w vnx st st₁ hρ (fun h => hv h _ (List.mem_cons_self ..)) h₁)
            fun ρ' _ hρ' => ?_
          exact ih.fields ρ' fs gs vnx st₁ st' hρ'
            (fun h g hg => hv h g (List.mem_cons_of_mem _ hg)) hl

theorem nx_findVals {ρ : VarEnv} {st : LSt} (hρ : Inv gd ρ st) {xs : List IL.Id}
    {ws : List Value} (hf : ρ.findVals? xs = some ws)
    (hx : xs.all (fun x => st.2.contains x) = true) : ∀ a ∈ ws, nxB a = true := by
  intro a ha
  obtain ⟨x, hx', hxa⟩ := findVals?_mem hf a ha
  exact hρ.nx x a (List.all_eq_true.1 hx x hx') hxa

set_option maxHeartbeats 1000000 in
theorem step_iter (ih : LinAt gd env n) : ∀ ρ e it ds v vnx st st', Inv gd ρ st →
    (vnx = true → nxB v = true) → linE vnx st (.iterE e (.mk it ds)) = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchIterE (n + 1) env ρ e it ds v)
      (matchIterE (n + 1) env (eraseScope ρ) e it ds (eraseV v)) := by
  intro ρ e it ds v vnx st st' hρ hv hl
  simp only [linE] at hl
  cases hI : linI st it with
  | none => simp [hI] at hl
  | some p =>
    obtain ⟨st₀, stb⟩ := p
    simp only [hI] at hl
    cases hB : linE vnx stb e with
    | none => simp [hB] at hl
    | some st₁ =>
      simp only [hB] at hl
      have hl' := hl
      rw [linDs_eq] at hl'
      cases it with
      | opt =>
        simp only [linI, Option.some.injEq, Prod.mk.injEq] at hI
        obtain ⟨rfl, rfl⟩ := hI
        simp only [matchIterE, asOpt?_eraseV]
        cases ht : v.asOpt? with
        | none => exact ER.error _
        | some o =>
          simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
          cases o with
          | none =>
            have := ih.exps ρ (ds.map domSrc) (ds.map fun _ => Value.opt none) _ st st' hρ
              (fun _ w hw => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw; rfl) hl'
            simpa [List.map_map, Function.comp_def] using this
          | some w =>
            simp only [Option.map_some]
            refine ER.bind (ih.exp ρ e w vnx st st₁ hρ (fun h => nx_asOpt (hv h) ht) hB)
              fun ρ' _ hρ' => ?_
            rw [findVals?_eraseScope]
            cases hf : ρ'.findVals? (ds.map domVar) with
            | none => exact ER.error _
            | some ws =>
              simp only [Option.map_some, Res.ofOption_some]
              have := ih.exps ρ (ds.map domSrc) (ws.map fun u => Value.opt (some u)) _ st st' hρ
                (fun hvx u hu => by
                  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
                  exact nx_findVals hρ' hf hvx a ha) hl'
              simpa [List.map_map, Function.comp_def] using this
      | list =>
        simp only [linI, Option.some.injEq, Prod.mk.injEq] at hI
        obtain ⟨rfl, rfl⟩ := hI
        simp only [matchIterE, asList?_eraseV]
        cases ht : v.asList? with
        | none => exact ER.error _
        | some vs =>
          simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
          exact ih.iterList ρ e ds none vs vnx st st st₁ st' hρ (fun _ => hρ)
            (fun h => nx_asList (hv h) ht) hB hl
      | list1 =>
        simp only [linI, Option.some.injEq, Prod.mk.injEq] at hI
        obtain ⟨rfl, rfl⟩ := hI
        simp only [matchIterE, asList?_eraseV]
        cases ht : v.asList? with
        | none => exact ER.error _
        | some vs =>
          simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
          exact ER.assert (by simp) fun _ => ih.iterList ρ e ds none vs vnx st st st₁ st' hρ
            (fun _ => hρ) (fun h => nx_asList (hv h) ht) hB hl
      | listN eₙ ido =>
        simp only [linI] at hI
        cases hN : linE true st eₙ with
        | none => simp [hN] at hI
        | some s =>
          simp only [hN, Option.some.injEq, Prod.mk.injEq] at hI
          obtain ⟨rfl, rfl⟩ := hI
          simp only [matchIterE, asList?_eraseV]
          cases ht : v.asList? with
          | none => exact ER.error _
          | some vs =>
            simp only [Option.map_some, Res.ofOption_some, bind, Except.bind, List.length_map]
            refine ER.bind (ih.exp ρ eₙ (.num (.natN vs.length)) true st s hρ (fun _ => rfl) hN)
              fun ρ₀ _ hρ₀ => ?_
            exact ih.iterList ρ₀ e ds ido vs vnx s _ st₁ st' hρ₀ (fun i => hρ₀.ctr ido i)
              (fun h => nx_asList (hv h) ht) hB hl

theorem step_iterList (ih : LinAt gd env n) : ∀ ρ e ds ido vs vnx st stb st₁ st', Inv gd ρ st →
    (∀ i, Inv gd (ctrScope ρ ido i) stb) → (vnx = true → ∀ v ∈ vs, nxB v = true) →
    linE vnx stb e = some st₁ →
    linDs ((ds.map domVar).all fun x => st₁.2.contains x) st ds = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchIterList (n + 1) env ρ e ds ido vs)
      (matchIterList (n + 1) env (eraseScope ρ) e ds ido (vs.map eraseV)) := by
  intro ρ e ds ido vs vnx st stb st₁ st' hρ hctr hv hB hl
  rw [linDs_eq] at hl
  simp only [matchIterList]
  refine ER.bind (ih.rounds ρ e (ds.map domVar) ido 0 vs vnx stb st₁ hctr hv hB)
    fun rows _ hrows => ?_
  rw [iterCols_erase]
  refine ih.exps ρ (ds.map domSrc) _ _ st st' hρ (fun hvx c hc => ?_) hl
  simp only [iterCols, List.mem_map, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  simp only [nxB_list]
  refine nxBs_of_mem' fun u hu => ?_
  simp only [iterCol, List.mem_filterMap] at hu
  obtain ⟨r, hr, hru⟩ := hu
  exact hrows hvx r hr u (List.mem_of_getElem? hru)

theorem step_rounds (ih : LinAt gd env n) : ∀ ρ e xs ido i vs vnx stb st₁,
    (∀ j, Inv gd (ctrScope ρ ido j) stb) → (vnx = true → ∀ v ∈ vs, nxB v = true) →
    linE vnx stb e = some st₁ →
    ER (List.map (List.map eraseV))
      (fun rows => xs.all (fun x => st₁.2.contains x) = true → ∀ r ∈ rows, ∀ u ∈ r, nxB u = true)
      (matchRounds (n + 1) env ρ e xs ido i vs)
      (matchRounds (n + 1) env (eraseScope ρ) e xs ido i (vs.map eraseV)) := by
  intro ρ e xs ido i vs vnx stb st₁ hctr hv hB
  cases vs with
  | nil => simp only [List.map_nil, matchRounds]; exact ER.ok (by simp)
  | cons v vs =>
    simp only [List.map_cons]
    have key : ER (List.map (List.map eraseV))
        (fun rows => xs.all (fun x => st₁.2.contains x) = true → ∀ r ∈ rows, ∀ u ∈ r, nxB u = true)
        (do
          let ρ' ← matchExp n env (ctrScope ρ ido i) e v
          let row ← Res.ofOption (ρ'.findVals? xs)
          let rest ← matchRounds n env ρ e xs ido (i + 1) vs
          .ok (row :: rest))
        (do
          let ρ' ← matchExp n env (eraseScope (ctrScope ρ ido i)) e (eraseV v)
          let row ← Res.ofOption (ρ'.findVals? xs)
          let rest ← matchRounds n env (eraseScope ρ) e xs ido (i + 1) (vs.map eraseV)
          .ok (row :: rest)) := by
      refine ER.bind (ih.exp _ e v vnx stb st₁ (hctr i) (fun h => hv h v (List.mem_cons_self ..)) hB)
        fun ρ' _ hρ' => ?_
      rw [findVals?_eraseScope]
      cases hf : ρ'.findVals? xs with
      | none => exact ER.error _
      | some row =>
        simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
        refine ER.bind (ih.rounds ρ e xs ido (i + 1) vs vnx stb st₁ hctr
          (fun h w hw => hv h w (List.mem_cons_of_mem _ hw)) hB) fun rest _ hrest => ?_
        refine ⟨rfl, fun rows hr => ?_⟩
        simp only [Except.ok.injEq] at hr
        subst hr
        intro hvx r hr u hu
        rcases List.mem_cons.1 hr with rfl | hr
        · exact nx_findVals hρ' hf hvx u hu
        · exact hrest hvx r hr u hu
    rw [eraseScope_ctr] at key
    cases ido with
    | none => simp only [matchRounds]; exact key
    | some y => simp only [matchRounds]; exact key

theorem linAt_succ (ih : LinAt gd env n) : LinAt gd env (n + 1) where
  exp := step_exp ih
  exps := step_exps ih
  fields := step_fields ih
  iter := step_iter ih
  iterList := step_iterList ih
  rounds := step_rounds ih

end

/-- **Matching passes the erasure at every fuel.** -/
theorem linAt (gd : String → Bool) (env : Env) : ∀ n, LinAt gd env n
  | 0 => linAt_zero gd env
  | n + 1 => linAt_succ (linAt gd env n)

/-! ## Argument patterns -/

theorem Inv.congr {ρ ρ' : VarEnv} {st : LSt} (h : Inv gd ρ st) (hv : ρ'.vals = ρ.vals)
    (hd : ρ'.defs = ρ.defs) : Inv gd ρ' st where
  wild := by simpa [VarEnv.findVal?, hv] using h.wild
  dom x w hx := h.dom x w (by simpa [VarEnv.findVal?, hv] using hx)
  nx x w hx hw := h.nx x w hx (by simpa [VarEnv.findVal?, hv] using hw)
  defs p hp := h.defs p (by rw [← hd]; exact hp)

theorem matchTypV_vals {env : Env} {ρ ρ' : VarEnv} {t' t : Typ}
    (h : matchTypV env ρ t' t = .ok ρ') : ρ'.vals = ρ.vals ∧ ρ'.defs = ρ.defs := by
  unfold matchTypV at h
  split at h
  · split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · split at h
      · split at h
        · cases h; exact ⟨rfl, rfl⟩
        · cases h
      · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

theorem matchSymV_vals {env : Env} {ρ ρ' : VarEnv} {g' g : Sym}
    (h : matchSymV env ρ g' g = .ok ρ') : ρ'.vals = ρ.vals ∧ ρ'.defs = ρ.defs := by
  unfold matchSymV at h
  split at h
  · split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · split at h
      · split at h
        · cases h; exact ⟨rfl, rfl⟩
        · cases h
      · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

/-- The pattern check on one argument. -/
def linArg (vnx : Bool) (st : LSt) : Arg → Option LSt
  | .expA e => linE vnx st e
  | _ => some st

theorem matchArg_erase (env : Env) : ∀ (n : Nat) (ρ : VarEnv) (a : Arg) (w : ArgV) (vnx : Bool)
    (st st' : LSt), Inv gd ρ st → (vnx = true → ∀ v, w = .val v → nxB v = true) →
    ArgIn QT gd w → linArg vnx st a = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchArg n env ρ a w)
      (matchArg n env (eraseScope ρ) a (eraseA w))
  | 0, _, _, _, _, _, _, _, _, _, _ => by simp only [matchArg]; exact ER.error _
  | n + 1, ρ, a, w, vnx, st, st', hρ, hv, hw, hl => by
    cases a with
    | expA e =>
      simp only [linArg] at hl
      cases w with
      | val v =>
        simp only [eraseA, matchArg, argSubOk_erase]
        split
        · exact (linAt gd env n).exp ρ e v vnx st st' hρ (fun h => hv h v rfl) hl
        · exact ER.error _
      | _ => simp only [eraseA, matchArg]; exact ER.error _
    | typA t' =>
      simp only [linArg, Option.some.injEq] at hl; subst hl
      cases w with
      | typ t =>
        simp only [eraseA, matchArg, matchTypV_erase]
        exact ⟨rfl, fun ρ' h => hρ.congr (matchTypV_vals h).1 (matchTypV_vals h).2⟩
      | _ => simp only [eraseA, matchArg]; exact ER.error _
    | defA y =>
      simp only [linArg, Option.some.injEq] at hl; subst hl
      cases w with
      | defName x =>
        simp only [eraseA, matchArg]
        rw [← eraseScope_bindDef]
        refine ER.ok ⟨hρ.wild, hρ.dom, hρ.nx, ?_⟩
        exact ((NxErase.sg_of_defs hρ.defs).bindDef hw).2
      | _ => simp only [eraseA, matchArg]; exact ER.error _
    | gramA g' =>
      simp only [linArg, Option.some.injEq] at hl; subst hl
      cases w with
      | gram g =>
        simp only [eraseA, matchArg, matchSymV_erase]
        exact ⟨rfl, fun ρ' h => hρ.congr (matchSymV_vals h).1 (matchSymV_vals h).2⟩
      | _ => simp only [eraseA, matchArg]; exact ER.error _

theorem linA_cons (fl : List Bool) (st : LSt) (a : Arg) (xs : List Arg) :
    linA fl st (a :: xs) =
      match linArg (fl.head?.getD false) st a with
      | some st₁ => linA fl.tail st₁ xs
      | none => none := by
  cases a with
  | expA e => simp only [linA, linArg]; cases linE (fl.head?.getD false) st e <;> rfl
  | _ => simp [linA, linArg]

/-- **Matching argument patterns passes the erasure.** -/
theorem matchArgs_erase (env : Env) : ∀ (n : Nat) (ρ : VarEnv) (args : List Arg) (ws : List ArgV)
    (fl : List Bool) (st st' : LSt), Inv gd ρ st →
    (∀ (i : Nat) v, fl[i]? = some true → ws[i]? = some (.val v) → nxB v = true) →
    (∀ w ∈ ws, ArgIn QT gd w) → linA fl st args = some st' →
    ER eraseScope (fun ρ' => Inv gd ρ' st') (matchArgs n env ρ args ws)
      (matchArgs n env (eraseScope ρ) args (ws.map eraseA))
  | 0, _, _, _, _, _, _, _, _, _, _ => by simp only [matchArgs]; exact ER.error _
  | n + 1, ρ, [], [], fl, st, st', hρ, _, _, hl => by
    simp only [linA, Option.some.injEq] at hl; subst hl
    simp only [List.map_nil, matchArgs]; exact ER.ok hρ
  | n + 1, ρ, [], _ :: _, _, _, _, _, _, _, _ => by
    simp only [List.map_cons, matchArgs]; exact ER.error _
  | n + 1, ρ, _ :: _, [], _, _, _, _, _, _, _ => by
    simp only [List.map_nil, matchArgs]; exact ER.error _
  | n + 1, ρ, a :: args, w :: ws, fl, st, st', hρ, hv, hw, hl => by
    rw [linA_cons] at hl
    cases h₁ : linArg (fl.head?.getD false) st a with
    | none => simp [h₁] at hl
    | some st₁ =>
      simp only [h₁] at hl
      simp only [List.map_cons, matchArgs]
      refine ER.bind (matchArg_erase env n ρ a w _ st st₁ hρ (fun h v hwv => ?_)
        (hw w (List.mem_cons_self ..)) h₁) fun ρ' _ hρ' => ?_
      · subst hwv
        refine hv 0 v ?_ rfl
        cases fl with
        | nil => simp at h
        | cons b fl => simp at h ⊢; exact h
      · refine matchArgs_erase env n ρ' args ws fl.tail st₁ st' hρ' (fun i v hi hwi => ?_)
          (fun u hu => hw u (List.mem_cons_of_mem _ hu)) hl
        refine hv (i + 1) v ?_ hwi
        cases fl with
        | nil => simp at hi
        | cons b fl => simpa using hi

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
