module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Basic

/-!
# Round 7, determination: matching keeps scopes `ExpFree` (unrefined)

`MatchEF n env`: at fuel `n`, matching an `ExpFree` value against a pattern in an `AllEF` scope
returns an `AllEF` scope, for every member of the matching family. Matching binds only parts of the
matched value, numerals (`unE`, `cvtE`, the `ListN` counter) and values read back from scopes it
built itself; everything it evaluates (`matchDefault`, `patLen`, a `ListN` bound) is only
compared, never bound. So no hypothesis on the evaluator or on the syntax is needed. The proof is
`Round7.Script.defsPres_succ` with the invariant changed, kept unrefined like it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (elimUndef_eq_ok)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

theorem ef_iterCol {rows : List (List Value)} (h : ∀ r ∈ rows, ∀ w ∈ r, ExpFree w) (j : Nat) :
    ExpFree (.list (iterCol rows j)) := by
  refine ef_list.2 fun w hw => ?_
  simp only [iterCol, List.mem_filterMap] at hw
  obtain ⟨r, hr, hrw⟩ := hw
  exact h r hr w (List.mem_of_getElem? hrw)

theorem ef_iterCols {rows : List (List Value)} (h : ∀ r ∈ rows, ∀ w ∈ r, ExpFree w) (k : Nat) :
    ∀ c ∈ iterCols rows k, ExpFree c := by
  intro c hc
  simp only [iterCols, List.mem_map] at hc
  obtain ⟨j, _, rfl⟩ := hc
  exact ef_iterCol h j

/-- **Matching keeps scopes `ExpFree`.** -/
structure MatchEF (n : Nat) (env : Env) : Prop where
  matchExp : ∀ ρ e v ρ', AllEF ρ → ExpFree v → matchExp n env ρ e v = .ok ρ' → AllEF ρ'
  matchDefault : ∀ ρ e v ρ', AllEF ρ → matchDefault n env ρ e v = .ok ρ' → AllEF ρ'
  matchExps : ∀ ρ es vs ρ', AllEF ρ → (∀ v ∈ vs, ExpFree v) →
    matchExps n env ρ es vs = .ok ρ' → AllEF ρ'
  matchExpFields : ∀ ρ fs gs ρ', AllEF ρ → (∀ g ∈ gs, ExpFree g.2) →
    matchExpFields n env ρ fs gs = .ok ρ' → AllEF ρ'
  matchIterE : ∀ ρ e it ds v ρ', AllEF ρ → ExpFree v →
    matchIterE n env ρ e it ds v = .ok ρ' → AllEF ρ'
  matchIterList : ∀ ρ e ds ido vs ρ', AllEF ρ → (∀ v ∈ vs, ExpFree v) →
    matchIterList n env ρ e ds ido vs = .ok ρ' → AllEF ρ'
  matchRounds : ∀ ρ e xs ido i vs rows, AllEF ρ → (∀ v ∈ vs, ExpFree v) →
    matchRounds n env ρ e xs ido i vs = .ok rows → ∀ r ∈ rows, ∀ w ∈ r, ExpFree w

theorem matchEF_zero (env : Env) : MatchEF 0 env := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [Sem.matchExp, Sem.matchDefault, Sem.matchExps, Sem.matchExpFields, Sem.matchIterE,
      Sem.matchIterList, Sem.matchRounds]

theorem ef_take {vs : List Value} (h : ExpFree (.list vs)) (k : Nat) :
    ExpFree (.list (vs.take k)) :=
  ef_list.2 fun w hw => ef_list.1 h w (List.mem_of_mem_take hw)

theorem ef_drop {vs : List Value} (h : ExpFree (.list vs)) (k : Nat) :
    ExpFree (.list (vs.drop k)) :=
  ef_list.2 fun w hw => ef_list.1 h w (List.mem_of_mem_drop hw)

theorem matchEF_succ (env : Env) (m : Nat) (ih : MatchEF m env) : MatchEF (m + 1) env := by
  have hm := ih.matchExp
  have hmd := ih.matchDefault
  have hms := ih.matchExps
  have hmf := ih.matchExpFields
  have hmi := ih.matchIterE
  have hmil := ih.matchIterList
  have hmr := ih.matchRounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `matchExp`
  · intro ρ e v ρ' hρ hv h
    cases e
    case varE x =>
      simp only [Sem.matchExp] at h
      split at h
      · split at h
        · cases h; exact hρ
        · cases h
      · cases h; exact allEF_bindVal hρ x hv
    case boolE b => simp only [Sem.matchExp, Res.assert_eq_ok] at h; cases h.2; exact hρ
    case numE b => simp only [Sem.matchExp, Res.assert_eq_ok] at h; cases h.2; exact hρ
    case textE b => simp only [Sem.matchExp, Res.assert_eq_ok] at h; cases h.2; exact hρ
    case unE op t e =>
      cases op <;> cases v <;> simp only [Sem.matchExp, Res.assert_eq_ok, Res.bind_eq_ok] at h <;>
        first
          | exact hmd _ _ _ _ hρ h
          | exact hm _ _ _ _ hρ (ef_num _) h.2
          | (obtain ⟨_, _, _, h⟩ := h; exact hm _ _ _ _ hρ (ef_num _) h)
    case tupE es =>
      simp only [Sem.matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, h⟩ := h
      exact hms _ _ _ _ hρ (ef_of_asTuple hv hvs) h
    case projE e i =>
      simp only [Sem.matchExp] at h
      split at h
      · exact hm _ _ _ _ hρ (ef_tuple.2 fun w hw => by
          rcases List.mem_singleton.1 hw with rfl; exact hv) h
      · exact hmd _ _ _ _ hρ h
    case caseE op e =>
      simp only [Sem.matchExp, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨⟨op', w⟩, hw, _, h⟩ := h
      exact hm _ _ _ _ hρ (ef_of_asCase hv hw) h
    case uncaseE e op => simp only [Sem.matchExp] at h; exact hm _ _ _ _ hρ (ef_case.2 hv) h
    case optE eo =>
      cases eo with
      | none => simp only [Sem.matchExp, Res.assert_eq_ok] at h; cases h.2; exact hρ
      | some e =>
        simp only [Sem.matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨o, ho, w, hw, h⟩ := h
        subst hw
        exact hm _ _ _ _ hρ (ef_of_asOpt hv ho) h
    case strE fs =>
      simp only [Sem.matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨gs, hgs, h⟩ := h
      exact hmf _ _ _ _ hρ (ef_of_asStruct hv hgs) h
    case listE es =>
      simp only [Sem.matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, h⟩ := h
      exact hms _ _ _ _ hρ (ef_of_asList hv hvs) h
    case catE e₁ e₂ =>
      simp only [Sem.matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, h⟩ := h
      have hl : ExpFree (.list vs) := ef_list.2 (ef_of_asList hv hvs)
      have hpair : ∀ ρ₁ a b, ExpFree a → ExpFree b →
          (do let ρ'' ← Sem.matchExp m env ρ e₁ a; Sem.matchExp m env ρ'' e₂ b) = .ok ρ₁ →
          AllEF ρ₁ := by
        intro ρ₁ a b ha hb hab
        simp only [Res.bind_eq_ok] at hab
        obtain ⟨ρ'', h₁, h₂⟩ := hab
        exact hm _ _ _ _ (hm _ _ _ _ hρ ha h₁) hb h₂
      rcases elimUndef_eq_ok h with ⟨k, _, h⟩ | ⟨_, h⟩
      · simp only [Res.assert_eq_ok] at h
        exact hpair _ _ _ (ef_take hl _) (ef_drop hl _) h.2
      · rcases elimUndef_eq_ok h with ⟨k, _, h⟩ | ⟨_, h⟩
        · simp only [Res.assert_eq_ok] at h
          exact hpair _ _ _ (ef_take hl _) (ef_drop hl _) h.2
        · obtain ⟨j, _, _, h⟩ := Res.scan_eq_ok _ _ h
          exact hpair _ _ _ (ef_take hl _) (ef_drop hl _) h
    case iterE e it =>
      cases it with
      | mk i ds => simp only [Sem.matchExp] at h; exact hmi _ _ _ _ _ _ hρ hv h
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [Sem.matchExp, Res.bind_eq_ok] at h <;>
        first
          | exact hmd _ _ _ _ hρ h
          | (obtain ⟨_, _, h⟩ := h; exact hm _ _ _ _ hρ (ef_num _) h)
    case subE e t₁ t₂ => simp only [Sem.matchExp] at h; exact hm _ _ _ _ hρ hv h
    all_goals (simp only [Sem.matchExp] at h; exact hmd _ _ _ _ hρ h)
  -- `matchDefault`
  · intro ρ e v ρ' hρ h
    simp only [Sem.matchDefault, Res.bind_eq_ok, Res.assert_eq_ok] at h
    obtain ⟨_, _, _, h⟩ := h
    cases h; exact hρ
  -- `matchExps`
  · intro ρ es vs ρ' hρ hvs h
    cases es with
    | nil => cases vs <;> simp only [Sem.matchExps] at h <;> cases h; exact hρ
    | cons e es =>
      cases vs with
      | nil => simp only [Sem.matchExps] at h; cases h
      | cons v vs =>
        simp only [Sem.matchExps, Res.bind_eq_ok] at h
        obtain ⟨ρ₁, h₁, h₂⟩ := h
        exact hms _ _ _ _ (hm _ _ _ _ hρ (hvs v List.mem_cons_self) h₁)
          (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) h₂
  -- `matchExpFields`
  · intro ρ fs gs ρ' hρ hgs h
    cases fs with
    | nil => cases gs <;> simp only [Sem.matchExpFields] at h <;> cases h; exact hρ
    | cons f fs =>
      cases f with
      | mk a e =>
        cases gs with
        | nil => simp only [Sem.matchExpFields] at h; cases h
        | cons g gs =>
          simp only [Sem.matchExpFields, Res.assert_eq_ok, Res.bind_eq_ok] at h
          obtain ⟨_, ρ₁, h₁, h₂⟩ := h
          exact hmf _ _ _ _ (hm _ _ _ _ hρ (hgs g List.mem_cons_self) h₁)
            (fun w hw => hgs w (List.mem_cons_of_mem _ hw)) h₂
  -- `matchIterE`
  · intro ρ e it ds v ρ' hρ hv h
    cases it with
    | opt =>
      simp only [Sem.matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨o, ho, h⟩ := h
      cases o with
      | none =>
        refine hms _ _ _ _ hρ (fun w hw => ?_) h
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw
        exact ef_optNone
      | some w =>
        simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨ρ₁, h₁, ws, hws, h⟩ := h
        have hρ₁ := hm _ _ _ _ hρ (ef_of_asOpt hv ho) h₁
        refine hms _ _ _ _ hρ (fun u hu => ?_) h
        obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hu
        exact ef_optSome.2 (ef_findVals hρ₁ hws u' hu')
    | list =>
      simp only [Sem.matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, h⟩ := h
      exact hmil _ _ _ _ _ _ hρ (ef_of_asList hv hvs) h
    | list1 =>
      simp only [Sem.matchIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, _, h⟩ := h
      exact hmil _ _ _ _ _ _ hρ (ef_of_asList hv hvs) h
    | listN eₙ x =>
      simp only [Sem.matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨vs, hvs, ρ₀, h₀, h⟩ := h
      exact hmil _ _ _ _ _ _ (hm _ _ _ _ hρ (ef_num _) h₀) (ef_of_asList hv hvs) h
  -- `matchIterList`
  · intro ρ e ds ido vs ρ' hρ hvs h
    simp only [Sem.matchIterList, Res.bind_eq_ok] at h
    obtain ⟨rows, hrows, h⟩ := h
    exact hms _ _ _ _ hρ (ef_iterCols (hmr _ _ _ _ _ _ _ hρ hvs hrows) _) h
  -- `matchRounds`
  · intro ρ e xs ido i vs rows hρ hvs h
    cases vs with
    | nil => simp only [Sem.matchRounds] at h; cases h; simp
    | cons v vs =>
      rw [Sem.matchRounds.eq_def] at h
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨ρ₁, h₁, row, hrow, rest, hrest, h⟩ := h
      cases h
      have hρ₁ : AllEF ρ₁ := by
        cases ido with
        | some y => exact hm _ _ _ _ (allEF_bindVal hρ y (ef_num _)) (hvs v List.mem_cons_self) h₁
        | none => exact hm _ _ _ _ hρ (hvs v List.mem_cons_self) h₁
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ef_findVals hρ₁ hrow
      · exact hmr _ _ _ _ _ _ _ hρ (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hrest r hr

/-- **`MatchEF` at every fuel.** -/
theorem matchEF (env : Env) : ∀ n, MatchEF n env
  | 0 => matchEF_zero env
  | n + 1 => matchEF_succ env n (matchEF env n)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
