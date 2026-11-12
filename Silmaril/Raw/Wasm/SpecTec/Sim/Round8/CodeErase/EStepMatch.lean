module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.EStepExp2

/-!
# Round 8 (copy of round 7 for `CODE` fields), the whole-evaluator erasure: matching, one step (unrefined)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

`matchExp`, `matchDefault`, `matchExps`, `matchExpFields`, `matchIterE`, `matchIterList`,
`matchRounds`, `matchArg` and `matchArgs` at fuel `n + 1`, from `EraseAt … n`. Matching an erased
value at the erased scope returns the erased scope of the original match. Equality patterns
(`varE` already bound, `matchDefault`) read alike by `QInj` (`Round8.CodeErase.Swap.eraseC_inj`); record
patterns never name `CODE`, so an `CODE` field of the value fails the match on both sides.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope ScopeIn find?_eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env} {n : Nat}

/-! ## Arguments: subtypes, types and grammars -/

theorem subCaseOk_erase (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    subCaseOk env (eraseScope ρ) t (eraseC v) = subCaseOk env ρ t v := by
  cases v with
  | case op w =>
    simp only [eraseC_case]
    unfold subCaseOk
    split <;> simp_all
  | opt o =>
    cases o <;> simp only [eraseC_opt_none, eraseC_opt_some] <;> unfold subCaseOk <;> split <;>
      simp_all
  | _ =>
    simp only [eraseC_bool, eraseC_num, eraseC_text, eraseC_tuple, eraseC_struct, eraseC_list]
    unfold subCaseOk
    split <;> simp_all

theorem argSubOk_erase (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) :
    argSubOk env (eraseScope ρ) e (eraseC v) = argSubOk env ρ e v := by
  cases e <;> simp only [argSubOk, subCaseOk_erase]

theorem matchTypV_erase (env : Env) (ρ : VarEnv) (t' t : Typ) :
    matchTypV env (eraseScope ρ) t' t = eraseScope <$> matchTypV env ρ t' t := by
  unfold matchTypV
  split
  · simp only [eraseScope_findTyp]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
  · split <;> rfl

theorem matchSymV_erase (env : Env) (ρ : VarEnv) (g' g : Sym) :
    matchSymV env (eraseScope ρ) g' g = eraseScope <$> matchSymV env ρ g' g := by
  unfold matchSymV
  split
  · simp only [eraseScope_findGram]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
  · split <;> rfl

theorem matchTypV_sg {ρ ρ' : VarEnv} (hρ : SG Q gd ρ) {t' t : Typ}
    (h : matchTypV env ρ t' t = .ok ρ') : SG Q gd ρ' := by
  unfold matchTypV at h
  split at h
  · split at h
    · split at h
      · cases h; exact hρ
      · cases h
    · split at h
      · split at h
        · cases h; exact hρ
        · cases h
      · cases h; exact hρ.bindTyp _ _
  · split at h
    · cases h; exact hρ
    · cases h

theorem matchSymV_sg {ρ ρ' : VarEnv} (hρ : SG Q gd ρ) {g' g : Sym}
    (h : matchSymV env ρ g' g = .ok ρ') : SG Q gd ρ' := by
  unfold matchSymV at h
  split at h
  · split at h
    · split at h
      · cases h; exact hρ
      · cases h
    · split at h
      · split at h
        · cases h; exact hρ
        · cases h
      · cases h; exact hρ.bindGram _ _
  · split at h
    · cases h; exact hρ
    · cases h

/-! ## `matchDefault`, lists and records -/

theorem step_matchDefault (H : Hyps Q gr gd env) (ih : EraseAt Q gr gd env n) :
    ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
      ER eraseScope (SG Q gd) (matchDefault (n + 1) env ρ e v)
        (matchDefault (n + 1) env (eraseScope ρ) e (eraseC v)) := by
  intro ρ e v hρ hx hv
  simp only [matchDefault]
  refine ER.bind (ih.exp ρ e hρ hx) fun w _ hw => ?_
  exact ER.assert ⟨fun h => h ▸ rfl, fun h => eraseC_inj H.inj hw hv h⟩ fun _ => ER.ok hρ

theorem step_matchExps (ih : EraseAt Q gr gd env n) :
    ∀ ρ es vs, SG Q gd ρ → xExps gr gd es = true → (∀ v ∈ vs, AllIn Q v) →
      ER eraseScope (SG Q gd) (matchExps (n + 1) env ρ es vs)
        (matchExps (n + 1) env (eraseScope ρ) es (vs.map eraseC)) := by
  intro ρ es vs hρ hx hv
  cases es with
  | nil =>
    cases vs with
    | nil => simp only [List.map_nil, matchExps]; exact ER.ok hρ
    | cons _ _ => simp only [List.map_cons, matchExps]; exact ER.error _
  | cons e es =>
    cases vs with
    | nil => simp only [List.map_nil, matchExps]; exact ER.error _
    | cons v vs =>
      simp only [xExps, Bool.and_eq_true] at hx
      simp only [List.map_cons, matchExps]
      refine ER.bind (ih.matchExp ρ e v hρ hx.1 (hv v (List.mem_cons_self ..))) fun ρ' _ hρ' => ?_
      exact ih.matchExps ρ' es vs hρ' hx.2 fun w hw => hv w (List.mem_cons_of_mem _ hw)

theorem step_matchExpFields (ih : EraseAt Q gr gd env n) :
    ∀ ρ fs gs, SG Q gd ρ → xFields gr gd fs = true → (∀ p ∈ gs, AllIn Q p.2) →
      ER eraseScope (SG Q gd) (matchExpFields (n + 1) env ρ fs gs)
        (matchExpFields (n + 1) env (eraseScope ρ) fs (eraseCf gs)) := by
  intro ρ fs gs hρ hx hg
  cases fs with
  | nil =>
    cases gs with
    | nil => simp only [eraseCf_nil, matchExpFields]; exact ER.ok hρ
    | cons g _ =>
      obtain ⟨b, w⟩ := g
      simp only [eraseCf_cons, matchExpFields]; exact ER.error _
  | cons f fs =>
    obtain ⟨a, e⟩ := f
    cases gs with
    | nil => simp only [eraseCf_nil, matchExpFields]; exact ER.error _
    | cons g gs =>
      obtain ⟨b, w⟩ := g
      simp only [xFields, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
      simp only [eraseCf_cons, matchExpFields]
      refine ER.assert Iff.rfl fun hab => ?_
      subst hab
      simp only [hx.1.1, ite_false]
      refine ER.bind (ih.matchExp ρ e w hρ hx.1.2 (hg _ (List.mem_cons_self ..))) fun ρ' _ hρ' => ?_
      exact ih.matchExpFields ρ' fs gs hρ' hx.2 fun p hp => hg p (List.mem_cons_of_mem _ hp)

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
