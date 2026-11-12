module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval

/-!
# Round 7: matching and premises do not touch type variables (unrefined)

`TypsPres n env`: at fuel `n`, every member of the evaluator that returns a scope (`matchExp`
and its helpers, `premHolds` and its helpers) returns one with the same type variables as it
was given. It is `Round7.Script.DefsPres` (`Raw/…/Round7/Script/Pres.lean`) with `VarEnv.typs` in
place of `VarEnv.defs`; the proof is the same case analysis, copied. It carries the invariant
"every type variable is bound to a type over `tyA`" (`Round7.TypAgree.TypsOk`) across the scopes
that matching returns in `Sem.hasTypInsts`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

theorem elimUndef_eq_ok' {α β : Type} {r : Res α} {f : α → Res β} {g : Unit → Res β} {b : β}
    (h : Res.elimUndef r f g = .ok b) :
    (∃ a, r = .ok a ∧ f a = .ok b) ∨ (r = .error .undef ∧ g () = .ok b) := by
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, h⟩
  | error e => cases e with
    | undef => exact Or.inr ⟨rfl, h⟩
    | outOfFuel => simp [Res.elimUndef] at h

theorem foldlM_typs {β : Type} {f : VarEnv → β → Res VarEnv} {xs : List β}
    (hf : ∀ ρ a ρ', a ∈ xs → f ρ a = .ok ρ' → ρ'.typs = ρ.typs) :
    ∀ ρ ρ', xs.foldlM f ρ = (.ok ρ' : Res VarEnv) → ρ'.typs = ρ.typs := by
  induction xs with
  | nil => intro ρ ρ' h; simp only [List.foldlM_nil] at h; cases h; rfl
  | cons a xs ih =>
    intro ρ ρ' h
    simp only [List.foldlM_cons, Res.bind_eq_ok] at h
    obtain ⟨ρ₁, h₁, h₂⟩ := h
    rw [ih (fun ρ a ρ' ha => hf ρ a ρ' (List.mem_cons_of_mem _ ha)) ρ₁ ρ' h₂,
      hf ρ a ρ₁ List.mem_cons_self h₁]

/-- **Scopes returned by matching and premises keep their type variables.** -/
structure TypsPres (n : Nat) (env : Env) : Prop where
  matchExp : ∀ ρ e v ρ', matchExp n env ρ e v = .ok ρ' → ρ'.typs = ρ.typs
  matchDefault : ∀ ρ e v ρ', matchDefault n env ρ e v = .ok ρ' → ρ'.typs = ρ.typs
  matchExps : ∀ ρ es vs ρ', matchExps n env ρ es vs = .ok ρ' → ρ'.typs = ρ.typs
  matchExpFields : ∀ ρ fs gs ρ', matchExpFields n env ρ fs gs = .ok ρ' → ρ'.typs = ρ.typs
  matchIterE : ∀ ρ e it ds v ρ', matchIterE n env ρ e it ds v = .ok ρ' → ρ'.typs = ρ.typs
  matchIterList : ∀ ρ e ds ido vs ρ', matchIterList n env ρ e ds ido vs = .ok ρ' →
    ρ'.typs = ρ.typs
  premHolds : ∀ ρ pr ρ', premHolds n env ρ pr = .ok ρ' → ρ'.typs = ρ.typs
  premsHold : ∀ ρ prs ρ', premsHold n env ρ prs = .ok ρ' → ρ'.typs = ρ.typs
  premIter : ∀ ρ pr it ds ρ', premIter n env ρ pr it ds = .ok ρ' → ρ'.typs = ρ.typs
  premRounds : ∀ ρ pr xvs ido k ρ', premRounds n env ρ pr xvs ido k = .ok ρ' → ρ'.typs = ρ.typs

theorem typsPres_zero (env : Env) : TypsPres 0 env := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [matchExp, matchDefault, matchExps, matchExpFields, matchIterE, matchIterList,
      premHolds, premsHold, premIter, premRounds]

theorem typsPres_succ (env : Env) (m : Nat) (ih : TypsPres m env) : TypsPres (m + 1) env := by
  have hm := ih.matchExp
  have hmd := ih.matchDefault
  have hms := ih.matchExps
  have hmf := ih.matchExpFields
  have hmi := ih.matchIterE
  have hmil := ih.matchIterList
  have hph := ih.premHolds
  have hphs := ih.premsHold
  have hpi := ih.premIter
  have hpr := ih.premRounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `matchExp`
  · intro ρ e v ρ' h
    cases e
    case varE x =>
      simp only [matchExp] at h
      split at h
      · split at h
        · cases h; rfl
        · cases h
      · cases h; rfl
    case boolE b => simp only [matchExp, Res.assert_eq_ok] at h; cases h.2; rfl
    case numE b => simp only [matchExp, Res.assert_eq_ok] at h; cases h.2; rfl
    case textE b => simp only [matchExp, Res.assert_eq_ok] at h; cases h.2; rfl
    case unE op t e =>
      cases op <;> cases v <;> simp only [matchExp, Res.assert_eq_ok, Res.bind_eq_ok] at h <;>
        first
          | exact hmd _ _ _ _ h
          | exact hm _ _ _ _ h.2
          | (obtain ⟨_, _, _, h⟩ := h; exact hm _ _ _ _ h)
    case tupE es =>
      simp only [matchExp, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact hms _ _ _ _ h
    case projE e i =>
      simp only [matchExp] at h
      split at h
      · exact hm _ _ _ _ h
      · exact hmd _ _ _ _ h
    case caseE op e =>
      simp only [matchExp, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, h⟩ := h
      exact hm _ _ _ _ h
    case uncaseE e op => simp only [matchExp] at h; exact hm _ _ _ _ h
    case optE eo =>
      cases eo with
      | none => simp only [matchExp, Res.assert_eq_ok] at h; cases h.2; rfl
      | some e =>
        simp only [matchExp, Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        exact hm _ _ _ _ h
    case strE fs =>
      simp only [matchExp, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact hmf _ _ _ _ h
    case listE es =>
      simp only [matchExp, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact hms _ _ _ _ h
    case catE e₁ e₂ =>
      simp only [matchExp, Res.bind_eq_ok] at h
      obtain ⟨vs, _, h⟩ := h
      have hpair : ∀ ρ₁ a b, (do let ρ'' ← Sem.matchExp m env ρ e₁ a; Sem.matchExp m env ρ'' e₂ b)
          = .ok ρ₁ → ρ₁.typs = ρ.typs := by
        intro ρ₁ a b hab
        simp only [Res.bind_eq_ok] at hab
        obtain ⟨ρ'', h₁, h₂⟩ := hab
        rw [hm _ _ _ _ h₂, hm _ _ _ _ h₁]
      rcases elimUndef_eq_ok' h with ⟨k, _, h⟩ | ⟨_, h⟩
      · simp only [Res.assert_eq_ok] at h
        exact hpair _ _ _ h.2
      · rcases elimUndef_eq_ok' h with ⟨k, _, h⟩ | ⟨_, h⟩
        · simp only [Res.assert_eq_ok] at h
          exact hpair _ _ _ h.2
        · obtain ⟨j, _, _, h⟩ := Res.scan_eq_ok _ _ h
          exact hpair _ _ _ h
    case iterE e it =>
      cases it with
      | mk i ds => simp only [matchExp] at h; exact hmi _ _ _ _ _ _ h
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [matchExp, Res.bind_eq_ok] at h <;>
        first
          | exact hmd _ _ _ _ h
          | (obtain ⟨_, _, h⟩ := h; exact hm _ _ _ _ h)
    case subE e t₁ t₂ => simp only [matchExp] at h; exact hm _ _ _ _ h
    all_goals (simp only [matchExp] at h; exact hmd _ _ _ _ h)
  -- `matchDefault`
  · intro ρ e v ρ' h
    simp only [matchDefault, Res.bind_eq_ok, Res.assert_eq_ok] at h
    obtain ⟨_, _, _, h⟩ := h
    cases h; rfl
  -- `matchExps`
  · intro ρ es vs ρ' h
    cases es with
    | nil => cases vs <;> simp only [matchExps] at h <;> cases h; rfl
    | cons e es =>
      cases vs with
      | nil => simp only [matchExps] at h; cases h
      | cons v vs =>
        simp only [matchExps, Res.bind_eq_ok] at h
        obtain ⟨ρ₁, h₁, h₂⟩ := h
        rw [hms _ _ _ _ h₂, hm _ _ _ _ h₁]
  -- `matchExpFields`
  · intro ρ fs gs ρ' h
    cases fs with
    | nil => cases gs <;> simp only [matchExpFields] at h <;> cases h; rfl
    | cons f fs =>
      cases f with
      | mk a e =>
        cases gs with
        | nil => simp only [matchExpFields] at h; cases h
        | cons g gs =>
          simp only [matchExpFields, Res.assert_eq_ok, Res.bind_eq_ok] at h
          obtain ⟨_, ρ₁, h₁, h₂⟩ := h
          rw [hmf _ _ _ _ h₂, hm _ _ _ _ h₁]
  -- `matchIterE`
  · intro ρ e it ds v ρ' h
    cases it with
    | opt =>
      simp only [matchIterE, Res.bind_eq_ok] at h
      obtain ⟨o, _, h⟩ := h
      cases o with
      | none => exact hms _ _ _ _ h
      | some w =>
        simp only [Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        exact hms _ _ _ _ h
    | list =>
      simp only [matchIterE, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact hmil _ _ _ _ _ _ h
    | list1 =>
      simp only [matchIterE, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, h⟩ := h
      exact hmil _ _ _ _ _ _ h
    | listN eₙ x =>
      simp only [matchIterE, Res.bind_eq_ok] at h
      obtain ⟨_, _, ρ₀, h₀, h⟩ := h
      rw [hmil _ _ _ _ _ _ h, hm _ _ _ _ h₀]
  -- `matchIterList`
  · intro ρ e ds ido vs ρ' h
    simp only [matchIterList, Res.bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    exact hms _ _ _ _ h
  -- `premHolds`
  · intro ρ pr ρ' h
    cases pr with
    | ifPr e =>
      simp only [premHolds, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, h⟩ := h
      cases h; rfl
    | elsePr => simp only [premHolds] at h; cases h; rfl
    | letPr e₁ e₂ =>
      simp only [premHolds, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact hm _ _ _ _ h
    | rulePr x args op e =>
      simp only [premHolds, Res.bind_eq_ok] at h
      obtain ⟨_, _, _, _, h⟩ := h
      split at h
      · cases h; rfl
      · cases h
    | iterPr pr it =>
      cases it with
      | mk i ds => simp only [premHolds] at h; exact hpi _ _ _ _ _ h
  -- `premsHold`
  · intro ρ prs ρ' h
    simp only [premsHold] at h
    exact foldlM_typs (fun ρ a ρ' _ h => hph ρ a ρ' h) ρ ρ' h
  -- `premIter`
  · intro ρ pr it ds ρ' h
    cases it with
    | opt =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      split at h
      · cases h; rfl
      · split at h
        · simp only [Res.bind_eq_ok] at h
          obtain ⟨_, _, h⟩ := h
          cases h; rfl
        · cases h
    | list =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ h
    | list1 =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ h
    | listN eₙ x =>
      simp only [premIter, Res.bind_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ h
  -- `premRounds`
  · intro ρ pr xvs ido k ρ' h
    simp only [premRounds, Res.bind_eq_ok, Res.assert_eq_ok] at h
    obtain ⟨_, _, _, _, _, h⟩ := h
    cases h; rfl

/-- **`TypsPres` at every fuel.** -/
theorem typsPres (env : Env) : ∀ n, TypsPres n env
  | 0 => typsPres_zero env
  | n + 1 => typsPres_succ env n (typsPres env n)

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
