module

public import Silmaril.Games.Composition.Thms

/-!
# Auxiliary facts about the game core

* the projections `lower`/`upper` on `cons` (copies of private simp lemmas of
  `Silmaril.Proofs.Games.Composition.Unit`, which cannot be imported here);
* `zip_empty_iff`: interacting with a component over the empty signature
  `Sig.empty` hides exactly the lower events (`Zip` against an empty lower
  interface is determined by the upper play);
* `mem_comp_empty_iff`: the plays of `τ ≫ σ` for `τ : Strategy Sig.empty E`
  are the upper projections of the plays of `σ` whose lower projection is a
  play of `τ`;
* `zip_noEv_iff`, `mem_comp_noEv_iff`: the same for any lower signature
  without events (e.g. `ifaceSig []`).
-/

public section

namespace Silmaril.Proofs.Wasm.Game.GamesAux

open Silmaril.Games

universe u

variable {E F : Sig.{u}}

@[simp] theorem upper_nil : upper ([] : List (Move E F)) = [] := rfl
@[simp] theorem upper_cons_inl (a : Ev E) (s : List (Move E F)) :
    upper (.inl a :: s) = upper s := rfl
@[simp] theorem upper_cons_inr (b : Ev F) (s : List (Move E F)) :
    upper (.inr b :: s) = b :: upper s := rfl
@[simp] theorem lower_nil : lower ([] : List (Move E F)) = [] := rfl
@[simp] theorem lower_cons_inl (a : Ev E) (s : List (Move E F)) :
    lower (.inl a :: s) = a :: lower s := rfl
@[simp] theorem lower_cons_inr (b : Ev F) (s : List (Move E F)) :
    lower (.inr b :: s) = lower s := rfl

@[simp] theorem upper_append (s t : List (Move E F)) : upper (s ++ t) = upper s ++ upper t := by
  simp [upper, List.filterMap_append]

@[simp] theorem lower_append (s t : List (Move E F)) : lower (s ++ t) = lower s ++ lower t := by
  simp [lower, List.filterMap_append]

@[simp] theorem lower_map_inl (l : List (Ev E)) : lower (l.map .inl : List (Move E F)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem upper_map_inl (l : List (Ev E)) : upper (l.map .inl : List (Move E F)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem lower_map_inr (l : List (Ev F)) : lower (l.map .inr : List (Move E F)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem upper_map_inr (l : List (Ev F)) : upper (l.map .inr : List (Move E F)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The empty signature has no events. -/
theorem Ev.empty_elim (a : Ev Sig.empty.{u}) : False := by
  cases a with
  | ask m => exact m.elim
  | ans m _ => exact m.elim

/-- Interaction with a component over the empty lower signature: the lower events of `t`
are exactly the moves of `s`, and the visible play is the upper part of `t`. -/
theorem zip_empty_iff {s : List (Move Sig.empty E)} {t : List (Move E F)}
    {p : List (Move Sig.empty F)} :
    Zip s t p ↔ s = (lower t).map .inr ∧ p = (upper t).map .inr := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | left a _ _ => exact (Ev.empty_elim a).elim
    | right c _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
    | sync b _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    induction t with
    | nil => exact .nil
    | cons m t ih =>
      rcases m with b | c
      · exact .sync b ih
      · exact .right c ih

/-- The plays of a composite whose lower component has the empty lower signature. -/
theorem mem_comp_empty_iff {τ : Strategy Sig.empty E} {σ : Strategy E F}
    {p : List (Move Sig.empty F)} :
    p ∈ τ.comp σ ↔ ∃ t ∈ σ, (lower t).map .inr ∈ τ ∧ p = (upper t).map .inr := by
  rw [Strategy.mem_comp]
  constructor
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨rfl, rfl⟩ := zip_empty_iff.1 hz
    exact ⟨t, ht, hs, rfl⟩
  · rintro ⟨t, ht, hs, rfl⟩
    exact ⟨_, hs, t, ht, zip_empty_iff.2 ⟨rfl, rfl⟩⟩

/-- `zip_empty_iff` for any lower signature without events. -/
theorem zip_noEv_iff {E₀ : Sig.{u}} (h₀ : Ev E₀ → False) {s : List (Move E₀ E)}
    {t : List (Move E F)} {p : List (Move E₀ F)} :
    Zip s t p ↔ s = (lower t).map .inr ∧ p = (upper t).map .inr := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | left a _ _ => exact (h₀ a).elim
    | right c _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
    | sync b _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    induction t with
    | nil => exact .nil
    | cons m t ih =>
      rcases m with b | c
      · exact .sync b ih
      · exact .right c ih

/-- `mem_comp_empty_iff` for any lower signature without events. -/
theorem mem_comp_noEv_iff {E₀ : Sig.{u}} (h₀ : Ev E₀ → False) {τ : Strategy E₀ E}
    {σ : Strategy E F} {p : List (Move E₀ F)} :
    p ∈ τ.comp σ ↔ ∃ t ∈ σ, (lower t).map .inr ∈ τ ∧ p = (upper t).map .inr := by
  rw [Strategy.mem_comp]
  constructor
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨rfl, rfl⟩ := (zip_noEv_iff h₀).1 hz
    exact ⟨t, ht, hs, rfl⟩
  · rintro ⟨t, ht, hs, rfl⟩
    exact ⟨_, hs, t, ht, (zip_noEv_iff h₀).2 ⟨rfl, rfl⟩⟩

/-- Prefixes of a mapped list are mapped prefixes. -/
theorem prefix_map_iff {α β : Type*} {f : α → β} {p : List β}
    {l : List α} : p <+: l.map f ↔ ∃ l', l' <+: l ∧ p = l'.map f := by
  constructor
  · rintro ⟨r, hr⟩
    induction l generalizing p with
    | nil =>
      simp only [List.map_nil, List.append_eq_nil_iff] at hr
      exact ⟨[], List.prefix_refl _, by simp [hr.1]⟩
    | cons a l ih =>
      cases p with
      | nil => exact ⟨[], List.nil_prefix, rfl⟩
      | cons b p =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hr
        obtain ⟨rfl, hr⟩ := hr
        obtain ⟨l', hl', rfl⟩ := ih hr
        exact ⟨a :: l', List.cons_prefix_cons.2 ⟨rfl, hl'⟩, rfl⟩
  · rintro ⟨l', hl', rfl⟩
    exact hl'.map f

end Silmaril.Proofs.Wasm.Game.GamesAux
